{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Haskell driver for the YCHR type checker.
--
-- Walks the desugared AST and feeds constraints into a CHR session
-- running the pre-compiled type-checker program. The type checker
-- catches type inconsistencies statically, while remaining optional:
-- programs without type annotations are accepted without errors.
--
-- == @tc_unify@ argument order invariant
--
-- The CHR-side @tc_unify(T1, T2, Ctx)@ rules are asymmetric in how
-- they handle @any@: when @any@ appears on the left, it succeeds
-- without binding the right side (which may be a type parameter that
-- should stay open). When @any@ appears on the right and the left is
-- a var, the var is bound to @any@. The discipline is therefore:
-- source-variable type on the LEFT, declared type on the RIGHT.
--
-- The driver enforces this indirectly: every source-vs-declared
-- meeting is routed through @check_constraint_use@,
-- @check_function_use@, or @check_constructor_use@, and the CHR rules
-- for those constraints produce @tc_unify@ calls in the correct
-- order. Direct @check_unify@ calls from the driver only happen
-- between two source-variable types (body @X = Y@, body @X is e@,
-- guard @X = Y@), where the ordering is irrelevant.
module YCHR.TypeCheck
  ( TypeCheckError (..),
    typeCheckProgram,
    typeCheckGoals,
  )
where

import Control.Monad (replicateM, when)
import Data.List qualified as List
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as T
import Effectful
import Effectful.Reader.Static (Reader, ask, runReader)
import Effectful.State.Static.Local (State, evalState, get, put)
import YCHR.Compile.Names (vmName)
import YCHR.Compile.Pipeline (CompiledProgram (..))
import YCHR.Desugared qualified as D
import YCHR.Diagnostic (Diagnostic (..))
import YCHR.PExpr (PExpr (Atom), mkOpTable)
import YCHR.Parsed (AnnP (..), SourceLoc (..))
import YCHR.Runtime.Interpreter (baseHostCallRegistry)
import YCHR.Runtime.Registry (fromValueList, valueList)
import YCHR.Runtime.Session (CHREffects, tellConstraint, withCHR)
import YCHR.Runtime.Types (Value (..))
import YCHR.Runtime.Var (Unify, deref, newVar)
import YCHR.TypeCheck.Compiled (typeCheckerProgram)
import YCHR.TypeCheck.Error (TypeCheckError (..))
import YCHR.TypeCheck.TH (TypeCheckerProgram (..))
import YCHR.Types
  ( DataConstructor (..),
    Name (..),
    Term (..),
    TypeDefinition (..),
    TypeExpr (..),
    flattenName,
  )
import YCHR.Types qualified as Types
import YCHR.VM qualified as VM

-- | Flatten a 'Name' to the same single-atom form used by the runtime
-- (see 'YCHR.Compile.Names.vmName'). Required so CHR-side constraints
-- emitted from this Haskell driver match what compiled CHR rules
-- produce after the renamer canonicalizes data-constructor names.
runtimeName :: Name -> Text
runtimeName name = let VM.Name t = vmName name in t

-- | Parse a 'flattenName'-encoded text back into a 'Name'. The renamer
-- emits qualified names as @\"module:local\"@ and unqualified names as
-- @\"local\"@; this is the inverse of 'flattenName'. Used for AST nodes
-- that store the flattened text (e.g. function-reference @AtomTerm@s)
-- so we can route the name through 'runtimeName' rather than hand-edit
-- the encoding.
parseFlattenedName :: Text -> Name
parseFlattenedName t = case T.splitOn ":" t of
  [m, n] -> Qualified m n
  _ -> Unqualified t

-- | Runtime functor name of a constructor declared in the @typechecker@
-- module — base types (@int@), record/tag constructors (@sig@), and
-- compound shapes (@tcon@, @fun@) alike. The renamer canonicalizes
-- such names to @typechecker:<n>@; the runtime functor symbol is the
-- flattened form @typechecker__<n>@. Used as the functor argument of
-- 'VTerm' values this Haskell driver builds, of any arity.
tcAtom :: Text -> Text
tcAtom n = "typechecker__" <> n

-- | A 0-arity declared constructor of the @typechecker@ module
-- (@int@, @float@, @string@, @any@) as a runtime 'Value'. Built as
-- @VTerm name []@ rather than @VAtom name@ so 'matchTerm' (which
-- only recognises 'VTerm') can dispatch on the same shape that
-- compiled head patterns produce.
tcCon0 :: Text -> Value
tcCon0 n = VTerm (tcAtom n) []

-- ---------------------------------------------------------------------------
-- Type-check environment and context
-- ---------------------------------------------------------------------------

-- | Program-wide immutable environment, shared via 'Reader'.
data TypeCheckEnv = TypeCheckEnv
  { -- | Map from constructor name to its parent type definition and constructor info.
    conMap :: Map Name (TypeDefinition, DataConstructor),
    -- | Resolves a use-site unqualified name to its declaration's qualified
    -- name when exactly one constructor matches. Constructors are name-only
    -- in YCHR's type system (arity is not part of their identity), so this
    -- is keyed by name alone — wrong-arity uses are diagnosed separately by
    -- 'validateConstructorArities'. Ambiguous names (declared in more than
    -- one module) are omitted so the canonicalization falls through and the
    -- lookup behaves as if the name were unknown.
    conAlias :: Map Text Name,
    -- | Set of known function identifiers (name, arity).
    funSet :: Set (Name, Int)
  }

-- | Per-rule or per-equation checking context, passed explicitly
-- because it changes at each scope boundary.
data CheckCtx = CheckCtx
  { -- | Maps source variable names to fresh type variables (Values).
    varTypes :: Map Text Value,
    -- | Human-readable label for error messages (e.g., "rule trans").
    label :: Maybe Text,
    -- | Source location of the current AST section.
    loc :: SourceLoc,
    -- | Original PExpr for the current AST section.
    origin :: PExpr
  }

buildConMap :: [TypeDefinition] -> Map Name (TypeDefinition, DataConstructor)
buildConMap tds =
  Map.fromList
    [ (dc.conName, (td, dc))
    | td <- tds,
      dc <- td.constructors
    ]

-- | Detect data constructors declared in more than one type definition.
-- Two constructors collide when they share a 'Qualified m n' after
-- renaming, regardless of arity (the type checker keys constructor
-- lookups on name only — see 'buildConMap' and the CHR-side
-- @delegate_guard_getarg@ / @constructor_match@ rules in
-- @typechecker/typechecker.chr@). Without this check, 'Map.fromList'
-- in 'buildConMap' would silently drop the earlier declaration.
detectDuplicateConstructors :: [TypeDefinition] -> [Diagnostic TypeCheckError]
detectDuplicateConstructors tds =
  [ Diagnostic Nothing (AnnP (DuplicateConstructor (flattenName name) (List.sort decls)) dummyLoc (Atom ""))
  | (name, decls) <- Map.toList grouped,
    length decls > 1
  ]
  where
    grouped =
      Map.fromListWith
        (++)
        [ (dc.conName, [(flattenName td.name, length dc.conArgs)])
        | td <- tds,
          dc <- td.constructors
        ]

-- | Build the use-site → declaration alias map, keyed by unqualified name.
-- A name is included only when exactly one declared constructor uses it;
-- ambiguous names (same unqualified name declared in more than one module)
-- are dropped so 'canonicalizeConName' falls through and the type checker
-- treats the use site as unknown rather than guessing.
buildConAlias :: [TypeDefinition] -> Map Text Name
buildConAlias tds =
  Map.mapMaybe single $
    Map.fromListWith
      (++)
      [ (unqualifiedText dc.conName, [dc.conName])
      | td <- tds,
        dc <- td.constructors
      ]
  where
    single [n] = Just n
    single _ = Nothing
    unqualifiedText (Unqualified t) = t
    unqualifiedText (Qualified _ t) = t

-- | Map a use-site constructor name to its declared, qualified form when a
-- unique match exists. 'Qualified' names pass through unchanged;
-- 'Unqualified' names are resolved through 'conAlias'. When no unique
-- match exists the name is returned as-is.
canonicalizeConName :: TypeCheckEnv -> Name -> Name
canonicalizeConName _ name@(Qualified _ _) = name
canonicalizeConName env (Unqualified n) =
  Map.findWithDefault (Unqualified n) n env.conAlias

-- | True when @name@ is a known data constructor and its declared arity
-- matches @useArity@. Wrong-arity uses are diagnosed by
-- 'validateConstructorArities'; this predicate gates the @check_constructor_use@
-- emissions so we don't pile a spurious tcon mismatch on top of the
-- arity-mismatch error.
knownConstructorWithArity :: TypeCheckEnv -> Name -> Int -> Bool
knownConstructorWithArity env name useArity =
  case Map.lookup name env.conMap of
    Just (_, dc) -> length dc.conArgs == useArity
    Nothing -> False

buildFunSet :: [D.Function] -> Set (Name, Int)
buildFunSet fns = Set.fromList [(f.name, f.arity) | f <- fns]

-- | Source-location info recovered from a CHR-side @Ctx@ handle.
type CtxInfo = (Maybe Text, SourceLoc, PExpr)

-- | Map from @Ctx@ handle (an 'Int') to the originating source location.
type CtxMap = Map Int CtxInfo

-- | Holds the source-location info for every CHR-side @Ctx@ handle the
-- driver has allocated. Threaded as a single 'State' effect so the
-- counter and the map stay in step.
data CtxStore = CtxStore
  { nextId :: !Int,
    ctxMap :: !CtxMap
  }

emptyCtxStore :: CtxStore
emptyCtxStore = CtxStore {nextId = 0, ctxMap = Map.empty}

-- | Effect constraint shared by all internal checking functions.
type CheckEffects es = (CHREffects es, Reader TypeCheckEnv :> es, State CtxStore :> es)

-- ---------------------------------------------------------------------------
-- Main entry point
-- ---------------------------------------------------------------------------

-- | Type-check a desugared program.
--
-- Returns a list of diagnostics for every type inconsistency found.
-- An empty list means the program is well-typed (or has no type
-- annotations — unannotated programs are accepted without errors
-- because missing types default to @any@).
--
-- Type errors prevent compilation from proceeding; the caller is
-- responsible for aborting when the list is non-empty.
typeCheckProgram :: D.Program -> IO [Diagnostic TypeCheckError]
typeCheckProgram prog = do
  let conMap = buildConMap prog.typeDefinitions
      conAlias = buildConAlias prog.typeDefinitions
      funSet = buildFunSet prog.functions
      -- Haskell-side validation
      env = TypeCheckEnv {conMap, conAlias, funSet}
      hsErrors =
        validateTypeDefinitions prog.typeDefinitions (Map.fromList [(td.name, td) | td <- prog.typeDefinitions])
          ++ detectDuplicateConstructors prog.typeDefinitions
          ++ validateConstructorArities env prog
  -- 'withCHR' wants a full 'CompiledProgram', but only reads the four
  -- fields that 'TypeCheckerProgram' carries (program, exportMap,
  -- exportedSet, symbolTable). The remaining fields are stubbed out;
  -- they would be unused even if populated.
  let tcp = typeCheckerProgram
      cp =
        CompiledProgram
          { program = tcp.program,
            exportMap = tcp.exportMap,
            exportedSet = tcp.exportedSet,
            symbolTable = tcp.symbolTable,
            allModules = [],
            opTable = mkOpTable [],
            allFunctions = [],
            nextLambdaIndex = 0,
            functionNameSet = Set.empty,
            desugaredProgram = D.Program [] [] Map.empty []
          }
  chrErrors <- withCHR cp baseHostCallRegistry $ do
    runReader env $
      evalState emptyCtxStore $ do
        -- Initialize error accumulator
        tellConstraint (Qualified "typechecker" "errors") [valueList []]
        -- Tell environment: constraint, function, and constructor signatures
        tellConstraintSigs prog
        tellFunctionSigs prog
        tellConSigs prog
        -- Check each rule and function equation
        mapM_ checkRule prog.rules
        mapM_ checkFunction prog.functions
        -- Collect errors from the CHR session
        collectErrors
  pure (hsErrors ++ chrErrors)

-- | Type-check a list of body goals (a query or single goal) against
-- the signatures of an already-compiled program.
--
-- Mirrors 'typeCheckProgram' but skips Haskell-side validations that
-- only make sense on a whole program (no new type definitions or
-- constructors are introduced by a goal). Variables are gathered once
-- across the whole goal list so a name shared between goals refers to
-- the same type slot — matching how rule bodies are checked.
--
-- Pass the desugared program whose signatures should be in scope. For
-- queries that introduce lifted lambdas, extend @prog.functions@ with
-- those lambdas before calling so their (default-@any@) signatures are
-- visible to @check_function_use@.
typeCheckGoals ::
  D.Program ->
  SourceLoc ->
  Maybe Text ->
  [D.BodyGoal] ->
  IO [Diagnostic TypeCheckError]
typeCheckGoals prog loc lbl goals = do
  let conMap = buildConMap prog.typeDefinitions
      conAlias = buildConAlias prog.typeDefinitions
      funSet = buildFunSet prog.functions
      env = TypeCheckEnv {conMap, conAlias, funSet}
  let tcp = typeCheckerProgram
      cp =
        CompiledProgram
          { program = tcp.program,
            exportMap = tcp.exportMap,
            exportedSet = tcp.exportedSet,
            symbolTable = tcp.symbolTable,
            allModules = [],
            opTable = mkOpTable [],
            allFunctions = [],
            nextLambdaIndex = 0,
            functionNameSet = Set.empty,
            desugaredProgram = D.Program [] [] Map.empty []
          }
  withCHR cp baseHostCallRegistry $ do
    runReader env $
      evalState emptyCtxStore $ do
        tellConstraint (Qualified "typechecker" "errors") [valueList []]
        tellConstraintSigs prog
        tellFunctionSigs prog
        tellConSigs prog
        let allVarNames = foldMap collectVarsInBodyGoal goals
        varTypes <- Map.fromList <$> mapM (\v -> (v,) <$> newVar) (Set.toList allVarNames)
        let cctx = CheckCtx {varTypes, label = lbl, loc, origin = Atom ""}
        mapM_ (checkBodyGoal cctx) goals
        collectErrors

-- ---------------------------------------------------------------------------
-- Context helpers
-- ---------------------------------------------------------------------------

-- | Allocate a fresh integer handle and store the current
-- 'CheckCtx''s source-location info in 'CtxMap' under that handle.
-- The returned 'VInt' is what the CHR rules carry around as the
-- @Ctx@ argument; on error decoding we look the handle back up to
-- recover the source location for the diagnostic.
freshCtxHandle ::
  (State CtxStore :> es) =>
  CheckCtx ->
  Eff es Value
freshCtxHandle cctx = do
  store <- get @CtxStore
  let n = store.nextId
  put
    CtxStore
      { nextId = n + 1,
        ctxMap = Map.insert n (cctx.label, cctx.loc, cctx.origin) store.ctxMap
      }
  pure (VInt n)

-- ---------------------------------------------------------------------------
-- Environment setup
-- ---------------------------------------------------------------------------

tellConstraintSigs :: (CHREffects es, State CtxStore :> es) => D.Program -> Eff es ()
tellConstraintSigs prog =
  Map.foldlWithKey'
    ( \m name argTypes ->
        m >> do
          tvars <- freshTypeVarsForDecl (collectTypeVars argTypes)
          encodedArgs <- traverse (encodeTypeExpr tvars) argTypes
          tellConstraint (Qualified "typechecker" "constraint_sig") [VAtom (runtimeName name), valueList encodedArgs]
    )
    (pure ())
    prog.constraintTypes

tellFunctionSigs :: (CHREffects es, State CtxStore :> es) => D.Program -> Eff es ()
tellFunctionSigs prog = mapM_ tellOne prog.functions
  where
    tellOne f = case f.signatures of
      [] -> do
        -- No annotations: default to all-any.
        let anyArgs = replicate f.arity (tcCon0 "any")
            sig = VTerm (tcAtom "sig") [valueList anyArgs, tcCon0 "any"]
        tellConstraint (Qualified "typechecker" "function_sig") [VAtom (runtimeName f.name), sig]
      [s] -> do
        sig <- encodeFunctionSig s
        tellConstraint (Qualified "typechecker" "function_sig") [VAtom (runtimeName f.name), sig]
      ss -> do
        sigs <- traverse encodeFunctionSig ss
        tellConstraint (Qualified "typechecker" "function_sigs") [VAtom (runtimeName f.name), valueList sigs]

-- | Encode one declared @(arg-types, return-type)@ pair as a runtime
-- @sig(args, ret)@ value, allocating fresh logical variables for the
-- type variables shared between the args and the return.
encodeFunctionSig :: (Unify :> es) => ([TypeExpr], TypeExpr) -> Eff es Value
encodeFunctionSig (argTys, retTy) = do
  tvars <- freshTypeVarsForDecl (collectTypeVars argTys ++ collectTypeVarsExpr retTy)
  encodedArgs <- traverse (encodeTypeExpr tvars) argTys
  encodedRet <- encodeTypeExpr tvars retTy
  pure (VTerm (tcAtom "sig") [valueList encodedArgs, encodedRet])

tellConSigs :: (CHREffects es, State CtxStore :> es) => D.Program -> Eff es ()
tellConSigs prog =
  mapM_
    ( \td ->
        mapM_
          ( \dc -> do
              let allVars = td.typeVars
              tvars <- freshTypeVarsForDecl allVars
              let parentType = encodeTCon tvars td.name td.typeVars
              encodedFields <- traverse (encodeTypeExpr tvars) dc.conArgs
              let sig = VTerm (tcAtom "sig") [parentType, valueList encodedFields]
              tellConstraint (Qualified "typechecker" "con_sig") [VAtom (runtimeName dc.conName), sig]
          )
          td.constructors
    )
    prog.typeDefinitions

-- | Encode a 'Name' as a runtime 'Value', matching the runtime
-- representation produced by 'YCHR.Compile.compileTerm' for declared
-- constructors: every qualified name becomes a 0-arity 'VTerm' with
-- the @vmName@ encoding (@m__n@). Using 'VTerm' (rather than 'VAtom')
-- lets 'matchTerm' dispatch on the same shape that compiled head
-- patterns produce. Unqualified names stay bare 'VAtom's.
encodeName :: Name -> Value
encodeName (Unqualified n) = VAtom n
encodeName name@(Qualified _ _) = VTerm (runtimeName name) []

-- | Encode a type constructor application: tcon(name, [arg1, arg2, ...])
encodeTCon :: Map Text Value -> Name -> [Text] -> Value
encodeTCon tvars name vars =
  VTerm (tcAtom "tcon") [encodeName name, valueList (map (\v -> Map.findWithDefault (tcCon0 "any") v tvars) vars)]

-- ---------------------------------------------------------------------------
-- Type encoding
-- ---------------------------------------------------------------------------

-- | Collect type variable names from a list of type expressions.
collectTypeVars :: [TypeExpr] -> [Text]
collectTypeVars = concatMap collectTypeVarsExpr

collectTypeVarsExpr :: TypeExpr -> [Text]
collectTypeVarsExpr (TypeVar v) = [v]
collectTypeVarsExpr (TypeCon _ args) = concatMap collectTypeVarsExpr args

-- | Create fresh logical variables for each unique type variable name.
freshTypeVarsForDecl :: (Unify :> es) => [Text] -> Eff es (Map Text Value)
freshTypeVarsForDecl vars = do
  let unique = Set.toList (Set.fromList vars)
  pairs <- mapM (\v -> (v,) <$> newVar) unique
  pure (Map.fromList pairs)

-- | Encode a TypeExpr as a runtime Value.
encodeTypeExpr :: (Unify :> es) => Map Text Value -> TypeExpr -> Eff es Value
encodeTypeExpr tvars (TypeVar v) =
  case Map.lookup v tvars of
    Just val -> pure val
    Nothing -> pure (tcCon0 "any")
encodeTypeExpr _ (TypeCon (Unqualified "int") []) = pure (tcCon0 "int")
encodeTypeExpr _ (TypeCon (Unqualified "float") []) = pure (tcCon0 "float")
encodeTypeExpr _ (TypeCon (Unqualified "string") []) = pure (tcCon0 "string")
encodeTypeExpr _ (TypeCon (Unqualified "any") []) = pure (tcCon0 "any")
-- Function type: fun(A, B) -> C is parsed as TypeCon "->" [TypeCon "fun" [A, B], C]
encodeTypeExpr tvars (TypeCon (Unqualified "->") [TypeCon (Unqualified "fun") argTys, retTy]) = do
  encodedArgs <- traverse (encodeTypeExpr tvars) argTys
  encodedRet <- encodeTypeExpr tvars retTy
  pure (VTerm (tcAtom "fun") [valueList encodedArgs, encodedRet])
encodeTypeExpr tvars (TypeCon name args) = do
  encodedArgs <- traverse (encodeTypeExpr tvars) args
  pure (VTerm (tcAtom "tcon") [encodeName name, valueList encodedArgs])

-- ---------------------------------------------------------------------------
-- Per-rule checking
-- ---------------------------------------------------------------------------

checkRule :: (CheckEffects es) => D.Rule -> Eff es ()
checkRule rule = do
  let allVarNames = collectVarsInRule rule
  varTypes <- Map.fromList <$> mapM (\v -> (v,) <$> newVar) (Set.toList allVarNames)
  let ruleLabel = fmap (\n -> "rule " <> n) rule.name
      AnnP hd headLoc headOrigin = rule.head
      AnnP guards guardLoc guardOrigin = rule.guard
      AnnP body bodyLoc bodyOrigin = rule.body
      headCtx = CheckCtx {varTypes, label = ruleLabel, loc = headLoc, origin = headOrigin}
      guardCtx = CheckCtx {varTypes, label = ruleLabel, loc = guardLoc, origin = guardOrigin}
      bodyCtx = CheckCtx {varTypes, label = ruleLabel, loc = bodyLoc, origin = bodyOrigin}
  -- Head constraints (kept and removed)
  mapM_ (checkConstraintUse headCtx) (hd.kept ++ hd.removed)
  -- Guards
  checkGuards guardCtx guards
  -- Body goals
  mapM_ (checkBodyGoal bodyCtx) body

checkConstraintUse :: (CheckEffects es) => CheckCtx -> Types.Constraint -> Eff es ()
checkConstraintUse cctx c = do
  argTypeVars <- traverse (typeOfTerm cctx) c.args
  ctx <- freshCtxHandle cctx
  tellConstraint (Qualified "typechecker" "check_constraint_use") [VAtom (runtimeName c.name), valueList argTypeVars, ctx]

-- ---------------------------------------------------------------------------
-- Guard checking
-- ---------------------------------------------------------------------------

-- | Process a guard list left-to-right, threading the canonicalized
-- constructor name from each 'D.GuardMatch' into any 'D.GuardGetArg's
-- that follow on the same term. Per 'docs/reference/type-system.md' (Desugared
-- guards / HNF synthetic guards), a @GuardGetArg@ always follows a
-- @GuardMatch@ on the same term — the match establishes which
-- constructor's field types to use, which the get-arg then needs to
-- resolve a field index.
checkGuards :: (CheckEffects es) => CheckCtx -> [D.Guard] -> Eff es ()
checkGuards cctx = go Nothing
  where
    go _ [] = pure ()
    go lastConName (g : gs) = do
      newLastCon <- checkGuard cctx lastConName g
      go newLastCon gs

checkGuard :: (CheckEffects es) => CheckCtx -> Maybe Name -> D.Guard -> Eff es (Maybe Name)
checkGuard cctx lastConName (D.GuardEqual t1 t2) = do
  tv1 <- typeOfTerm cctx t1
  tv2 <- typeOfTerm cctx t2
  ctx <- freshCtxHandle cctx
  tellConstraint (Qualified "typechecker" "check_unify") [tv1, tv2, ctx]
  pure lastConName
checkGuard cctx _ (D.GuardMatch term conName arity) = do
  -- Canonicalize the name so subsequent GuardGetArgs (and the
  -- check_constructor_use we emit below) all reference the same
  -- declaration-side qualified form.
  env <- ask @TypeCheckEnv
  let canonical = canonicalizeConName env conName
  -- Emit check_constructor_use only when the constructor is known
  -- \*and* the use-site arity matches the declaration. Wrong-arity
  -- uses are reported by 'validateConstructorArities' as a
  -- ConstructorArityMismatch; here we silently fall through so we
  -- don't pile a spurious tcon mismatch on top of the real error.
  when (knownConstructorWithArity env canonical arity) $ do
    termType <- typeOfTerm cctx term
    argTypeVars <- replicateM arity newVar
    ctx <- freshCtxHandle cctx
    tellConstraint
      (Qualified "typechecker" "check_constructor_use")
      [VAtom (runtimeName canonical), valueList argTypeVars, termType, ctx]
  pure (Just canonical)
checkGuard cctx lastConName (D.GuardGetArg varName term idx) = do
  resultTypeVar <- varType cctx varName
  -- The lastConName fallback covers a (defensively impossible)
  -- GuardGetArg with no preceding GuardMatch on the same term.
  conName <- case lastConName of
    Just cn -> pure cn
    Nothing -> pure (Unqualified varName)
  -- Skip emission when the preceding pattern was a known constructor
  -- but the field index is outside its declared arity. The
  -- ConstructorArityMismatch from 'validateConstructorArities' has
  -- already covered the user-facing error; emitting here would let the
  -- @delegate_guard_getarg@ rule call @nth@ out of bounds.
  env <- ask @TypeCheckEnv
  let withinArity =
        case Map.lookup conName env.conMap of
          Just (_, dc) -> idx < length dc.conArgs
          Nothing -> True -- unknown constructor → unknown_guard_getarg handles it
  when withinArity $ do
    termType <- typeOfTerm cctx term
    ctx <- freshCtxHandle cctx
    tellConstraint (Qualified "typechecker" "check_guard_getarg") [resultTypeVar, termType, VAtom (runtimeName conName), VInt idx, ctx]
  pure lastConName
checkGuard cctx _ (D.GuardExpr term) = do
  tv <- typeOfTerm cctx term
  ctx <- freshCtxHandle cctx
  tellConstraint (Qualified "typechecker" "check_guard_bool") [tv, ctx]
  pure Nothing

-- ---------------------------------------------------------------------------
-- Body goal checking
-- ---------------------------------------------------------------------------

checkBodyGoal :: (CheckEffects es) => CheckCtx -> D.BodyGoal -> Eff es ()
checkBodyGoal _ D.BodyTrue = pure ()
checkBodyGoal cctx (D.BodyConstraint c) =
  checkConstraintUse cctx c
checkBodyGoal cctx (D.BodyUnify t1 t2) = do
  tv1 <- typeOfTerm cctx t1
  tv2 <- typeOfTerm cctx t2
  ctx <- freshCtxHandle cctx
  tellConstraint (Qualified "typechecker" "check_unify") [tv1, tv2, ctx]
-- The spec says `is` is a directed assignment (RHS type flows to LHS).
-- We use bidirectional check_unify here, which is equivalent: if the
-- LHS var is unbound, unify binds it to the RHS type; if already bound,
-- it checks consistency. Both match the spec's semantics.
checkBodyGoal cctx (D.BodyIs v term) = do
  vType <- varType cctx v
  termType <- typeOfTerm cctx term
  ctx <- freshCtxHandle cctx
  tellConstraint (Qualified "typechecker" "check_unify") [vType, termType, ctx]
checkBodyGoal cctx (D.BodyFunctionCall name args) = do
  argTypeVars <- traverse (typeOfTerm cctx) args
  retTypeVar <- newVar
  ctx <- freshCtxHandle cctx
  tellConstraint (Qualified "typechecker" "check_function_use") [VAtom (runtimeName name), valueList argTypeVars, retTypeVar, ctx]
checkBodyGoal cctx (D.BodyHostStmt _ args) = do
  -- Process arguments for side effects (nested constructors/functions still get checked)
  mapM_ (typeOfTerm cctx) args

-- ---------------------------------------------------------------------------
-- Per-equation checking
-- ---------------------------------------------------------------------------

checkFunction :: (CheckEffects es) => D.Function -> Eff es ()
checkFunction func = do
  let AnnP eqs eqLoc eqOrigin = func.equations
  mapM_ (checkEquation func eqLoc eqOrigin) eqs

checkEquation :: (CheckEffects es) => D.Function -> SourceLoc -> PExpr -> D.Equation -> Eff es ()
checkEquation func loc origin eq = do
  let allVarNames = collectVarsInEq eq
  varTypes <- Map.fromList <$> mapM (\v -> (v,) <$> newVar) (Set.toList allVarNames)
  let cctx = CheckCtx {varTypes, label = Just ("function " <> flattenName func.name), loc, origin}
  -- Untyped functions skip equation checking entirely; typed (single or
  -- overloaded) ones go through check_function_use, which dispatches on
  -- whether function_sig (single) or function_sigs (overloaded) is
  -- registered for this name. The CHR rule does the same copy_term-and-
  -- unify work that we'd otherwise do here, so a single emission point
  -- handles both cases.
  case func.signatures of
    [] -> pure ()
    _ -> do
      argTypeVars <- traverse (typeOfTerm cctx) eq.params
      retTypeVar <- typeOfTerm cctx eq.rhs
      ctx <- freshCtxHandle cctx
      tellConstraint
        (Qualified "typechecker" "check_function_use")
        [VAtom (runtimeName func.name), valueList argTypeVars, retTypeVar, ctx]
  checkGuards cctx eq.guards

-- ---------------------------------------------------------------------------
-- Term typing
-- ---------------------------------------------------------------------------

-- | Look up a source variable's pre-allocated type slot, or fall back to
-- a fresh logical variable. The fallback is unreachable for a
-- well-formed desugared AST: 'collectVarsInRule' / 'collectVarsInEq' walk
-- the same nodes that 'typeOfTerm' / @checkGuard@ / @checkBodyGoal@
-- visit, so every variable has an entry in 'CheckCtx.varTypes' before
-- type checking begins. The fallback exists only to keep us from
-- crashing if the desugarer ever emits a variable we missed.
varType :: (Unify :> es) => CheckCtx -> Text -> Eff es Value
varType cctx v = case Map.lookup v cctx.varTypes of
  Just val -> pure val
  Nothing -> newVar

typeOfTerm :: (CheckEffects es) => CheckCtx -> Term -> Eff es Value
typeOfTerm cctx (VarTerm v) = varType cctx v
typeOfTerm _ (IntTerm _) = pure (tcCon0 "int")
typeOfTerm _ (FloatTerm _) = pure (tcCon0 "float")
typeOfTerm _ (TextTerm _) = pure (tcCon0 "string")
typeOfTerm _ Wildcard = newVar
typeOfTerm cctx (AtomTerm s) =
  typeOfAtom cctx (Unqualified s)
typeOfTerm cctx (CompoundTerm name args) =
  typeOfCompound cctx name args

typeOfAtom :: (CheckEffects es) => CheckCtx -> Name -> Eff es Value
typeOfAtom cctx name = do
  env <- ask @TypeCheckEnv
  let canonical = canonicalizeConName env name
  if knownConstructorWithArity env canonical 0
    then do
      resultType <- newVar
      ctx <- freshCtxHandle cctx
      tellConstraint (Qualified "typechecker" "check_constructor_use") [VAtom (runtimeName canonical), valueList [], resultType, ctx]
      pure resultType
    else
      -- Either unknown or a known constructor of nonzero arity (in
      -- which case 'validateConstructorArities' already reported it).
      pure (tcCon0 "any")

typeOfCompound :: (CheckEffects es) => CheckCtx -> Name -> [Term] -> Eff es Value
-- Lambda: fun(X, Y) -> Expr end
-- Represented as CompoundTerm "->" [CompoundTerm "fun" params, body]
typeOfCompound cctx (Unqualified "->") [CompoundTerm (Unqualified "fun") params, body] = do
  paramTypeVars <- traverse (typeOfTerm cctx) params
  bodyType <- typeOfTerm cctx body
  pure (VTerm (tcAtom "fun") [valueList paramTypeVars, bodyType])
-- Function reference: fun name/arity
-- After renaming the outer "fun" is stripped, leaving CompoundTerm "/" [AtomTerm name, IntTerm arity].
-- The renamer flattens the resolved name with @flattenName@ (@:@-separator);
-- 'parseFlattenedName' . 'runtimeName' converts it to the runtime form
-- (@__@-separator) so the emitted @check_function_use@ joins with the
-- @function_sig@ that 'tellFunctionSigs' tells.
typeOfCompound cctx (Unqualified "/") [AtomTerm fname, IntTerm arity] = do
  argTypeVars <- replicateM arity newVar
  retTypeVar <- newVar
  ctx <- freshCtxHandle cctx
  let runtimeFname = runtimeName (parseFlattenedName fname)
  tellConstraint (Qualified "typechecker" "check_function_use") [VAtom runtimeFname, valueList argTypeVars, retTypeVar, ctx]
  pure (VTerm (tcAtom "fun") [valueList argTypeVars, retTypeVar])
-- Constructor or function. Constructors are canonicalized so that bare
-- functor names (e.g. cons "." or own-module names) resolve to their
-- declaration-side qualified form. Wrong-arity constructor uses fall
-- through to the function/unknown path here; 'validateConstructorArities'
-- reports them as ConstructorArityMismatch.
typeOfCompound cctx name args = do
  env <- ask @TypeCheckEnv
  let arity = length args
      canonical = canonicalizeConName env name
  if knownConstructorWithArity env canonical arity
    then do
      argTypes <- traverse (typeOfTerm cctx) args
      resultType <- newVar
      ctx <- freshCtxHandle cctx
      tellConstraint (Qualified "typechecker" "check_constructor_use") [VAtom (runtimeName canonical), valueList argTypes, resultType, ctx]
      pure resultType
    else
      if Set.member (name, arity) env.funSet
        then do
          argTypes <- traverse (typeOfTerm cctx) args
          resultType <- newVar
          ctx <- freshCtxHandle cctx
          tellConstraint (Qualified "typechecker" "check_function_use") [VAtom (runtimeName name), valueList argTypes, resultType, ctx]
          pure resultType
        else do
          -- Unknown (or wrong-arity constructor — error pre-reported).
          -- Process args for side effects, return any.
          mapM_ (typeOfTerm cctx) args
          pure (tcCon0 "any")

-- ---------------------------------------------------------------------------
-- Variable collection
-- ---------------------------------------------------------------------------

collectVarsInRule :: D.Rule -> Set Text
collectVarsInRule rule =
  let AnnP hd _ _ = rule.head
      AnnP guards _ _ = rule.guard
      AnnP body _ _ = rule.body
   in mconcat
        [ foldMap collectVarsInConstraint (hd.kept ++ hd.removed),
          foldMap collectVarsInGuard guards,
          foldMap collectVarsInBodyGoal body
        ]

collectVarsInEq :: D.Equation -> Set Text
collectVarsInEq eq =
  mconcat
    [ foldMap collectVarsInTerm eq.params,
      foldMap collectVarsInGuard eq.guards,
      collectVarsInTerm eq.rhs
    ]

collectVarsInConstraint :: Types.Constraint -> Set Text
collectVarsInConstraint c = foldMap collectVarsInTerm c.args

collectVarsInGuard :: D.Guard -> Set Text
collectVarsInGuard (D.GuardEqual t1 t2) = collectVarsInTerm t1 <> collectVarsInTerm t2
collectVarsInGuard (D.GuardMatch t _ _) = collectVarsInTerm t
collectVarsInGuard (D.GuardGetArg v t _) = Set.singleton v <> collectVarsInTerm t
collectVarsInGuard (D.GuardExpr t) = collectVarsInTerm t

collectVarsInBodyGoal :: D.BodyGoal -> Set Text
collectVarsInBodyGoal D.BodyTrue = Set.empty
collectVarsInBodyGoal (D.BodyConstraint c) = collectVarsInConstraint c
collectVarsInBodyGoal (D.BodyUnify t1 t2) = collectVarsInTerm t1 <> collectVarsInTerm t2
collectVarsInBodyGoal (D.BodyHostStmt _ args) = foldMap collectVarsInTerm args
collectVarsInBodyGoal (D.BodyIs v t) = Set.singleton v <> collectVarsInTerm t
collectVarsInBodyGoal (D.BodyFunctionCall _ args) = foldMap collectVarsInTerm args

collectVarsInTerm :: Term -> Set Text
collectVarsInTerm (VarTerm v) = Set.singleton v
collectVarsInTerm (CompoundTerm _ args) = foldMap collectVarsInTerm args
collectVarsInTerm _ = Set.empty

-- ---------------------------------------------------------------------------
-- Error collection
-- ---------------------------------------------------------------------------

collectErrors ::
  (CheckEffects es) =>
  Eff es [Diagnostic TypeCheckError]
collectErrors = do
  errVar <- newVar
  tellConstraint (Qualified "typechecker" "collect") [errVar]
  errVal <- deref errVar
  store <- get @CtxStore
  decodeErrorList store.ctxMap errVal

decodeErrorList :: (Unify :> es) => CtxMap -> Value -> Eff es [Diagnostic TypeCheckError]
decodeErrorList ctxMap val = do
  case fromValueList val of
    Just items -> concat <$> traverse (decodeError ctxMap) items
    Nothing -> pure []

decodeError :: (Unify :> es) => CtxMap -> Value -> Eff es [Diagnostic TypeCheckError]
decodeError ctxMap (VTerm errorFunctor [ctxVal, codeVal, detailVal])
  | errorFunctor == tcAtom "error" = do
      let (label, loc, origin) = case ctxVal of
            VInt n -> case Map.lookup n ctxMap of
              Just info -> info
              Nothing -> (Nothing, dummyLoc, Atom "")
            _ -> (Nothing, dummyLoc, Atom "")
      code <- deref codeVal
      detail <- deref detailVal
      case code of
        VAtom "inconsistent" -> do
          (t1text, t2text) <- case detail of
            VTerm "pair" [t1, t2] -> do
              t1' <- deref t1
              t2' <- deref t2
              pure (showType t1', showType t2')
            _ -> pure ("?", "?")
          pure [Diagnostic label (AnnP (InconsistentTypes t1text t2text) loc origin)]
        VAtom "unknown_constraint" -> do
          nameText <- showValue detail
          pure [Diagnostic label (AnnP (UnknownConstraint nameText) loc origin)]
        VAtom "unknown_function" -> do
          nameText <- showValue detail
          pure [Diagnostic label (AnnP (UnknownFunction nameText) loc origin)]
        VAtom "no_matching_overload" -> do
          nameText <- showValue detail
          pure [Diagnostic label (AnnP (NoMatchingOverload nameText) loc origin)]
        _ -> pure []
decodeError _ _ = pure []

showType :: Value -> Text
showType (VAtom a) = displayQualifiedAtom a
-- 0-arity declared constructor (e.g. @VTerm "typechecker__int" []@):
-- the runtime form 'compileTerm' produces for any qualified data
-- constructor with no fields, including the four base types
-- @int@/@float@/@string@/@any@.
showType (VTerm functor []) = displayQualifiedAtom functor
showType (VTerm functor [a, b])
  | functor == tcAtom "tcon" =
      let name = showTypeName a
       in case fromValueList b of
            Just [] -> name
            Just as -> name <> "(" <> T.intercalate ", " (map showType as) <> ")"
            Nothing -> name <> "(?)"
  | functor == tcAtom "fun" =
      case fromValueList a of
        Just as -> "fun(" <> T.intercalate ", " (map showType as) <> ") -> " <> showType b
        Nothing -> "fun(?) -> " <> showType b
showType (VVar _) = "_"
showType (VInt n) = T.pack (show n)
showType _ = "?"

showTypeName :: Value -> Text
showTypeName (VAtom a) = displayQualifiedAtom a
showTypeName (VTerm functor []) = displayQualifiedAtom functor
showTypeName _ = "?"

showValue :: (Unify :> es) => Value -> Eff es Text
showValue v = do
  v' <- deref v
  case v' of
    VAtom a -> pure (displayQualifiedAtom a)
    _ -> pure "?"

-- | Convert a runtime-flattened qualified atom (@m__n@) back to the
-- source-level display form (@m:n@). No-op when the atom doesn't
-- contain @__@. Used in error messages so users see familiar syntax.
-- Inverse of 'runtimeName'.
displayQualifiedAtom :: Text -> Text
displayQualifiedAtom = T.replace "__" ":"

dummyLoc :: SourceLoc
dummyLoc = SourceLoc "<typechecker>" 0 0

-- ---------------------------------------------------------------------------
-- Type definition validation (pure, Haskell-side)
-- ---------------------------------------------------------------------------

validateTypeDefinitions :: [TypeDefinition] -> Map Name TypeDefinition -> [Diagnostic TypeCheckError]
validateTypeDefinitions tds typeMap =
  concatMap (validateTypeDef typeMap) tds

validateTypeDef :: Map Name TypeDefinition -> TypeDefinition -> [Diagnostic TypeCheckError]
validateTypeDef typeMap td =
  concatMap (validateConstructor typeMap td) td.constructors

validateConstructor :: Map Name TypeDefinition -> TypeDefinition -> DataConstructor -> [Diagnostic TypeCheckError]
validateConstructor typeMap td dc =
  concatMap (validateFieldType typeMap td dc) dc.conArgs

validateFieldType :: Map Name TypeDefinition -> TypeDefinition -> DataConstructor -> TypeExpr -> [Diagnostic TypeCheckError]
validateFieldType _ td dc (TypeVar v)
  | v `elem` td.typeVars = []
  | otherwise =
      [ Diagnostic
          Nothing
          ( AnnP
              (UnboundTypeVar (flattenName td.name) (flattenName dc.conName) v)
              dummyLoc
              (Atom "")
          )
      ]
validateFieldType typeMap td dc (TypeCon name args) =
  let nameErrors = case name of
        Unqualified n
          | n `elem` ["int", "float", "string", "any"] -> []
        _ ->
          if Map.member name typeMap
            then []
            else
              [ Diagnostic
                  Nothing
                  ( AnnP
                      (UndefinedType (flattenName td.name) (flattenName dc.conName) (flattenName name))
                      dummyLoc
                      (Atom "")
                  )
              ]
      argErrors = concatMap (validateFieldType typeMap td dc) args
   in nameErrors ++ argErrors

-- ---------------------------------------------------------------------------
-- Constructor arity validation (pure, Haskell-side)
-- ---------------------------------------------------------------------------

-- | Walk every term in every rule and equation, and report each use of a
-- known data constructor whose arity differs from its declaration. Done as
-- a pre-pass — separately from the CHR session — so the diagnostic is a
-- direct ConstructorArityMismatch rather than a downstream tcon
-- inconsistency. The check phase silently skips wrong-arity sites
-- (treating them as @any@) so this error is the only one reported for
-- such uses.
validateConstructorArities :: TypeCheckEnv -> D.Program -> [Diagnostic TypeCheckError]
validateConstructorArities env prog =
  concatMap validateRule prog.rules
    ++ concatMap validateFunction prog.functions
  where
    validateRule rule =
      let AnnP hd headLoc headOrigin = rule.head
          AnnP guards guardLoc guardOrigin = rule.guard
          AnnP body bodyLoc bodyOrigin = rule.body
          ruleLabel = fmap (\n -> "rule " <> n) rule.name
          inHead = foldMap termArity (concatMap (.args) (hd.kept ++ hd.removed))
          inGuards = foldMap guardArity guards
          inBody = foldMap bodyArity body
       in mkDiags ruleLabel headLoc headOrigin inHead
            ++ mkDiags ruleLabel guardLoc guardOrigin inGuards
            ++ mkDiags ruleLabel bodyLoc bodyOrigin inBody
    validateFunction func =
      let AnnP eqs loc origin = func.equations
          funLabel = Just ("function " <> flattenName func.name)
          inEqs = foldMap eqArity eqs
       in mkDiags funLabel loc origin inEqs
    eqArity eq =
      foldMap termArity eq.params
        <> foldMap guardArity eq.guards
        <> termArity eq.rhs
    guardArity (D.GuardEqual t1 t2) = termArity t1 <> termArity t2
    guardArity (D.GuardMatch t conName arity) = checkArity conName arity <> termArity t
    guardArity (D.GuardGetArg _ t _) = termArity t
    guardArity (D.GuardExpr t) = termArity t
    bodyArity D.BodyTrue = mempty
    bodyArity (D.BodyConstraint c) = foldMap termArity c.args
    bodyArity (D.BodyUnify t1 t2) = termArity t1 <> termArity t2
    bodyArity (D.BodyIs _ t) = termArity t
    bodyArity (D.BodyFunctionCall _ args) = foldMap termArity args
    bodyArity (D.BodyHostStmt _ args) = foldMap termArity args
    -- An atom is a 0-arity constructor use; a compound is an n-arity use.
    -- Function-reference @name/arity@ and lambdas @fun(...) -> body end@
    -- are compound terms whose subterms (the bare function name, the
    -- lambda parameter list) must NOT be treated as constructor uses,
    -- so we skip walking into them.
    termArity (AtomTerm s) = checkArity (Unqualified s) 0
    termArity (CompoundTerm (Unqualified "/") [AtomTerm _, IntTerm _]) = mempty
    termArity (CompoundTerm (Unqualified "->") [CompoundTerm (Unqualified "fun") _, body]) =
      termArity body
    termArity (CompoundTerm name args) =
      checkArity name (length args) <> foldMap termArity args
    termArity _ = mempty
    checkArity name useArity =
      let canonical = canonicalizeConName env name
       in case Map.lookup canonical env.conMap of
            Just (_, dc)
              | length dc.conArgs /= useArity ->
                  [(canonical, useArity, length dc.conArgs)]
            _ -> []
    mkDiags lbl loc origin =
      map
        ( \(name, useArity, declaredArity) ->
            Diagnostic
              lbl
              ( AnnP
                  (ConstructorArityMismatch (flattenName name) useArity declaredArity)
                  loc
                  origin
              )
        )
