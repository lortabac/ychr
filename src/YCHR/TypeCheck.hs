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

import Control.Monad (replicateM, when, zipWithM_)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Reader (ReaderT, ask, runReaderT)
import Control.Monad.Trans.State.Strict (StateT, evalStateT, get, put)
import Data.List qualified as List
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as T
import YCHR.Compile.Names (vmName)
import YCHR.Desugared qualified as D
import YCHR.Diagnostic (Diagnostic (..))
import YCHR.PExpr (PExpr (Atom))
import YCHR.Parsed (AnnP (..), SourceLoc (..))
import YCHR.Runtime.Interpreter (baseHostCallRegistry)
import YCHR.Runtime.Monad (Chr)
import YCHR.Runtime.Registry (fromValueList, valueList)
import YCHR.Runtime.Session (tellConstraint, withCHR)
import YCHR.Runtime.Types (Value (..))
import YCHR.Runtime.Var (deref, newVar)
import YCHR.TypeCheck.Compiled (typeCheckerProgram)
import YCHR.TypeCheck.Error (TypeCheckError (..))
import YCHR.Types
  ( BoundSig (..),
    DataConstructor (..),
    HeadArg (..),
    Name (..),
    Term (..),
    TypeDefinition (..),
    TypeExpr (..),
    flattenName,
    headArgToTerm,
    headConstraintToConstraint,
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
    funSet :: Set (Name, Int),
    -- | Declared bounds for every bounded @:- chr_constraint@. Used
    -- by 'checkRule' to allocate per-head-occurrence ambient
    -- signatures and emit the head-occurrence bound checks
    -- (§Bounded constraints §Use sites).
    constraintBoundsEnv :: Map Types.QualifiedName [BoundSig],
    -- | Declared argument types for every @:- chr_constraint@ —
    -- the same data 'tellConstraintSigs' tells to the CHR program.
    -- Pulled in here so 'checkRule' can encode a bounded
    -- constraint's primary signature against the same σ as its
    -- ambient signatures.
    constraintTypesEnv :: Map Types.QualifiedName [TypeExpr]
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
    origin :: PExpr,
    -- | Ambient signatures contributed by the enclosing bounded
    -- declarations. Keyed by the runtime name of the bound's target
    -- function. Each entry is the list of @sig(args, ret)@ values
    -- visible at every call site in this scope; the list has one
    -- entry per relevant bound currently active. Empty for code
    -- outside any bounded scope.
    --
    -- A call to a function whose name appears in this map is emitted
    -- as @check_function_use_with_ambient@; calls to other functions
    -- use the ordinary @check_function_use@ path. See the CHR
    -- @check_with_ambient_*@ rules in
    -- @typechecker\/typechecker.chr@.
    ambientSigs :: Map Text [Value]
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
  [ Diagnostic
      Nothing
      ( AnnP
          (DuplicateConstructor (flattenName name) (map dropLoc sortedByLoc))
          firstLoc
          (Atom firstTypeName)
      )
  | (name, decls) <- Map.toList grouped,
    length decls > 1,
    let sortedByLoc = List.sortOn (\(_, _, l) -> (l.file, l.line, l.col)) decls,
    (firstTypeName, _, firstLoc) : _ <- [sortedByLoc]
  ]
  where
    dropLoc (tn, ar, _) = (tn, ar)
    grouped =
      Map.fromListWith
        (++)
        [ (dc.conName, [(flattenName td.name, length dc.conArgs, td.loc)])
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
buildFunSet fns = Set.fromList [(Types.qualifiedToName f.name, f.arity) | f <- fns]

-- | Source-location info recovered from a CHR-side @Ctx@ handle.
data CtxInfo = CtxInfo
  { label :: Maybe Text,
    loc :: SourceLoc,
    origin :: PExpr
  }

-- | Opaque handle into 'CtxMap'. Travels through the CHR program as
-- the @Ctx@ argument of every @check_*@ constraint and comes back in
-- 'decodeError' to recover the originating source location. Lives in
-- its own newtype so it cannot be confused with 'ScopeId' (they are
-- both small integers in different namespaces).
newtype CtxHandle = CtxHandle Int
  deriving (Eq, Ord)

-- | Materialize a 'CtxHandle' as the 'Value' the CHR program sees.
ctxHandleValue :: CtxHandle -> Value
ctxHandleValue (CtxHandle n) = VInt n

-- | Ambient-signature scope id. Each bounded scope (a bounded
-- function's equation or a rule with a bounded head constraint) gets
-- its own; @active_scope@ / @end_scope@ pair up by this id so the
-- right ambient signatures are torn down.
newtype ScopeId = ScopeId Int
  deriving (Eq, Ord)

-- | Materialize a 'ScopeId' as the 'Value' the CHR program sees.
scopeIdValue :: ScopeId -> Value
scopeIdValue (ScopeId n) = VInt n

-- | Map from 'CtxHandle' to the originating source location.
type CtxMap = Map CtxHandle CtxInfo

-- | Holds the source-location info for every allocated 'CtxHandle'
-- together with a separate counter for 'ScopeId's. Threaded as a
-- single 'State' effect so both counters and the location map stay in
-- step.
data CtxStore = CtxStore
  { nextCtxHandle :: !CtxHandle,
    ctxMap :: !CtxMap,
    nextScopeId :: !ScopeId
  }

emptyCtxStore :: CtxStore
emptyCtxStore =
  CtxStore
    { nextCtxHandle = CtxHandle 0,
      ctxMap = Map.empty,
      nextScopeId = ScopeId 0
    }

-- | Internal monad of the type-check driver: a 'ReaderT' carrying the
-- program-wide environment over a 'StateT' for the context store,
-- both sitting above the 'Chr' session monad.
type TC = ReaderT TypeCheckEnv (StateT CtxStore Chr)

-- | Lift a 'Chr' action into 'TC'.
chrOp :: Chr a -> TC a
chrOp = lift . lift

-- | Read the context store.
getStore :: TC CtxStore
getStore = lift get

-- | Replace the context store.
putStore :: CtxStore -> TC ()
putStore = lift . put

-- | Allocate a fresh ambient-sig 'ScopeId'.
freshScopeId :: TC ScopeId
freshScopeId = do
  store <- getStore
  let ScopeId n = store.nextScopeId
  putStore store {nextScopeId = ScopeId (n + 1)}
  pure (ScopeId n)

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
      env =
        TypeCheckEnv
          { conMap,
            conAlias,
            funSet,
            constraintBoundsEnv = prog.constraintBounds,
            constraintTypesEnv = prog.constraintTypes
          }
      hsErrors =
        validateTypeDefinitions
          prog.typeDefinitions
          ( Map.fromList
              [ ( td.name,
                  td
                )
              | td <- prog.typeDefinitions
              ]
          )
          ++ detectDuplicateConstructors prog.typeDefinitions
          ++ validateConstructorArities env prog
  chrErrors <-
    withCHR typeCheckerProgram baseHostCallRegistry $
      evalStateT
        ( runReaderT
            ( do
                -- Initialize error accumulator
                chrOp (tellConstraint (Qualified "typechecker" "errors") [valueList []])
                -- Tell environment: constraint, function, and constructor signatures
                tellConstraintSigs prog
                tellFunctionSigs prog
                tellConSigs prog
                -- Check each rule and function equation
                mapM_ checkRule prog.rules
                mapM_ checkFunction prog.functions
                -- Collect errors from the CHR session
                collectErrors
            )
            env
        )
        emptyCtxStore
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
      env =
        TypeCheckEnv
          { conMap,
            conAlias,
            funSet,
            constraintBoundsEnv = prog.constraintBounds,
            constraintTypesEnv = prog.constraintTypes
          }
  withCHR typeCheckerProgram baseHostCallRegistry $
    evalStateT
      ( runReaderT
          ( do
              chrOp (tellConstraint (Qualified "typechecker" "errors") [valueList []])
              tellConstraintSigs prog
              tellFunctionSigs prog
              tellConSigs prog
              let allVarNames = foldMap collectVarsInBodyGoal goals
              varTypes <-
                Map.fromList
                  <$> mapM (\v -> (v,) <$> chrOp newVar) (Set.toList allVarNames)
              let cctx =
                    CheckCtx
                      { varTypes,
                        label = lbl,
                        loc,
                        origin = Atom "",
                        ambientSigs = Map.empty
                      }
              mapM_ (checkBodyGoal cctx) goals
              collectErrors
          )
          env
      )
      emptyCtxStore

-- ---------------------------------------------------------------------------
-- Context helpers
-- ---------------------------------------------------------------------------

-- | Allocate a fresh 'CtxHandle' and store the current 'CheckCtx''s
-- source-location info in 'CtxMap' under it. The handle travels
-- through the CHR program as the @Ctx@ argument of every @check_*@
-- constraint (materialised via 'ctxHandleValue'); on error decoding
-- we look it back up to recover the source location for the
-- diagnostic.
freshCtxHandle :: CheckCtx -> TC CtxHandle
freshCtxHandle cctx = do
  store <- getStore
  let CtxHandle n = store.nextCtxHandle
      handle = CtxHandle n
      info = CtxInfo {label = cctx.label, loc = cctx.loc, origin = cctx.origin}
  putStore
    store
      { nextCtxHandle = CtxHandle (n + 1),
        ctxMap = Map.insert handle info store.ctxMap
      }
  pure handle

-- ---------------------------------------------------------------------------
-- Environment setup
-- ---------------------------------------------------------------------------

-- | Tell @constraint_sig@ for every declared constraint. Bounded
-- constraints additionally emit @constraint_bounds@ using the SAME
-- shared type-variable map so a single @copy_term@ at the use site
-- freshens both the argument types and the bound signatures
-- consistently.
tellConstraintSigs :: D.Program -> TC ()
tellConstraintSigs prog =
  Map.foldlWithKey'
    ( \m name argTypes ->
        m >> do
          let bounds = Map.findWithDefault [] name prog.constraintBounds
              allVars = collectTypeVars argTypes ++ concatMap boundSigVars bounds
          tvars <- chrOp (freshTypeVarsForDecl allVars)
          encodedArgs <- chrOp (traverse (encodeTypeExpr tvars) argTypes)
          let runtimeNm = runtimeName (Types.qualifiedToName name)
          chrOp $
            tellConstraint
              (Qualified "typechecker" "constraint_sig")
              [VAtom runtimeNm, valueList encodedArgs]
          case bounds of
            [] -> pure ()
            _ -> do
              encodedBounds <- chrOp (traverse (encodeNamedBound tvars) bounds)
              chrOp $
                tellConstraint
                  (Qualified "typechecker" "constraint_bounds")
                  [VAtom runtimeNm, valueList encodedBounds]
    )
    (pure ())
    prog.constraintTypes

-- | Tell @function_sig@ or @function_sigs@ for every declared
-- function. Bounded single-sig functions additionally emit
-- @function_bounds@ using a shared type-variable map so a single
-- @copy_term@ at the use site freshens the signature and the
-- bound signatures consistently (see
-- 'YCHR.Types.BoundSig' and the @bounded_function_match@ rule).
tellFunctionSigs :: D.Program -> TC ()
tellFunctionSigs prog = mapM_ tellOne prog.functions
  where
    tellOne f =
      let fName = Types.qualifiedToName f.name
          runtimeNm = runtimeName fName
       in case (f.signatures, f.requiring) of
            ([], _) -> do
              -- No annotations: default to all-any. Bounded functions
              -- always have one signature (the resolver guarantees
              -- this), so a missing signature implies no bounds.
              let anyArgs = replicate f.arity (tcCon0 "any")
                  sig = VTerm (tcAtom "sig") [valueList anyArgs, tcCon0 "any"]
              chrOp $
                tellConstraint
                  (Qualified "typechecker" "function_sig")
                  [VAtom runtimeNm, sig]
            ([s], bounds@(_ : _)) -> do
              let (argTys, retTy) = s
                  allVars =
                    collectTypeVars argTys
                      ++ collectTypeVarsExpr retTy
                      ++ concatMap boundSigVars bounds
              tvars <- chrOp (freshTypeVarsForDecl allVars)
              encodedArgs <- chrOp (traverse (encodeTypeExpr tvars) argTys)
              encodedRet <- chrOp (encodeTypeExpr tvars retTy)
              let sig = VTerm (tcAtom "sig") [valueList encodedArgs, encodedRet]
              encodedBounds <- chrOp (traverse (encodeNamedBound tvars) bounds)
              chrOp $
                tellConstraint
                  (Qualified "typechecker" "function_sig")
                  [VAtom runtimeNm, sig]
              chrOp $
                tellConstraint
                  (Qualified "typechecker" "function_bounds")
                  [VAtom runtimeNm, valueList encodedBounds]
            ([s], []) -> do
              sig <- chrOp (encodeFunctionSig s)
              chrOp $
                tellConstraint
                  (Qualified "typechecker" "function_sig")
                  [VAtom runtimeNm, sig]
            (ss, _) -> do
              sigs <- chrOp (traverse encodeFunctionSig ss)
              chrOp $
                tellConstraint
                  (Qualified "typechecker" "function_sigs")
                  [VAtom runtimeNm, valueList sigs]

-- | Encode one declared @(arg-types, return-type)@ pair as a runtime
-- @sig(args, ret)@ value, allocating fresh logical variables for the
-- type variables shared between the args and the return.
encodeFunctionSig :: ([TypeExpr], TypeExpr) -> Chr Value
encodeFunctionSig (argTys, retTy) = do
  tvars <- freshTypeVarsForDecl (collectTypeVars argTys ++ collectTypeVarsExpr retTy)
  encodedArgs <- traverse (encodeTypeExpr tvars) argTys
  encodedRet <- encodeTypeExpr tvars retTy
  pure (VTerm (tcAtom "sig") [valueList encodedArgs, encodedRet])

-- | Encode a single 'BoundSig' against a shared type-variable map
-- as a runtime @nbound(GName, args, ret)@ value (the flat shape
-- expected by the CHR-side @bound_named@ algebraic type). The
-- shared map is essential: every bound on the same declaration uses
-- the same logical variables for the declaration's type parameters,
-- so a single @copy_term@ at the call site freshens them
-- consistently across signature and bounds.
encodeNamedBound :: Map Text Value -> BoundSig -> Chr Value
encodeNamedBound tvars bs = do
  encodedArgs <- traverse (encodeTypeExpr tvars) bs.argTypes
  encodedRet <- encodeTypeExpr tvars bs.returnType
  pure
    ( VTerm
        (tcAtom "nbound")
        [VAtom (runtimeName bs.name), valueList encodedArgs, encodedRet]
    )

-- | Collect every type variable mentioned in a 'BoundSig'.
boundSigVars :: BoundSig -> [Text]
boundSigVars bs = collectTypeVars bs.argTypes ++ collectTypeVarsExpr bs.returnType

tellConSigs :: D.Program -> TC ()
tellConSigs prog =
  mapM_
    ( \td ->
        mapM_
          ( \dc -> do
              let allVars = td.typeVars
              tvars <- chrOp (freshTypeVarsForDecl allVars)
              let parentType = encodeTCon tvars td.name td.typeVars
              encodedFields <- chrOp (traverse (encodeTypeExpr tvars) dc.conArgs)
              let sig = VTerm (tcAtom "sig") [parentType, valueList encodedFields]
              chrOp $
                tellConstraint
                  (Qualified "typechecker" "con_sig")
                  [ VAtom
                      ( runtimeName
                          dc.conName
                      ),
                    sig
                  ]
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
  VTerm
    (tcAtom "tcon")
    [ encodeName name,
      valueList (map (\v -> Map.findWithDefault (tcCon0 "any") v tvars) vars)
    ]

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
freshTypeVarsForDecl :: [Text] -> Chr (Map Text Value)
freshTypeVarsForDecl vars = do
  let unique = Set.toList (Set.fromList vars)
  pairs <- mapM (\v -> (v,) <$> newVar) unique
  pure (Map.fromList pairs)

-- | Encode a TypeExpr as a runtime Value.
encodeTypeExpr :: Map Text Value -> TypeExpr -> Chr Value
encodeTypeExpr tvars (TypeVar v) =
  case Map.lookup v tvars of
    Just val -> pure val
    Nothing -> pure (tcCon0 "any")
encodeTypeExpr _ (TypeCon (Unqualified "int") []) = pure (tcCon0 "int")
encodeTypeExpr _ (TypeCon (Unqualified "float") []) = pure (tcCon0 "float")
encodeTypeExpr _ (TypeCon (Unqualified "string") []) = pure (tcCon0 "string")
encodeTypeExpr _ (TypeCon (Unqualified "any") []) = pure (tcCon0 "any")
-- Function type: fun(A, B) -> C is parsed as TypeCon "->" [TypeCon "fun" [A, B], C]
encodeTypeExpr
  tvars
  ( TypeCon
      (Unqualified "->")
      [ TypeCon (Unqualified "fun") argTys,
        retTy
        ]
    ) = do
    encodedArgs <- traverse (encodeTypeExpr tvars) argTys
    encodedRet <- encodeTypeExpr tvars retTy
    pure (VTerm (tcAtom "fun") [valueList encodedArgs, encodedRet])
encodeTypeExpr tvars (TypeCon name args) = do
  encodedArgs <- traverse (encodeTypeExpr tvars) args
  pure (VTerm (tcAtom "tcon") [encodeName name, valueList encodedArgs])

-- ---------------------------------------------------------------------------
-- Per-rule checking
-- ---------------------------------------------------------------------------

checkRule :: D.Rule -> TC ()
checkRule rule = do
  env <- ask
  let allVarNames = collectVarsInRule rule
  varTypes <- Map.fromList <$> mapM (\v -> (v,) <$> chrOp newVar) (Set.toList allVarNames)
  let ruleLabel = fmap (\n -> "rule " <> n) rule.name
      AnnP hd headLoc headOrigin = rule.head
      AnnP guards guardLoc guardOrigin = rule.guard
      AnnP body bodyLoc bodyOrigin = rule.body
      headCtx0 =
        CheckCtx
          { varTypes,
            label = ruleLabel,
            loc = headLoc,
            origin = headOrigin,
            ambientSigs = Map.empty
          }
      headConstraints = hd.kept ++ hd.removed
      hasBoundedHead =
        any
          (\hc -> Map.member hc.name env.constraintBoundsEnv)
          headConstraints
  -- Allocate this rule's ambient-sig scope id. Unused when no
  -- bounded constraint sits in the head, but allocating eagerly is
  -- cheap and avoids carrying a "no-scope" sentinel through
  -- 'checkHeadConstraint'.
  scopeId <- freshScopeId
  -- Walk each head constraint. For bounded constraints, allocate a
  -- fresh σ for this head occurrence (per §Use sites: each
  -- occurrence's type variables are freshly allocated even when the
  -- same bounded constraint appears twice) and emit ambient sigs +
  -- bound-discharge residuals. For unbounded constraints, fall
  -- through to the ordinary check.
  ambientPerName <-
    fmap (Map.unionsWith (++)) $
      traverse (checkHeadConstraint headCtx0 scopeId env) headConstraints
  -- Activate the scope so the CHR-side ambient_sig entries are
  -- visible to the body's checks. Skip when there are no bounds:
  -- emitting active_scope with no ambient_sig would still be sound
  -- but pollutes the constraint store.
  when hasBoundedHead $
    chrOp $
      tellConstraint
        (Qualified "typechecker" "active_scope")
        [scopeIdValue scopeId]
  let guardCtx =
        CheckCtx
          { varTypes,
            label = ruleLabel,
            loc = guardLoc,
            origin = guardOrigin,
            ambientSigs = ambientPerName
          }
      bodyCtx =
        CheckCtx
          { varTypes,
            label = ruleLabel,
            loc = bodyLoc,
            origin = bodyOrigin,
            ambientSigs = ambientPerName
          }
  checkGuards guardCtx guards
  mapM_ (checkBodyGoal bodyCtx) body
  when hasBoundedHead $
    chrOp $
      tellConstraint
        (Qualified "typechecker" "end_scope")
        [scopeIdValue scopeId]

-- | Check one head constraint occurrence. Returns the ambient sigs
-- this occurrence contributes (empty for unbounded constraints).
checkHeadConstraint ::
  CheckCtx ->
  ScopeId ->
  TypeCheckEnv ->
  D.HeadConstraint ->
  TC (Map Text [Value])
checkHeadConstraint cctx scopeId env hc =
  case Map.lookup hc.name env.constraintBoundsEnv of
    Nothing -> do
      checkConstraintUse cctx (headConstraintToConstraint hc)
      pure Map.empty
    Just bounds -> do
      let argTypes = Map.findWithDefault [] hc.name env.constraintTypesEnv
          allVars = collectTypeVars argTypes ++ concatMap boundSigVars bounds
      tvars <- chrOp (freshTypeVarsForDecl allVars)
      encodedDeclArgs <- chrOp (traverse (encodeTypeExpr tvars) argTypes)
      headArgValues <- traverse (typeOfTerm cctx . headArgToTerm) hc.args
      ctx <- freshCtxHandle cctx
      zipWithM_ (tellCheckUnify ctx) headArgValues encodedDeclArgs
      ambEntries <- traverse (emitAmbientAndBound scopeId ctx tvars) bounds
      pure (Map.fromListWith (++) ambEntries)

-- | Emit a @check_unify(t1, t2, ctx)@ constraint. The argument order
-- matches the CHR rule: source-variable type first, declared type
-- second. See the @tc_unify@ argument-order note in the module
-- header.
tellCheckUnify :: CtxHandle -> Value -> Value -> TC ()
tellCheckUnify ctx t1 t2 =
  chrOp $
    tellConstraint
      (Qualified "typechecker" "check_unify")
      [t1, t2, ctxHandleValue ctx]

-- | Encode one bound, tell its @ambient_sig@ (for in-scope calls to
-- the bound's named function) and a @check_bound@ residual (for the
-- spec's head-occurrence discharge rule). Returns the @(runtimeName,
-- [sigValue])@ entry the caller folds into the rule's ambient-sigs
-- map so 'CheckCtx.ambientSigs' carries the same data the CHR-side
-- 'check_function_use_with_ambient' rule needs.
emitAmbientAndBound ::
  ScopeId ->
  CtxHandle ->
  Map Text Value ->
  BoundSig ->
  TC (Text, [Value])
emitAmbientAndBound scopeId ctx tvars bs = do
  encodedArgs <- chrOp (traverse (encodeTypeExpr tvars) bs.argTypes)
  encodedRet <- chrOp (encodeTypeExpr tvars bs.returnType)
  let sigVal = VTerm (tcAtom "sig") [valueList encodedArgs, encodedRet]
      runtimeNm = runtimeName bs.name
  chrOp $
    tellConstraint
      (Qualified "typechecker" "ambient_sig")
      [scopeIdValue scopeId, VAtom runtimeNm, sigVal]
  chrOp $
    tellConstraint
      (Qualified "typechecker" "check_bound")
      [VAtom runtimeNm, valueList encodedArgs, encodedRet, ctxHandleValue ctx]
  pure (runtimeNm, [sigVal])

checkConstraintUse :: CheckCtx -> Types.QualifiedConstraint -> TC ()
checkConstraintUse cctx c = do
  argTypeVars <- traverse (typeOfTerm cctx) c.args
  ctx <- freshCtxHandle cctx
  chrOp $
    tellConstraint
      (Qualified "typechecker" "check_constraint_use")
      [ VAtom (runtimeName (Types.qualifiedToName c.name)),
        valueList argTypeVars,
        ctxHandleValue ctx
      ]

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
checkGuards :: CheckCtx -> [D.Guard] -> TC ()
checkGuards cctx = go Nothing
  where
    go _ [] = pure ()
    go lastConName (g : gs) = do
      newLastCon <- checkGuard cctx lastConName g
      go newLastCon gs

checkGuard :: CheckCtx -> Maybe Name -> D.Guard -> TC (Maybe Name)
checkGuard cctx lastConName (D.GuardEqual t1 t2) = do
  tv1 <- typeOfTerm cctx t1
  tv2 <- typeOfTerm cctx t2
  ctx <- freshCtxHandle cctx
  tellCheckUnify ctx tv1 tv2
  pure lastConName
checkGuard cctx _ (D.GuardMatch term conName arity) = do
  env <- ask
  let canonical = canonicalizeConName env conName
  when (knownConstructorWithArity env canonical arity) $ do
    termType <- typeOfTerm cctx term
    argTypeVars <- chrOp (replicateM arity newVar)
    ctx <- freshCtxHandle cctx
    chrOp $
      tellConstraint
        (Qualified "typechecker" "check_constructor_use")
        [ VAtom (runtimeName canonical),
          valueList argTypeVars,
          termType,
          ctxHandleValue ctx
        ]
  pure (Just canonical)
checkGuard cctx lastConName (D.GuardGetArg varName term idx) = do
  resultTypeVar <- chrOp (varType cctx varName)
  conName <- case lastConName of
    Just cn -> pure cn
    Nothing -> pure (Unqualified varName)
  env <- ask
  let withinArity =
        case Map.lookup conName env.conMap of
          Just (_, dc) -> idx < length dc.conArgs
          Nothing -> True
  when withinArity $ do
    termType <- typeOfTerm cctx term
    ctx <- freshCtxHandle cctx
    chrOp $
      tellConstraint
        (Qualified "typechecker" "check_guard_getarg")
        [ resultTypeVar,
          termType,
          VAtom (runtimeName conName),
          VInt idx,
          ctxHandleValue ctx
        ]
  pure lastConName
checkGuard cctx _ (D.GuardExpr term) = do
  tv <- typeOfTerm cctx term
  ctx <- freshCtxHandle cctx
  chrOp $
    tellConstraint
      (Qualified "typechecker" "check_guard_bool")
      [tv, ctxHandleValue ctx]
  pure Nothing

-- ---------------------------------------------------------------------------
-- Body goal checking
-- ---------------------------------------------------------------------------

checkBodyGoal :: CheckCtx -> D.BodyGoal -> TC ()
checkBodyGoal _ D.BodyTrue = pure ()
checkBodyGoal cctx (D.BodyConstraint c) =
  checkConstraintUse cctx c
checkBodyGoal cctx (D.BodyUnify t1 t2) = do
  tv1 <- typeOfTerm cctx t1
  tv2 <- typeOfTerm cctx t2
  ctx <- freshCtxHandle cctx
  tellCheckUnify ctx tv1 tv2
checkBodyGoal cctx (D.BodyIs v term) = do
  vType <- chrOp (varType cctx v)
  termType <- typeOfTerm cctx term
  ctx <- freshCtxHandle cctx
  tellCheckUnify ctx vType termType
checkBodyGoal cctx (D.BodyFunctionCall name args) = do
  argTypeVars <- traverse (typeOfTerm cctx) args
  retTypeVar <- chrOp newVar
  emitFunctionCall cctx name argTypeVars retTypeVar
checkBodyGoal cctx (D.BodyHostStmt _ args) =
  mapM_ (typeOfTerm cctx) args

-- | Emit a function-call type check. Routes through
-- @check_function_use_with_ambient@ when the call's target name has
-- ambient signatures in the current 'CheckCtx' (i.e. the call sits
-- inside a bounded function's equation or under a bounded
-- constraint's head occurrence in a rule). Otherwise falls back to
-- the plain @check_function_use@ path. The CHR side handles both
-- forms with the same overload-resolution mechanism.
emitFunctionCall ::
  CheckCtx ->
  Name ->
  [Value] ->
  Value ->
  TC ()
emitFunctionCall cctx name argTypeVars retTypeVar = do
  ctx <- freshCtxHandle cctx
  let runtimeFname = runtimeName name
      ctxVal = ctxHandleValue ctx
  case Map.lookup runtimeFname cctx.ambientSigs of
    Just ambs@(_ : _) ->
      chrOp $
        tellConstraint
          (Qualified "typechecker" "check_function_use_with_ambient")
          [ VAtom runtimeFname,
            valueList ambs,
            valueList argTypeVars,
            retTypeVar,
            ctxVal
          ]
    _ ->
      chrOp $
        tellConstraint
          (Qualified "typechecker" "check_function_use")
          [ VAtom runtimeFname,
            valueList argTypeVars,
            retTypeVar,
            ctxVal
          ]

-- ---------------------------------------------------------------------------
-- Per-equation checking
-- ---------------------------------------------------------------------------

checkFunction :: D.Function -> TC ()
checkFunction func = do
  let AnnP eqs eqLoc eqOrigin = func.equations
  mapM_ (checkEquation func eqLoc eqOrigin) eqs

checkEquation ::
  D.Function ->
  SourceLoc ->
  PExpr ->
  D.Equation ->
  TC ()
checkEquation func loc origin eq = do
  let allVarNames = collectVarsInEq eq
  varTypes <- Map.fromList <$> mapM (\v -> (v,) <$> chrOp newVar) (Set.toList allVarNames)
  case (func.signatures, func.requiring) of
    ([], _) -> do
      let cctx = freshCheckCtx varTypes Map.empty
      checkGuards cctx eq.guards
    ([sig], bounds@(_ : _)) -> checkBoundedEquation func sig bounds varTypes eq
    (_, _) -> do
      let cctx = freshCheckCtx varTypes Map.empty
      argTypeVars <- traverse (typeOfTerm cctx . headArgToTerm) eq.params
      retTypeVar <- typeOfTerm cctx eq.rhs
      ctx <- freshCtxHandle cctx
      chrOp $
        tellConstraint
          (Qualified "typechecker" "check_function_use")
          [ VAtom (runtimeName (Types.qualifiedToName func.name)),
            valueList argTypeVars,
            retTypeVar,
            ctxHandleValue ctx
          ]
      checkGuards cctx eq.guards
  where
    freshCheckCtx vt ambs =
      CheckCtx
        { varTypes = vt,
          label = Just ("function " <> flattenName (Types.qualifiedToName func.name)),
          loc,
          origin,
          ambientSigs = ambs
        }

-- | Check an equation of a bounded function. Allocates a fresh σ
-- explicitly so the equation's parameter types, RHS type, and the
-- ambient signatures contributed by the function's @requiring@
-- clause all share the same logical variables. This is what makes
-- the spec's "the ambient signature's type variables share identity
-- with the enclosing function's declared type variables" property
-- hold: a call to a bound-named function inside the equation that
-- resolves through the ambient sig stays polymorphic in T, because
-- T is the SAME logical variable the equation parameters' types are
-- bound to.
checkBoundedEquation ::
  D.Function ->
  ([TypeExpr], TypeExpr) ->
  [BoundSig] ->
  Map Text Value ->
  D.Equation ->
  TC ()
checkBoundedEquation func (argTys, retTy) bounds varTypes eq = do
  let allVars =
        collectTypeVars argTys
          ++ collectTypeVarsExpr retTy
          ++ concatMap boundSigVars bounds
  tvars <- chrOp (freshTypeVarsForDecl allVars)
  encodedArgs <- chrOp (traverse (encodeTypeExpr tvars) argTys)
  encodedRet <- chrOp (encodeTypeExpr tvars retTy)
  scopeId <- freshScopeId
  let AnnP _ eqLoc eqOrigin = func.equations
  let baseCtx =
        CheckCtx
          { varTypes,
            label = Just ("function " <> flattenName (Types.qualifiedToName func.name)),
            loc = eqLoc,
            origin = eqOrigin,
            ambientSigs = Map.empty
          }
  ctx <- freshCtxHandle baseCtx
  ambEntries <-
    traverse (emitAmbientAndBound scopeId ctx tvars) bounds
  let ambMap = Map.fromListWith (++) ambEntries
      cctx = baseCtx {ambientSigs = ambMap}
  chrOp $
    tellConstraint
      (Qualified "typechecker" "active_scope")
      [scopeIdValue scopeId]
  paramTypes <- traverse (typeOfTerm cctx . headArgToTerm) eq.params
  zipWithM_ (tellCheckUnify ctx) paramTypes encodedArgs
  rhsType <- typeOfTerm cctx eq.rhs
  tellCheckUnify ctx rhsType encodedRet
  checkGuards cctx eq.guards
  chrOp $
    tellConstraint
      (Qualified "typechecker" "end_scope")
      [scopeIdValue scopeId]

-- ---------------------------------------------------------------------------
-- Term typing
-- ---------------------------------------------------------------------------

-- | Look up a source variable's pre-allocated type slot.
-- 'collectVarsInRule' / 'collectVarsInEq' walk the same nodes that
-- 'typeOfTerm' / @checkGuard@ / @checkBodyGoal@ visit, so every
-- variable has an entry in 'CheckCtx.varTypes' before type checking
-- begins. A missing entry signals a broken invariant in the desugarer
-- or the variable collector.
varType :: CheckCtx -> Text -> Chr Value
varType cctx v = case Map.lookup v cctx.varTypes of
  Just val -> pure val
  Nothing -> error ("TypeCheck.varType: missing var slot for " <> T.unpack v)

typeOfTerm :: CheckCtx -> Term -> TC Value
typeOfTerm cctx (VarTerm v) = chrOp (varType cctx v)
typeOfTerm _ (IntTerm _) = pure (tcCon0 "int")
typeOfTerm _ (FloatTerm _) = pure (tcCon0 "float")
typeOfTerm _ (TextTerm _) = pure (tcCon0 "string")
typeOfTerm _ Wildcard = chrOp newVar
typeOfTerm cctx (AtomTerm s) =
  typeOfAtom cctx (Unqualified s)
typeOfTerm cctx (CompoundTerm name args) =
  typeOfCompound cctx name args

typeOfAtom :: CheckCtx -> Name -> TC Value
typeOfAtom cctx name = do
  env <- ask
  let canonical = canonicalizeConName env name
  if knownConstructorWithArity env canonical 0
    then do
      resultType <- chrOp newVar
      ctx <- freshCtxHandle cctx
      chrOp $
        tellConstraint
          (Qualified "typechecker" "check_constructor_use")
          [ VAtom (runtimeName canonical),
            valueList [],
            resultType,
            ctxHandleValue ctx
          ]
      pure resultType
    else pure (tcCon0 "any")

typeOfCompound :: CheckCtx -> Name -> [Term] -> TC Value
typeOfCompound cctx (Unqualified "->") [CompoundTerm (Unqualified "fun") params, body] = do
  paramTypeVars <- traverse (typeOfTerm cctx) params
  bodyType <- typeOfTerm cctx body
  pure (VTerm (tcAtom "fun") [valueList paramTypeVars, bodyType])
typeOfCompound cctx (Unqualified "/") [AtomTerm fname, IntTerm arity] = do
  argTypeVars <- chrOp (replicateM arity newVar)
  retTypeVar <- chrOp newVar
  emitFunctionCall cctx (parseFlattenedName fname) argTypeVars retTypeVar
  pure (VTerm (tcAtom "fun") [valueList argTypeVars, retTypeVar])
typeOfCompound cctx name args = do
  env <- ask
  let arity = length args
      canonical = canonicalizeConName env name
  if knownConstructorWithArity env canonical arity
    then do
      argTypes <- traverse (typeOfTerm cctx) args
      resultType <- chrOp newVar
      ctx <- freshCtxHandle cctx
      chrOp $
        tellConstraint
          (Qualified "typechecker" "check_constructor_use")
          [ VAtom (runtimeName canonical),
            valueList argTypes,
            resultType,
            ctxHandleValue ctx
          ]
      pure resultType
    else
      if Set.member (name, arity) env.funSet
        then do
          argTypes <- traverse (typeOfTerm cctx) args
          resultType <- chrOp newVar
          emitFunctionCall cctx name argTypes resultType
          pure resultType
        else do
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
      headCs = map headConstraintToConstraint (hd.kept ++ hd.removed)
   in mconcat
        [ foldMap collectVarsInConstraint headCs,
          foldMap collectVarsInGuard guards,
          foldMap collectVarsInBodyGoal body
        ]

collectVarsInEq :: D.Equation -> Set Text
collectVarsInEq eq =
  mconcat
    [ foldMap collectVarsInHeadArg eq.params,
      foldMap collectVarsInGuard eq.guards,
      collectVarsInTerm eq.rhs
    ]

collectVarsInConstraint :: Types.QualifiedConstraint -> Set Text
collectVarsInConstraint c = foldMap collectVarsInTerm c.args

collectVarsInHeadArg :: HeadArg -> Set Text
collectVarsInHeadArg (HeadVar v) = Set.singleton v
collectVarsInHeadArg HeadWildcard = Set.empty

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

collectErrors :: TC [Diagnostic TypeCheckError]
collectErrors = do
  errVar <- chrOp newVar
  chrOp (tellConstraint (Qualified "typechecker" "collect") [errVar])
  errVal <- chrOp (deref errVar)
  store <- getStore
  chrOp (decodeErrorList store.ctxMap errVal)

decodeErrorList :: CtxMap -> Value -> Chr [Diagnostic TypeCheckError]
decodeErrorList ctxMap val = do
  case fromValueList val of
    Just items -> concat <$> traverse (decodeError ctxMap) items
    Nothing -> pure []

decodeError :: CtxMap -> Value -> Chr [Diagnostic TypeCheckError]
decodeError ctxMap val = do
  val' <- deref val
  case val' of
    VTerm errorFunctor [ctxValRaw, codeVal, detailVal]
      | errorFunctor == tcAtom "error" -> decodeErrorBody ctxValRaw codeVal detailVal
    _ ->
      error ("TypeCheck.decodeError: malformed error term: " <> showValueShape val')
  where
    decodeErrorBody ctxValRaw codeVal detailVal = do
      ctxVal <- deref ctxValRaw
      let info = case ctxVal of
            VInt n ->
              Map.findWithDefault
                (error ("TypeCheck.decodeError: orphan Ctx handle " <> show n))
                (CtxHandle n)
                ctxMap
            _ ->
              error
                ( "TypeCheck.decodeError: non-Int Ctx value: "
                    <> showValueShape ctxVal
                )
      code <- deref codeVal
      detail <- deref detailVal
      case code of
        VTerm c [] | c == tcAtom "inconsistent" -> do
          (t1text, t2text) <- case detail of
            VTerm pf [t1, t2] | pf == tcAtom "pair" -> do
              t1' <- deref t1
              t2' <- deref t2
              pure (showType t1', showType t2')
            _ -> pure ("?", "?")
          pure
            [ Diagnostic
                info.label
                ( AnnP
                    (InconsistentTypes t1text t2text)
                    info.loc
                    info.origin
                )
            ]
        VTerm c [] | c == tcAtom "no_matching_overload" -> do
          nameText <- showValue detail
          pure
            [ Diagnostic
                info.label
                ( AnnP
                    (NoMatchingOverload nameText)
                    info.loc
                    info.origin
                )
            ]
        VTerm c [] | c == tcAtom "bound_unsatisfied" -> do
          nameText <- showValue detail
          pure
            [ Diagnostic
                info.label
                ( AnnP
                    (BoundUnsatisfied nameText)
                    info.loc
                    info.origin
                )
            ]
        VTerm c [] ->
          error
            ( "TypeCheck.decodeError: unknown error code "
                <> T.unpack (displayQualifiedAtom c)
            )
        _ -> error "TypeCheck.decodeError: malformed error code value"

-- | One-line description of a runtime 'Value''s outer shape, used only
-- in 'error' messages for broken-invariant cases in 'decodeError'.
showValueShape :: Value -> String
showValueShape (VTerm f xs) =
  "VTerm " <> T.unpack f <> "/" <> show (length xs)
showValueShape (VAtom a) = "VAtom " <> T.unpack a
showValueShape (VInt _) = "VInt"
showValueShape (VFloat _) = "VFloat"
showValueShape (VText _) = "VText"
showValueShape (VBool _) = "VBool"
showValueShape (VVar _) = "VVar"
showValueShape VWildcard = "VWildcard"

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

showValue :: Value -> Chr Text
showValue v = do
  v' <- deref v
  case v' of
    VAtom a -> pure (displayQualifiedAtom a)
    VTerm functor [] -> pure (displayQualifiedAtom functor)
    _ -> pure "?"

-- | Convert a runtime-flattened qualified atom (@m__n@) back to the
-- source-level display form (@m:n@). No-op when the atom doesn't
-- contain @__@. Used in error messages so users see familiar syntax.
-- Inverse of 'runtimeName'.
displayQualifiedAtom :: Text -> Text
displayQualifiedAtom = T.replace "__" ":"

-- ---------------------------------------------------------------------------
-- Type definition validation (pure, Haskell-side)
-- ---------------------------------------------------------------------------

validateTypeDefinitions ::
  [TypeDefinition] ->
  Map Name TypeDefinition ->
  [Diagnostic TypeCheckError]
validateTypeDefinitions tds typeMap =
  concatMap (validateTypeDef typeMap) tds

validateTypeDef :: Map Name TypeDefinition -> TypeDefinition -> [Diagnostic TypeCheckError]
validateTypeDef typeMap td =
  concatMap (validateConstructor typeMap td) td.constructors

validateConstructor ::
  Map Name TypeDefinition ->
  TypeDefinition ->
  DataConstructor ->
  [Diagnostic TypeCheckError]
validateConstructor typeMap td dc =
  concatMap (validateFieldType typeMap td dc) dc.conArgs

validateFieldType ::
  Map Name TypeDefinition ->
  TypeDefinition ->
  DataConstructor ->
  TypeExpr ->
  [Diagnostic TypeCheckError]
validateFieldType _ td dc (TypeVar v)
  | v `elem` td.typeVars = []
  | otherwise =
      [ Diagnostic
          Nothing
          ( AnnP
              (UnboundTypeVar (flattenName td.name) (flattenName dc.conName) v)
              td.loc
              (Atom (flattenName td.name))
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
                      ( UndefinedType
                          (flattenName td.name)
                          (flattenName dc.conName)
                          (flattenName name)
                      )
                      td.loc
                      (Atom (flattenName td.name))
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
          headArgs = concatMap (map headArgToTerm . (.args)) (hd.kept ++ hd.removed)
          inHead = foldMap termArity headArgs
          inGuards = foldMap guardArity guards
          inBody = foldMap bodyArity body
       in mkDiags ruleLabel headLoc headOrigin inHead
            ++ mkDiags ruleLabel guardLoc guardOrigin inGuards
            ++ mkDiags ruleLabel bodyLoc bodyOrigin inBody
    validateFunction func =
      let AnnP eqs loc origin = func.equations
          funLabel =
            Just ("function " <> flattenName (Types.qualifiedToName func.name))
          inEqs = foldMap eqArity eqs
       in mkDiags funLabel loc origin inEqs
    eqArity eq =
      foldMap (termArity . headArgToTerm) eq.params
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
