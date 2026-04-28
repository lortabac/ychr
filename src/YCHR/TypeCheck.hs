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
-- a var, the var is bound to @any@. This means the Haskell driver
-- __must__ always place the source variable's type on the LEFT and
-- the declared type on the RIGHT. Body unifications (@X = Y@) are
-- symmetric (both sides are source variable types) so the asymmetry
-- does not cause issues there.
module YCHR.TypeCheck
  ( TypeCheckError (..),
    typeCheckProgram,
  )
where

import Control.Monad (replicateM)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as T
import Effectful
import Effectful.Reader.Static (Reader, ask, runReader)
import Effectful.State.Static.Local (State, evalState, get, modify)
import YCHR.Compile.Pipeline (CompiledProgram (..))
import YCHR.Desugared qualified as D
import YCHR.Diagnostic (Diagnostic (..))
import YCHR.PExpr (PExpr (Atom), mkOpTable)
import YCHR.Parsed (AnnP (..), SourceLoc (..))
import YCHR.Run (CHREffects, tellConstraint, withCHR)
import YCHR.Runtime.Interpreter (baseHostCallRegistry)
import YCHR.Runtime.Registry (fromValueList, valueList)
import YCHR.Runtime.Types (Value (..))
import YCHR.Runtime.Var (Unify, deref, newVar)
import YCHR.TypeCheck.Compiled (typeCheckerProgram)
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

-- ---------------------------------------------------------------------------
-- Error types
-- ---------------------------------------------------------------------------

data TypeCheckError
  = InconsistentTypes Text Text
  | UnknownConstraint Text
  | UnknownFunction Text
  | NoMatchingOverload Text
  | UnboundTypeVar Text Text Text
  | UndefinedType Text Text Text
  deriving (Show, Eq)

-- ---------------------------------------------------------------------------
-- Type-check environment and context
-- ---------------------------------------------------------------------------

-- | Program-wide immutable environment, shared via 'Reader'.
data TypeCheckEnv = TypeCheckEnv
  { -- | Map from constructor name to its parent type definition and constructor info.
    conMap :: Map Name (TypeDefinition, DataConstructor),
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

buildFunSet :: [D.Function] -> Set (Name, Int)
buildFunSet fns = Set.fromList [(f.name, f.arity) | f <- fns]

-- | Context for error reporting. Maps integer IDs to source information.
type CtxMap = Map Int (Maybe Text, SourceLoc, PExpr)

-- | Effect constraint shared by all internal checking functions.
type CheckEffects es = (CHREffects es, Reader TypeCheckEnv :> es, State CtxMap :> es, State Int :> es)

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
      funSet = buildFunSet prog.functions
      -- Haskell-side validation
      hsErrors = validateTypeDefinitions prog.typeDefinitions (Map.fromList [(td.name, td) | td <- prog.typeDefinitions])
  -- Convert TypeCheckerProgram to a minimal CompiledProgram for withCHR
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
  let env = TypeCheckEnv {conMap, funSet}
  chrErrors <- withCHR cp baseHostCallRegistry $ do
    runReader env $
      evalState (Map.empty :: CtxMap) $
        evalState (0 :: Int) $ do
          -- Initialize error accumulator
          tellConstraint (Qualified "typechecker" "errors") [valueList []]
          -- Tell environment: constraint signatures
          tellConstraintSigs prog
          -- Tell environment: function signatures
          tellFunctionSigs prog
          -- Tell environment: constructor signatures
          tellConSigs prog
          -- Check each rule
          mapM_ checkRule prog.rules
          -- Check each function equation
          mapM_ checkFunction prog.functions
          -- Collect errors
          collectErrors
  pure (hsErrors ++ chrErrors)

-- ---------------------------------------------------------------------------
-- Context helpers
-- ---------------------------------------------------------------------------

freshCtx ::
  (State CtxMap :> es, State Int :> es) =>
  CheckCtx ->
  Eff es Value
freshCtx cctx = do
  n <- get @Int
  modify @Int (+ 1)
  modify @CtxMap (Map.insert n (cctx.label, cctx.loc, cctx.origin))
  pure (VInt n)

-- ---------------------------------------------------------------------------
-- Environment setup
-- ---------------------------------------------------------------------------

tellConstraintSigs :: (CHREffects es, State CtxMap :> es, State Int :> es) => D.Program -> Eff es ()
tellConstraintSigs prog =
  Map.foldlWithKey'
    ( \m name argTypes ->
        m >> do
          tvars <- freshTypeVarsForDecl (collectTypeVars argTypes)
          encodedArgs <- traverse (encodeTypeExpr tvars) argTypes
          tellConstraint (Qualified "typechecker" "constraint_sig") [VAtom (flattenName name), valueList encodedArgs]
    )
    (pure ())
    prog.constraintTypes

tellFunctionSigs :: (CHREffects es, State CtxMap :> es, State Int :> es) => D.Program -> Eff es ()
tellFunctionSigs prog =
  mapM_
    ( \f -> case f.signatures of
        [] -> do
          -- No type annotations: default all to any
          let anyArgs = replicate f.arity (VAtom "any")
              sig = VTerm "sig" [valueList anyArgs, VAtom "any"]
          tellConstraint (Qualified "typechecker" "function_sig") [VAtom (flattenName f.name), sig]
        [(argTys, retTy)] -> do
          -- Single signature: use non-overloaded path
          let allVars = collectTypeVars argTys ++ collectTypeVarsExpr retTy
          tvars <- freshTypeVarsForDecl allVars
          encodedArgs <- traverse (encodeTypeExpr tvars) argTys
          encodedRet <- encodeTypeExpr tvars retTy
          let sig = VTerm "sig" [valueList encodedArgs, encodedRet]
          tellConstraint (Qualified "typechecker" "function_sig") [VAtom (flattenName f.name), sig]
        sigs -> do
          -- Multiple signatures: overloaded path
          encodedSigs <- mapM (encodeSig f.name) sigs
          tellConstraint (Qualified "typechecker" "function_sigs") [VAtom (flattenName f.name), valueList encodedSigs]
    )
    prog.functions
  where
    encodeSig _name (argTys, retTy) = do
      let allVars = collectTypeVars argTys ++ collectTypeVarsExpr retTy
      tvars <- freshTypeVarsForDecl allVars
      encodedArgs <- traverse (encodeTypeExpr tvars) argTys
      encodedRet <- encodeTypeExpr tvars retTy
      pure (VTerm "sig" [valueList encodedArgs, encodedRet])

tellConSigs :: (CHREffects es, State CtxMap :> es, State Int :> es) => D.Program -> Eff es ()
tellConSigs prog =
  mapM_
    ( \td ->
        mapM_
          ( \dc -> do
              let allVars = td.typeVars
              tvars <- freshTypeVarsForDecl allVars
              let parentType = encodeTCon tvars td.name td.typeVars
              encodedFields <- traverse (encodeTypeExpr tvars) dc.conArgs
              let sig = VTerm "sig" [parentType, valueList encodedFields]
              tellConstraint (Qualified "typechecker" "con_sig") [VAtom (flattenName dc.conName), sig]
          )
          td.constructors
    )
    prog.typeDefinitions

-- | Encode a 'Name' as a runtime 'Value', matching CHR runtime
-- representation: unqualified names become atoms, qualified names
-- become @':'(module, name)@ compound terms.
encodeName :: Name -> Value
encodeName (Unqualified n) = VAtom n
encodeName (Qualified m n) = VTerm ":" [VAtom m, VAtom n]

-- | Encode a type constructor application: tcon(name, [arg1, arg2, ...])
encodeTCon :: Map Text Value -> Name -> [Text] -> Value
encodeTCon tvars name vars =
  VTerm "tcon" [encodeName name, valueList (map (\v -> Map.findWithDefault (VAtom "any") v tvars) vars)]

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
    Nothing -> pure (VAtom "any")
encodeTypeExpr _ (TypeCon (Unqualified "int") []) = pure (VAtom "int")
encodeTypeExpr _ (TypeCon (Unqualified "float") []) = pure (VAtom "float")
encodeTypeExpr _ (TypeCon (Unqualified "string") []) = pure (VAtom "string")
encodeTypeExpr _ (TypeCon (Unqualified "any") []) = pure (VAtom "any")
-- Function type: fun(A, B) -> C is parsed as TypeCon "->" [TypeCon "fun" [A, B], C]
encodeTypeExpr tvars (TypeCon (Unqualified "->") [TypeCon (Unqualified "fun") argTys, retTy]) = do
  encodedArgs <- traverse (encodeTypeExpr tvars) argTys
  encodedRet <- encodeTypeExpr tvars retTy
  pure (VTerm "fun" [valueList encodedArgs, encodedRet])
encodeTypeExpr tvars (TypeCon name args) = do
  encodedArgs <- traverse (encodeTypeExpr tvars) args
  pure (VTerm "tcon" [encodeName name, valueList encodedArgs])

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
  ctx <- freshCtx cctx
  tellConstraint (Qualified "typechecker" "check_constraint_use") [VAtom (flattenName c.name), valueList argTypeVars, ctx]

-- ---------------------------------------------------------------------------
-- Guard checking
-- ---------------------------------------------------------------------------

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
  ctx <- freshCtx cctx
  tellConstraint (Qualified "typechecker" "check_unify") [tv1, tv2, ctx]
  pure lastConName
checkGuard _ _ (D.GuardMatch _term conName _arity) = do
  -- GuardMatch is not emitted as a CHR constraint. Its type information
  -- is covered by other paths:
  --   * Non-nullary constructors: the subsequent GuardGetArg(s) emit
  --     check_guard_getarg, which unifies the term type with the
  --     constructor's parent type.
  --   * Nullary constructors: the desugarer produces GuardEqual instead,
  --     and typeOfAtom looks up the constructor's type.
  -- We just remember the constructor name for the following GuardGetArg.
  pure (Just conName)
checkGuard cctx lastConName (D.GuardGetArg varName term idx) = do
  resultTypeVar <- case Map.lookup varName cctx.varTypes of
    Just v -> pure v
    Nothing -> newVar -- defensive: should not happen for well-formed AST
  conName <- case lastConName of
    Just cn -> pure cn
    Nothing -> pure (Unqualified varName) -- defensive: GuardGetArg without GuardMatch
  termType <- typeOfTerm cctx term
  ctx <- freshCtx cctx
  tellConstraint (Qualified "typechecker" "check_guard_getarg") [resultTypeVar, termType, VAtom (flattenName conName), VInt idx, ctx]
  pure lastConName
checkGuard cctx _ (D.GuardExpr term) = do
  tv <- typeOfTerm cctx term
  ctx <- freshCtx cctx
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
  ctx <- freshCtx cctx
  tellConstraint (Qualified "typechecker" "check_unify") [tv1, tv2, ctx]
-- The spec says `is` is a directed assignment (RHS type flows to LHS).
-- We use bidirectional check_unify here, which is equivalent: if the
-- LHS var is unbound, unify binds it to the RHS type; if already bound,
-- it checks consistency. Both match the spec's semantics.
checkBodyGoal cctx (D.BodyIs v term) = do
  varType <- case Map.lookup v cctx.varTypes of
    Just val -> pure val
    Nothing -> newVar -- defensive: should not happen for well-formed AST
  termType <- typeOfTerm cctx term
  ctx <- freshCtx cctx
  tellConstraint (Qualified "typechecker" "check_unify") [varType, termType, ctx]
checkBodyGoal cctx (D.BodyFunctionCall name args) = do
  argTypeVars <- traverse (typeOfTerm cctx) args
  retTypeVar <- newVar
  ctx <- freshCtx cctx
  tellConstraint (Qualified "typechecker" "check_function_use") [VAtom (flattenName name), valueList argTypeVars, retTypeVar, ctx]
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
  -- Declared types for parameters
  _ <- case func.signatures of
    [(argTys, retTy)] -> do
      -- Single signature: check equation against it directly
      let allVars = collectTypeVars argTys ++ collectTypeVarsExpr retTy
      tvars <- freshTypeVarsForDecl allVars
      -- Check each parameter against declared type
      mapM_
        ( \(param, declTyExpr) -> do
            paramType <- typeOfTerm cctx param
            declType <- encodeTypeExpr tvars declTyExpr
            ctx <- freshCtx cctx
            tellConstraint (Qualified "typechecker" "check_unify") [paramType, declType, ctx]
        )
        (zip eq.params argTys)
      -- Check RHS against declared return type
      rhsType <- typeOfTerm cctx eq.rhs
      retType <- encodeTypeExpr tvars retTy
      ctx <- freshCtx cctx
      tellConstraint (Qualified "typechecker" "check_unify") [rhsType, retType, ctx]
      pure tvars
    [] ->
      -- Untyped: no type checking for params/RHS
      pure Map.empty
    _sigs -> do
      -- Overloaded: check equation against all signatures via
      -- check_function_use, which leverages overload resolution
      argTypeVars <- traverse (typeOfTerm cctx) eq.params
      retTypeVar <- typeOfTerm cctx eq.rhs
      ctx <- freshCtx cctx
      tellConstraint (Qualified "typechecker" "check_function_use") [VAtom (flattenName func.name), valueList argTypeVars, retTypeVar, ctx]
      pure Map.empty
  -- Guards
  checkGuards cctx eq.guards
  -- Note: RHS already checked above for typed functions; for untyped functions,
  -- the RHS is processed via typeOfTerm in the guard/param checking which
  -- still checks nested expressions.
  pure ()

-- ---------------------------------------------------------------------------
-- Term typing
-- ---------------------------------------------------------------------------

typeOfTerm :: (CheckEffects es) => CheckCtx -> Term -> Eff es Value
typeOfTerm cctx (VarTerm v) =
  case Map.lookup v cctx.varTypes of
    Just val -> pure val
    Nothing -> newVar -- shouldn't happen for well-formed AST
typeOfTerm _ (IntTerm _) = pure (VAtom "int")
typeOfTerm _ (FloatTerm _) = pure (VAtom "float")
typeOfTerm _ (TextTerm _) = pure (VAtom "string")
typeOfTerm _ Wildcard = newVar
typeOfTerm cctx (AtomTerm s) =
  typeOfAtom cctx (Unqualified s)
typeOfTerm cctx (CompoundTerm name args) =
  typeOfCompound cctx name args

typeOfAtom :: (CheckEffects es) => CheckCtx -> Name -> Eff es Value
typeOfAtom cctx name = do
  env <- ask @TypeCheckEnv
  case Map.lookup name env.conMap of
    Just _ -> do
      resultType <- newVar
      ctx <- freshCtx cctx
      tellConstraint (Qualified "typechecker" "check_constructor_use") [VAtom (flattenName name), valueList [], resultType, ctx]
      pure resultType
    Nothing -> pure (VAtom "any")

typeOfCompound :: (CheckEffects es) => CheckCtx -> Name -> [Term] -> Eff es Value
-- List cons: [H|T] is CompoundTerm "." [H, T]
typeOfCompound cctx (Unqualified ".") [h, t] = do
  env <- ask @TypeCheckEnv
  case Map.lookup (Unqualified ".") env.conMap of
    Just _ -> do
      argTypes <- traverse (typeOfTerm cctx) [h, t]
      resultType <- newVar
      ctx <- freshCtx cctx
      tellConstraint (Qualified "typechecker" "check_constructor_use") [VAtom ".", valueList argTypes, resultType, ctx]
      pure resultType
    Nothing -> do
      -- Process args for side effects
      mapM_ (typeOfTerm cctx) [h, t]
      pure (VAtom "any")
-- Lambda: fun(X, Y) -> Expr end
-- Represented as CompoundTerm "->" [CompoundTerm "fun" params, body]
typeOfCompound cctx (Unqualified "->") [CompoundTerm (Unqualified "fun") params, body] = do
  paramTypeVars <- traverse (typeOfTerm cctx) params
  bodyType <- typeOfTerm cctx body
  pure (VTerm "fun" [valueList paramTypeVars, bodyType])
-- Function reference: fun name/arity
-- After renaming the outer "fun" is stripped, leaving CompoundTerm "/" [AtomTerm name, IntTerm arity]
typeOfCompound cctx (Unqualified "/") [AtomTerm fname, IntTerm arity] = do
  argTypeVars <- replicateM arity newVar
  retTypeVar <- newVar
  ctx <- freshCtx cctx
  tellConstraint (Qualified "typechecker" "check_function_use") [VAtom fname, valueList argTypeVars, retTypeVar, ctx]
  pure (VTerm "fun" [valueList argTypeVars, retTypeVar])
-- Constructor or function
typeOfCompound cctx name args = do
  env <- ask @TypeCheckEnv
  if Map.member name env.conMap
    then do
      argTypes <- traverse (typeOfTerm cctx) args
      resultType <- newVar
      ctx <- freshCtx cctx
      tellConstraint (Qualified "typechecker" "check_constructor_use") [VAtom (flattenName name), valueList argTypes, resultType, ctx]
      pure resultType
    else
      if Set.member (name, length args) env.funSet
        then do
          argTypes <- traverse (typeOfTerm cctx) args
          resultType <- newVar
          ctx <- freshCtx cctx
          tellConstraint (Qualified "typechecker" "check_function_use") [VAtom (flattenName name), valueList argTypes, resultType, ctx]
          pure resultType
        else do
          -- Unknown: process args for side effects, return any
          mapM_ (typeOfTerm cctx) args
          pure (VAtom "any")

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
  ctxMap <- get @CtxMap
  decodeErrorList ctxMap errVal

decodeErrorList :: (Unify :> es) => CtxMap -> Value -> Eff es [Diagnostic TypeCheckError]
decodeErrorList ctxMap val = do
  case fromValueList val of
    Just items -> concat <$> traverse (decodeError ctxMap) items
    Nothing -> pure []

decodeError :: (Unify :> es) => CtxMap -> Value -> Eff es [Diagnostic TypeCheckError]
decodeError ctxMap (VTerm "error" [ctxVal, codeVal, detailVal]) = do
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
showType (VAtom a) = a
showType (VTerm "tcon" [nameVal, args]) =
  let name = showTypeName nameVal
   in case fromValueList args of
        Just [] -> name
        Just as -> name <> "(" <> T.intercalate ", " (map showType as) <> ")"
        Nothing -> name <> "(?)"
showType (VTerm "fun" [args, ret]) =
  case fromValueList args of
    Just as -> "fun(" <> T.intercalate ", " (map showType as) <> ") -> " <> showType ret
    Nothing -> "fun(?) -> " <> showType ret
showType (VVar _) = "_"
showType (VInt n) = T.pack (show n)
showType _ = "?"

showTypeName :: Value -> Text
showTypeName (VAtom a) = a
showTypeName (VTerm ":" [VAtom m, VAtom n]) = m <> ":" <> n
showTypeName _ = "?"

showValue :: (Unify :> es) => Value -> Eff es Text
showValue v = do
  v' <- deref v
  case v' of
    VAtom a -> pure a
    VTerm ":" [VAtom m, VAtom n] -> pure (m <> ":" <> n)
    _ -> pure "?"

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
          | n `elem` ["int", "string", "any"] -> []
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
