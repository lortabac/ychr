{-# LANGUAGE OverloadedStrings #-}

-- | Haskell driver for the YCHR type checker.
--
-- Walks the desugared AST and feeds constraints into a CHR session
-- running the pre-compiled type-checker program. The type checker
-- catches type inconsistencies statically, while remaining optional:
-- programs without type annotations are accepted without errors.
module YCHR.TypeCheck
  ( TypeCheckError (..),
    typeCheckProgram,
  )
where

import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as T
import Effectful
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
  | UnboundTypeVar Text Text Text
  | UndefinedType Text Text Text
  deriving (Show, Eq)

-- ---------------------------------------------------------------------------
-- Lookup maps
-- ---------------------------------------------------------------------------

-- | Map from constructor name to its parent type definition and constructor info.
type ConMap = Map Name (TypeDefinition, DataConstructor)

-- | Set of known function identifiers (name, arity).
type FunSet = Set (Name, Int)

buildConMap :: [TypeDefinition] -> ConMap
buildConMap tds =
  Map.fromList
    [ (dc.conName, (td, dc))
    | td <- tds,
      dc <- td.constructors
    ]

buildFunSet :: [D.Function] -> FunSet
buildFunSet fns = Set.fromList [(f.name, f.arity) | f <- fns]

-- ---------------------------------------------------------------------------
-- Context tracking
-- ---------------------------------------------------------------------------

-- | Context for error reporting. Maps integer IDs to source information.
type CtxMap = Map Int (Maybe Text, SourceLoc, PExpr)

-- | Per-rule/equation variable type map. Maps source variable names to
-- fresh type variables (Values).
type VarTypes = Map Text Value

-- ---------------------------------------------------------------------------
-- Main entry point
-- ---------------------------------------------------------------------------

-- | Type-check a desugared program. Returns a list of type errors.
-- An empty list means the program is well-typed.
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
  chrErrors <- withCHR cp baseHostCallRegistry $ do
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
        mapM_ (checkRule conMap funSet prog) prog.rules
        -- Check each function equation
        mapM_ (checkFunction conMap funSet prog) prog.functions
        -- Collect errors
        collectErrors
  pure (hsErrors ++ chrErrors)

-- ---------------------------------------------------------------------------
-- Context helpers
-- ---------------------------------------------------------------------------

freshCtx ::
  (State CtxMap :> es, State Int :> es) =>
  Maybe Text ->
  SourceLoc ->
  PExpr ->
  Eff es Value
freshCtx label loc origin = do
  n <- get @Int
  modify @Int (+ 1)
  modify @CtxMap (Map.insert n (label, loc, origin))
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
    ( \f -> case (f.argTypes, f.returnType) of
        (Just argTys, Just retTy) -> do
          let allVars = collectTypeVars argTys ++ collectTypeVarsExpr retTy
          tvars <- freshTypeVarsForDecl allVars
          encodedArgs <- traverse (encodeTypeExpr tvars) argTys
          encodedRet <- encodeTypeExpr tvars retTy
          let sig = VTerm "sig" [valueList encodedArgs, encodedRet]
          tellConstraint (Qualified "typechecker" "function_sig") [VAtom (flattenName f.name), sig]
        _ -> do
          -- No type annotations: default all to any
          let anyArgs = replicate f.arity (VAtom "any")
              sig = VTerm "sig" [valueList anyArgs, VAtom "any"]
          tellConstraint (Qualified "typechecker" "function_sig") [VAtom (flattenName f.name), sig]
    )
    prog.functions

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

-- | Encode a type constructor application: tcon(name, [arg1, arg2, ...])
encodeTCon :: Map Text Value -> Name -> [Text] -> Value
encodeTCon tvars name vars =
  VTerm "tcon" [VAtom (flattenName name), valueList (map (\v -> Map.findWithDefault (VAtom "any") v tvars) vars)]

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
encodeTypeExpr _ (TypeCon (Unqualified "string") []) = pure (VAtom "string")
encodeTypeExpr _ (TypeCon (Unqualified "any") []) = pure (VAtom "any")
encodeTypeExpr tvars (TypeCon name args) = do
  encodedArgs <- traverse (encodeTypeExpr tvars) args
  pure (VTerm "tcon" [VAtom (flattenName name), valueList encodedArgs])

-- ---------------------------------------------------------------------------
-- Per-rule checking
-- ---------------------------------------------------------------------------

checkRule ::
  (CHREffects es, State CtxMap :> es, State Int :> es) =>
  ConMap ->
  FunSet ->
  D.Program ->
  D.Rule ->
  Eff es ()
checkRule conMap funSet prog rule = do
  let allVarNames = collectVarsInRule rule
  varTypes <- Map.fromList <$> mapM (\v -> (v,) <$> newVar) (Set.toList allVarNames)
  let ruleLabel = fmap (\n -> "rule " <> n) rule.name
      AnnP hd headLoc headOrigin = rule.head
      AnnP guards guardLoc guardOrigin = rule.guard
      AnnP body bodyLoc bodyOrigin = rule.body
  -- Head constraints (kept and removed)
  mapM_ (checkConstraintUse conMap funSet prog varTypes ruleLabel headLoc headOrigin) (hd.kept ++ hd.removed)
  -- Guards
  checkGuards conMap funSet prog varTypes ruleLabel guardLoc guardOrigin guards
  -- Body goals
  mapM_ (checkBodyGoal conMap funSet prog varTypes ruleLabel bodyLoc bodyOrigin) body

checkConstraintUse ::
  (CHREffects es, State CtxMap :> es, State Int :> es) =>
  ConMap ->
  FunSet ->
  D.Program ->
  VarTypes ->
  Maybe Text ->
  SourceLoc ->
  PExpr ->
  Types.Constraint ->
  Eff es ()
checkConstraintUse conMap funSet prog varTypes label loc origin c = do
  argTypeVars <- traverse (typeOfTerm conMap funSet prog varTypes label loc origin) c.args
  ctx <- freshCtx label loc origin
  tellConstraint (Qualified "typechecker" "check_constraint_use") [VAtom (flattenName c.name), valueList argTypeVars, ctx]

-- ---------------------------------------------------------------------------
-- Guard checking
-- ---------------------------------------------------------------------------

checkGuards ::
  (CHREffects es, State CtxMap :> es, State Int :> es) =>
  ConMap ->
  FunSet ->
  D.Program ->
  VarTypes ->
  Maybe Text ->
  SourceLoc ->
  PExpr ->
  [D.Guard] ->
  Eff es ()
checkGuards conMap funSet prog varTypes label loc origin = go Nothing
  where
    go _ [] = pure ()
    go lastConName (g : gs) = do
      newLastCon <- checkGuard conMap funSet prog varTypes label loc origin lastConName g
      go newLastCon gs

checkGuard ::
  (CHREffects es, State CtxMap :> es, State Int :> es) =>
  ConMap ->
  FunSet ->
  D.Program ->
  VarTypes ->
  Maybe Text ->
  SourceLoc ->
  PExpr ->
  Maybe Name ->
  D.Guard ->
  Eff es (Maybe Name)
checkGuard conMap funSet prog varTypes label loc origin _ (D.GuardEqual t1 t2) = do
  tv1 <- typeOfTerm conMap funSet prog varTypes label loc origin t1
  tv2 <- typeOfTerm conMap funSet prog varTypes label loc origin t2
  ctx <- freshCtx label loc origin
  tellConstraint (Qualified "typechecker" "check_unify") [tv1, tv2, ctx]
  pure Nothing
checkGuard _ _ _ _ _ _ _ _ (D.GuardMatch _term conName _arity) = do
  -- GuardMatch constrains the term type; we handle it in GuardGetArg
  -- since GuardGetArg always follows GuardMatch on the same term.
  -- Just remember the constructor name.
  pure (Just conName)
checkGuard conMap funSet prog varTypes label loc origin lastConName (D.GuardGetArg varName term idx) = do
  let resultTypeVar = Map.findWithDefault (error "checkGuard: unbound var") varName varTypes
      conName = case lastConName of
        Just cn -> cn
        Nothing -> error "checkGuard: GuardGetArg without preceding GuardMatch"
  termType <- typeOfTerm conMap funSet prog varTypes label loc origin term
  ctx <- freshCtx label loc origin
  tellConstraint (Qualified "typechecker" "check_guard_getarg") [resultTypeVar, termType, VAtom (flattenName conName), VInt idx, ctx]
  pure lastConName
checkGuard conMap funSet prog varTypes label loc origin _ (D.GuardExpr term) = do
  tv <- typeOfTerm conMap funSet prog varTypes label loc origin term
  ctx <- freshCtx label loc origin
  tellConstraint (Qualified "typechecker" "check_guard_bool") [tv, ctx]
  pure Nothing

-- ---------------------------------------------------------------------------
-- Body goal checking
-- ---------------------------------------------------------------------------

checkBodyGoal ::
  (CHREffects es, State CtxMap :> es, State Int :> es) =>
  ConMap ->
  FunSet ->
  D.Program ->
  VarTypes ->
  Maybe Text ->
  SourceLoc ->
  PExpr ->
  D.BodyGoal ->
  Eff es ()
checkBodyGoal _ _ _ _ _ _ _ D.BodyTrue = pure ()
checkBodyGoal conMap funSet prog varTypes label loc origin (D.BodyConstraint c) =
  checkConstraintUse conMap funSet prog varTypes label loc origin c
checkBodyGoal conMap funSet prog varTypes label loc origin (D.BodyUnify t1 t2) = do
  tv1 <- typeOfTerm conMap funSet prog varTypes label loc origin t1
  tv2 <- typeOfTerm conMap funSet prog varTypes label loc origin t2
  ctx <- freshCtx label loc origin
  tellConstraint (Qualified "typechecker" "check_unify") [tv1, tv2, ctx]
checkBodyGoal conMap funSet prog varTypes label loc origin (D.BodyIs v term) = do
  let varType = Map.findWithDefault (error "checkBodyGoal: unbound var") v varTypes
  termType <- typeOfTerm conMap funSet prog varTypes label loc origin term
  ctx <- freshCtx label loc origin
  tellConstraint (Qualified "typechecker" "check_unify") [varType, termType, ctx]
checkBodyGoal conMap funSet prog varTypes label loc origin (D.BodyFunctionCall name args) = do
  argTypeVars <- traverse (typeOfTerm conMap funSet prog varTypes label loc origin) args
  retTypeVar <- newVar
  ctx <- freshCtx label loc origin
  tellConstraint (Qualified "typechecker" "check_function_use") [VAtom (flattenName name), valueList argTypeVars, retTypeVar, ctx]
checkBodyGoal conMap funSet prog varTypes label loc origin (D.BodyHostStmt _ args) = do
  -- Process arguments for side effects (nested constructors/functions still get checked)
  mapM_ (typeOfTerm conMap funSet prog varTypes label loc origin) args

-- ---------------------------------------------------------------------------
-- Per-equation checking
-- ---------------------------------------------------------------------------

checkFunction ::
  (CHREffects es, State CtxMap :> es, State Int :> es) =>
  ConMap ->
  FunSet ->
  D.Program ->
  D.Function ->
  Eff es ()
checkFunction conMap funSet prog func = do
  let AnnP eqs eqLoc eqOrigin = func.equations
  mapM_ (checkEquation conMap funSet prog func eqLoc eqOrigin) eqs

checkEquation ::
  (CHREffects es, State CtxMap :> es, State Int :> es) =>
  ConMap ->
  FunSet ->
  D.Program ->
  D.Function ->
  SourceLoc ->
  PExpr ->
  D.Equation ->
  Eff es ()
checkEquation conMap funSet prog func loc origin eq = do
  let allVarNames = collectVarsInEq eq
  varTypes <- Map.fromList <$> mapM (\v -> (v,) <$> newVar) (Set.toList allVarNames)
  let label = Just ("function " <> flattenName func.name)
  -- Declared types for parameters
  _ <- case (func.argTypes, func.returnType) of
    (Just argTys, Just retTy) -> do
      let allVars = collectTypeVars argTys ++ collectTypeVarsExpr retTy
      tvars <- freshTypeVarsForDecl allVars
      -- Check each parameter against declared type
      mapM_
        ( \(param, declTyExpr) -> do
            paramType <- typeOfTerm conMap funSet prog varTypes label loc origin param
            declType <- encodeTypeExpr tvars declTyExpr
            ctx <- freshCtx label loc origin
            tellConstraint (Qualified "typechecker" "check_unify") [paramType, declType, ctx]
        )
        (zip eq.params argTys)
      -- Check RHS against declared return type
      rhsType <- typeOfTerm conMap funSet prog varTypes label loc origin eq.rhs
      retType <- encodeTypeExpr tvars retTy
      ctx <- freshCtx label loc origin
      tellConstraint (Qualified "typechecker" "check_unify") [rhsType, retType, ctx]
      pure tvars
    _ -> pure Map.empty
  -- Guards
  checkGuards conMap funSet prog varTypes label loc origin eq.guards
  -- Note: RHS already checked above for typed functions; for untyped functions,
  -- the RHS is processed via typeOfTerm in the guard/param checking which
  -- still checks nested expressions.
  pure ()

-- ---------------------------------------------------------------------------
-- Term typing
-- ---------------------------------------------------------------------------

typeOfTerm ::
  (CHREffects es, State CtxMap :> es, State Int :> es) =>
  ConMap ->
  FunSet ->
  D.Program ->
  VarTypes ->
  Maybe Text ->
  SourceLoc ->
  PExpr ->
  Term ->
  Eff es Value
typeOfTerm _ _ _ varTypes _ _ _ (VarTerm v) =
  case Map.lookup v varTypes of
    Just val -> pure val
    Nothing -> newVar -- shouldn't happen for well-formed AST
typeOfTerm _ _ _ _ _ _ _ (IntTerm _) = pure (VAtom "int")
typeOfTerm _ _ _ _ _ _ _ (TextTerm _) = pure (VAtom "string")
typeOfTerm _ _ _ _ _ _ _ Wildcard = newVar
typeOfTerm conMap _ _ _ label loc origin (AtomTerm s) =
  typeOfAtom conMap label loc origin (Unqualified s)
typeOfTerm conMap funSet prog varTypes label loc origin (CompoundTerm name args) =
  typeOfCompound conMap funSet prog varTypes label loc origin name args

typeOfAtom ::
  (CHREffects es, State CtxMap :> es, State Int :> es) =>
  ConMap ->
  Maybe Text ->
  SourceLoc ->
  PExpr ->
  Name ->
  Eff es Value
typeOfAtom conMap label loc origin name =
  case Map.lookup name conMap of
    Just _ -> do
      resultType <- newVar
      ctx <- freshCtx label loc origin
      tellConstraint (Qualified "typechecker" "check_constructor_use") [VAtom (flattenName name), valueList [], resultType, ctx]
      pure resultType
    Nothing -> pure (VAtom "any")

typeOfCompound ::
  (CHREffects es, State CtxMap :> es, State Int :> es) =>
  ConMap ->
  FunSet ->
  D.Program ->
  VarTypes ->
  Maybe Text ->
  SourceLoc ->
  PExpr ->
  Name ->
  [Term] ->
  Eff es Value
-- List cons: [H|T] is CompoundTerm "." [H, T]
typeOfCompound conMap funSet prog varTypes label loc origin (Unqualified ".") [h, t] = do
  -- "." is the list cons constructor
  case Map.lookup (Unqualified ".") conMap of
    Just _ -> do
      argTypes <- traverse (typeOfTerm conMap funSet prog varTypes label loc origin) [h, t]
      resultType <- newVar
      ctx <- freshCtx label loc origin
      tellConstraint (Qualified "typechecker" "check_constructor_use") [VAtom ".", valueList argTypes, resultType, ctx]
      pure resultType
    Nothing -> do
      -- Process args for side effects
      mapM_ (typeOfTerm conMap funSet prog varTypes label loc origin) [h, t]
      pure (VAtom "any")
-- Qualified constructor or function
typeOfCompound conMap funSet prog varTypes label loc origin name args
  | Map.member name conMap = do
      argTypes <- traverse (typeOfTerm conMap funSet prog varTypes label loc origin) args
      resultType <- newVar
      ctx <- freshCtx label loc origin
      tellConstraint (Qualified "typechecker" "check_constructor_use") [VAtom (flattenName name), valueList argTypes, resultType, ctx]
      pure resultType
  | Set.member (name, length args) funSet = do
      argTypes <- traverse (typeOfTerm conMap funSet prog varTypes label loc origin) args
      resultType <- newVar
      ctx <- freshCtx label loc origin
      tellConstraint (Qualified "typechecker" "check_function_use") [VAtom (flattenName name), valueList argTypes, resultType, ctx]
      pure resultType
  | otherwise = do
      -- Unknown: process args for side effects, return any
      mapM_ (typeOfTerm conMap funSet prog varTypes label loc origin) args
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
  (CHREffects es, State CtxMap :> es, State Int :> es) =>
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
    _ -> pure []
decodeError _ _ = pure []

showType :: Value -> Text
showType (VAtom a) = a
showType (VTerm "tcon" [VAtom name, args]) =
  case fromValueList args of
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
