{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}

-- | CHR-to-VM Compiler
--
-- Transforms a desugared CHR program into a VM program following the
-- basic compilation scheme from the paper (Section 5.2) with the
-- Early Drop optimization (Section 5.3, Listing 8).
module YCHR.Compile
  ( CompileError (..),
    compile,
    procNameFor,
  )
where

import Control.Monad (foldM)
import Data.List (partition)
import Data.Map.Strict qualified as Map
import Data.Text (Text)
import Data.Text qualified as T'
import Data.Traversable (for)
import Effectful (Eff, runPureEff)
import Effectful.Writer.Static.Local (Writer, runWriter, tell)
import YCHR.Desugared qualified as D
import YCHR.Types (SymbolTable, lookupSymbol, symbolTableSize, symbolTableToList)
import YCHR.Types qualified as T
import YCHR.VM

data CompileError
  = UnknownConstraintType T.Name
  | UnboundVariable Text
  deriving (Eq, Show)

-- ---------------------------------------------------------------------------
-- Internal types
-- ---------------------------------------------------------------------------

data Occurrence = Occurrence
  { occConName :: T.Name,
    occNumber :: Int,
    occRule :: D.Rule,
    occActiveIdx :: Int,
    occIsKept :: Bool,
    occActiveArgs :: [T.Term],
    occPartners :: [Partner]
  }

data Partner = Partner
  { partIdx :: Int,
    partConstraint :: T.Constraint,
    partIsKept :: Bool,
    partCType :: ConstraintType
  }

type ArityMap = Map.Map T.Name Int

type OccurrenceMap = Map.Map T.Name [Occurrence]

-- ---------------------------------------------------------------------------
-- Public API
-- ---------------------------------------------------------------------------

compile :: D.Program -> SymbolTable -> Either [CompileError] Program
compile prog symTab =
  let arityMap = buildArityMap prog
      (occMap, occErrs) = runPureEff . runWriter $ collectOccurrences symTab prog
      (procs, procErrs) = runPureEff . runWriter $ do
        fmap concat $ traverse (genConstraintProcs symTab arityMap occMap) (symbolTableToList symTab)
      dispatch = genReactivateDispatch symTab arityMap
      allErrs = occErrs ++ procErrs
   in if null allErrs
        then
          Right
            Program
              { progNumTypes = symbolTableSize symTab,
                progProcedures = procs ++ [dispatch]
              }
        else Left allErrs

-- ---------------------------------------------------------------------------
-- Arity map
-- ---------------------------------------------------------------------------

buildArityMap :: D.Program -> ArityMap
buildArityMap (D.Program rules) =
  Map.fromList
    [ (T.conName c, length (T.conArgs c))
    | r <- rules,
      c <-
        D.headKept (D.ruleHead r)
          ++ D.headRemoved (D.ruleHead r)
          ++ [c' | D.BodyConstraint c' <- D.ruleBody r]
    ]

-- ---------------------------------------------------------------------------
-- Occurrence collection
-- ---------------------------------------------------------------------------

collectOccurrences :: SymbolTable -> D.Program -> Eff '[Writer [CompileError]] OccurrenceMap
collectOccurrences symTab (D.Program rules) = do
  allOccs <- fmap concat (traverse (ruleOccurrences symTab) (zip [0 ..] rules))
  let grouped = foldl' (\m occ -> Map.insertWith (++) (occConName occ) [occ] m) Map.empty allOccs
  pure (Map.map (assignNumbers . reverse) grouped)
  where
    assignNumbers occs = zipWith (\n o -> o {occNumber = n}) [1 ..] occs

ruleOccurrences :: SymbolTable -> (Int, D.Rule) -> Eff '[Writer [CompileError]] [Occurrence]
ruleOccurrences symTab (ruleIdx, rule) = do
  let kept = D.headKept (D.ruleHead rule)
      removed = D.headRemoved (D.ruleHead rule)
      combined =
        [(i, c, False) | (i, c) <- zip [0 ..] removed]
          ++ [(i, c, True) | (i, c) <- zip [length removed ..] (reverse kept)]
      ruleName' = case D.ruleName rule of
        Just n -> n
        Nothing -> "rule_" <> T'.pack (show ruleIdx)
  for combined $ \(idx, con, isKept) ->
    mkOccurrence symTab rule ruleName' combined idx con isKept

mkOccurrence ::
  SymbolTable ->
  D.Rule ->
  Text ->
  [(Int, T.Constraint, Bool)] ->
  Int ->
  T.Constraint ->
  Bool ->
  Eff '[Writer [CompileError]] Occurrence
mkOccurrence symTab rule _ruleName combined activeIdx activeCon activeIsKept = do
  let partners' = [(idx, con, isKept) | (idx, con, isKept) <- combined, idx /= activeIdx]
  partners <- for partners' $ \(idx, con, isKept) -> do
    ct <- lookupCType symTab (T.conName con)
    pure
      Partner
        { partIdx = idx,
          partConstraint = con,
          partIsKept = isKept,
          partCType = ct
        }
  pure
    Occurrence
      { occConName = T.conName activeCon,
        occNumber = 0,
        occRule = rule,
        occActiveIdx = activeIdx,
        occIsKept = activeIsKept,
        occActiveArgs = T.conArgs activeCon,
        occPartners = partners
      }

lookupCType :: SymbolTable -> T.Name -> Eff '[Writer [CompileError]] ConstraintType
lookupCType symTab name = case lookupSymbol name symTab of
  Just ct -> pure ct
  Nothing -> do
    tell [UnknownConstraintType name]
    pure (ConstraintType (-1))

-- ---------------------------------------------------------------------------
-- Procedure generation for each constraint type
-- ---------------------------------------------------------------------------

genConstraintProcs :: SymbolTable -> ArityMap -> OccurrenceMap -> (T.Name, ConstraintType) -> Eff '[Writer [CompileError]] [Procedure]
genConstraintProcs symTab arityMap occMap (name, cType) = do
  let arity = Map.findWithDefault 0 name arityMap
      occs = Map.findWithDefault [] name occMap
      tellProc = genTell name cType arity
      activate = genActivate name arity occs
  occProcs <- traverse (genOccurrence symTab name arity) occs
  pure (tellProc : activate : occProcs)

-- ---------------------------------------------------------------------------
-- tell_c
-- ---------------------------------------------------------------------------

genTell :: T.Name -> ConstraintType -> Int -> Procedure
genTell name cType arity =
  let params = argNames arity
      tellName = procNameFor "tell" name
      activateName = procNameFor "activate" name
   in Procedure
        tellName
        params
        [ Let "id" (CreateConstraint cType (map Var params)),
          Store (Var "id"),
          ExprStmt (CallExpr activateName (Var "id" : map Var params))
        ]

-- ---------------------------------------------------------------------------
-- activate_c
-- ---------------------------------------------------------------------------

genActivate :: T.Name -> Int -> [Occurrence] -> Procedure
genActivate name arity occs =
  let params = Name "id" : argNames arity
      activateName = procNameFor "activate" name
      body = concatMap (genActivateCall params) occs ++ [Return (Lit (BoolLit False))]
   in Procedure activateName params body
  where
    genActivateCall params' occ =
      let occName = occProcName name (occNumber occ)
       in [ Let "d" (CallExpr occName (map Var params')),
            If (Var "d") [Return (Lit (BoolLit True))] []
          ]

-- ---------------------------------------------------------------------------
-- occurrence_c_j
-- ---------------------------------------------------------------------------

genOccurrence :: SymbolTable -> T.Name -> Int -> Occurrence -> Eff '[Writer [CompileError]] Procedure
genOccurrence symTab name arity occ = do
  let params = Name "id" : argNames arity
      procName' = occProcName name (occNumber occ)
      varMap = buildVarMap occ
  body <- genOccurrenceBody symTab varMap occ
  pure (Procedure procName' params body)

buildVarMap :: Occurrence -> Map.Map Text Expr
buildVarMap occ =
  let activeBindings =
        [ (v, Var (argName i))
        | (i, T.VarTerm v) <- zip [0 ..] (occActiveArgs occ)
        ]
      partnerBindings =
        [ (v, Var (partArgName k j))
        | (k, partner) <- zip [0 ..] (occPartners occ),
          (j, T.VarTerm v) <- zip [0 ..] (T.conArgs (partConstraint partner))
        ]
   in Map.fromList (activeBindings ++ partnerBindings)

genOccurrenceBody :: SymbolTable -> Map.Map Text Expr -> Occurrence -> Eff '[Writer [CompileError]] [Stmt]
genOccurrenceBody symTab varMap occ
  | null (occPartners occ) = genNoPartnerBody symTab varMap occ
  | otherwise = do
      body <- genPartnerBody symTab varMap occ 0
      pure (body ++ [Return (Lit (BoolLit False))])

-- Single-head rule (no partners)
genNoPartnerBody :: SymbolTable -> Map.Map Text Expr -> Occurrence -> Eff '[Writer [CompileError]] [Stmt]
genNoPartnerBody symTab varMap occ = do
  let guards = D.ruleGuard (occRule occ)
  (wrapper, guardExpr, varMap') <- compileGuards varMap guards
  fireStmts <- genFireStmts symTab varMap' occ
  let inner = case guardExpr of
        Nothing -> fireStmts
        Just gExpr -> [If gExpr fireStmts []]
  pure (wrapper inner ++ [Return (Lit (BoolLit False))])

-- Multi-head rule with partners
genPartnerBody :: SymbolTable -> Map.Map Text Expr -> Occurrence -> Int -> Eff '[Writer [CompileError]] [Stmt]
genPartnerBody symTab varMap occ k
  | k >= length (occPartners occ) = do
      let guards = D.ruleGuard (occRule occ)
      (wrapper, guardExpr, varMap') <- compileGuards varMap guards
      fireStmts <- genFireStmts symTab varMap' occ
      let inner = case guardExpr of
            Nothing -> fireStmts
            Just gExpr -> [If gExpr fireStmts []]
      pure (wrapper inner)
  | otherwise = do
      let partner = occPartners occ !! k
          label = Label ("L" <> T'.pack (show (k + 1)))
          suspVar = partSuspName k
          partArity = length (T.conArgs (partConstraint partner))
          fieldExtracts =
            Let (partIdName k) (FieldGet (Var suspVar) FieldId)
              : [ Let (partArgName k j) (FieldGet (Var suspVar) (FieldArg (ArgIndex j)))
                | j <- [0 .. partArity - 1]
                ]
          aliveCheck = And (Alive (Var "id")) (Alive (Var (partIdName k)))
          distinctActive = Not (IdEqual (Var (partIdName k)) (Var "id"))
          distinctEarlier =
            [ Not (IdEqual (Var (partIdName k)) (Var (partIdName j)))
            | j <- [0 .. k - 1]
            ]
          distinctAll = foldl' And distinctActive distinctEarlier
      innerBody <- genPartnerBody symTab varMap occ (k + 1)
      let innerWithDistinct = [If distinctAll innerBody []]
          innerWithAlive = [If aliveCheck innerWithDistinct []]
          foreachBody = fieldExtracts ++ innerWithAlive
      pure [Foreach label (partCType partner) suspVar [] foreachBody]

-- ---------------------------------------------------------------------------
-- Fire: history check + kill + body + early drop
-- ---------------------------------------------------------------------------

genFireStmts :: SymbolTable -> Map.Map Text Expr -> Occurrence -> Eff '[Writer [CompileError]] [Stmt]
genFireStmts symTab varMap occ = do
  let rule = occRule occ
      isPropagation = null (D.headRemoved (D.ruleHead rule))
      activeIsRemoved = not (occIsKept occ)
      ruleName' = case D.ruleName rule of
        Just n -> RuleName n
        Nothing -> RuleName "rule_anon"
      historyIds = buildHistoryIds occ
      killStmts = genKillStmts occ
  bodyStmts <- compileBodyGoals symTab varMap (D.ruleBody rule)
  let earlyDropStmts
        | activeIsRemoved = [Return (Lit (BoolLit True))]
        | otherwise = [If (Not (Alive (Var "id"))) [Return (Lit (BoolLit True))] []]
      coreFireStmts = killStmts ++ bodyStmts ++ earlyDropStmts
  pure $
    if isPropagation
      then
        [ If
            (NotInHistory ruleName' historyIds)
            (AddHistory ruleName' historyIds : coreFireStmts)
            []
        ]
      else coreFireStmts

buildHistoryIds :: Occurrence -> [Expr]
buildHistoryIds occ =
  let -- All head positions: active + partners, sorted by position index
      allPositions =
        (occActiveIdx occ, Var "id")
          : [ (partIdx p, Var (partIdName k))
            | (k, p) <- zip [0 ..] (occPartners occ)
            ]
      sorted = map snd $ Map.toAscList $ Map.fromList allPositions
   in sorted

genKillStmts :: Occurrence -> [Stmt]
genKillStmts occ =
  let -- Kill removed partners
      partnerKills =
        [ Kill (Var (partIdName k))
        | (k, p) <- zip [0 ..] (occPartners occ),
          not (partIsKept p)
        ]
      -- Kill active if removed
      activeKill = [Kill (Var "id") | not (occIsKept occ)]
   in partnerKills ++ activeKill

-- ---------------------------------------------------------------------------
-- Compile terms
-- ---------------------------------------------------------------------------

compileTerm :: Map.Map Text Expr -> T.Term -> Eff '[Writer [CompileError]] Expr
compileTerm varMap (T.VarTerm v) = case Map.lookup v varMap of
  Just expr -> pure expr
  Nothing -> do
    tell [UnboundVariable v]
    pure (Lit WildcardLit)
compileTerm _ (T.IntTerm n) = pure (Lit (IntLit n))
compileTerm _ (T.AtomTerm s) = pure (Lit (AtomLit s))
compileTerm _ (T.TextTerm s) = pure (Lit (TextLit s))
compileTerm varMap (T.CompoundTerm name args) = do
  args' <- traverse (compileTerm varMap) args
  pure (MakeTerm (vmName name) args')
compileTerm _ T.Wildcard = pure (Lit WildcardLit)

-- ---------------------------------------------------------------------------
-- Compile guards
-- ---------------------------------------------------------------------------

compileGuards ::
  Map.Map Text Expr ->
  [D.Guard] ->
  Eff '[Writer [CompileError]] ([Stmt] -> [Stmt], Maybe Expr, Map.Map Text Expr)
compileGuards varMap guards = do
  let (matchGuards, checkGuards) = partition isMatchGuard guards
  (wrapper, varMap') <- foldM compileMatchGuard (id, varMap) matchGuards
  checkExpr <- compileCheckGuards varMap' checkGuards
  pure (wrapper, checkExpr, varMap')
  where
    isMatchGuard (D.GuardMatch {}) = True
    isMatchGuard (D.GuardGetArg {}) = True
    isMatchGuard _ = False

compileMatchGuard ::
  ([Stmt] -> [Stmt], Map.Map Text Expr) ->
  D.Guard ->
  Eff '[Writer [CompileError]] ([Stmt] -> [Stmt], Map.Map Text Expr)
compileMatchGuard (wrapper, varMap) (D.GuardMatch term name arity) = do
  termExpr <- compileTerm varMap term
  let check body = [If (MatchTerm termExpr (vmName name) arity) body []]
  pure (wrapper . check, varMap)
compileMatchGuard (wrapper, varMap) (D.GuardGetArg vname term idx) = do
  termExpr <- compileTerm varMap term
  let binding body = Let (Name vname) (GetArg termExpr idx) : body
      varMap' = Map.insert vname (Var (Name vname)) varMap
  pure (wrapper . binding, varMap')
compileMatchGuard acc _ = pure acc

compileCheckGuards :: Map.Map Text Expr -> [D.Guard] -> Eff '[Writer [CompileError]] (Maybe Expr)
compileCheckGuards varMap guards = case nonTrivialGuards of
  [] -> pure Nothing
  [g] -> Just <$> compileCheckGuard varMap g
  gs -> Just . foldl1 And <$> traverse (compileCheckGuard varMap) gs
  where
    nonTrivialGuards = filter isNonTrivial guards
    isNonTrivial (D.GuardCommon D.GoalTrue) = False
    isNonTrivial _ = True

compileCheckGuard :: Map.Map Text Expr -> D.Guard -> Eff '[Writer [CompileError]] Expr
compileCheckGuard _ (D.GuardCommon D.GoalTrue) = pure (Lit (BoolLit True))
compileCheckGuard varMap (D.GuardEqual t1 t2) = Equal <$> compileTerm varMap t1 <*> compileTerm varMap t2
compileCheckGuard varMap (D.GuardExpr term) = HostEval <$> compileTerm varMap term
compileCheckGuard _ _ = pure (Lit (BoolLit True))

-- ---------------------------------------------------------------------------
-- Compile body goals
-- ---------------------------------------------------------------------------

compileBodyGoals :: SymbolTable -> Map.Map Text Expr -> [D.BodyGoal] -> Eff '[Writer [CompileError]] [Stmt]
compileBodyGoals _ _ [] = pure []
compileBodyGoals symTab varMap (goal : rest) = case goal of
  D.BodyHostCall v f args -> do
    args' <- traverse (compileTerm varMap) args
    case Map.lookup v varMap of
      Just existing -> do
        let stmts =
              [ ExprStmt (Unify existing (HostCall (Name f) args')),
                DrainReactivationQueue "rs" [ExprStmt (CallExpr "reactivate_dispatch" [Var "rs"])]
              ]
        rest' <- compileBodyGoals symTab varMap rest
        pure (stmts ++ rest')
      Nothing -> do
        let stmt = Let (Name v) (HostCall (Name f) args')
            varMap' = Map.insert v (Var (Name v)) varMap
        rest' <- compileBodyGoals symTab varMap' rest
        pure (stmt : rest')
  D.BodyIs v expr -> do
    expr' <- compileTerm varMap expr
    case Map.lookup v varMap of
      Just existing -> do
        let stmts =
              [ ExprStmt (Unify existing (HostEval expr')),
                DrainReactivationQueue "rs" [ExprStmt (CallExpr "reactivate_dispatch" [Var "rs"])]
              ]
        rest' <- compileBodyGoals symTab varMap rest
        pure (stmts ++ rest')
      Nothing -> do
        let stmt = Let (Name v) (HostEval expr')
            varMap' = Map.insert v (Var (Name v)) varMap
        rest' <- compileBodyGoals symTab varMap' rest
        pure (stmt : rest')
  D.BodyConstraint con -> do
    let argVars = [v | T.VarTerm v <- T.conArgs con, Map.notMember v varMap]
        newStmts = [Let (Name v) NewVar | v <- argVars]
        varMap' = foldl' (\m v -> Map.insert v (Var (Name v)) m) varMap argVars
    callArgs <- traverse (compileTerm varMap') (T.conArgs con)
    let tellName = procNameFor "tell" (T.conName con)
    rest' <- compileBodyGoals symTab varMap' rest
    pure (newStmts ++ [ExprStmt (CallExpr tellName callArgs)] ++ rest')
  _ -> do
    goal' <- compileBodyGoal symTab varMap goal
    rest' <- compileBodyGoals symTab varMap rest
    pure (goal' ++ rest')

compileBodyGoal :: SymbolTable -> Map.Map Text Expr -> D.BodyGoal -> Eff '[Writer [CompileError]] [Stmt]
compileBodyGoal _ _ (D.BodyCommon D.GoalTrue) = pure []
compileBodyGoal _ varMap (D.BodyConstraint con) = do
  args <- traverse (compileTerm varMap) (T.conArgs con)
  let tellName = procNameFor "tell" (T.conName con)
  pure [ExprStmt (CallExpr tellName args)]
compileBodyGoal _ varMap (D.BodyUnify t1 t2) = do
  t1' <- compileTerm varMap t1
  t2' <- compileTerm varMap t2
  pure
    [ ExprStmt (Unify t1' t2'),
      DrainReactivationQueue "rs" [ExprStmt (CallExpr "reactivate_dispatch" [Var "rs"])]
    ]
compileBodyGoal _ varMap (D.BodyHostStmt f args) = do
  args' <- traverse (compileTerm varMap) args
  pure [ExprStmt (HostCall (Name f) args')]
compileBodyGoal _ varMap (D.BodyHostCall v f args) = do
  args' <- traverse (compileTerm varMap) args
  case Map.lookup v varMap of
    Just existing ->
      pure
        [ ExprStmt (Unify existing (HostCall (Name f) args')),
          DrainReactivationQueue "rs" [ExprStmt (CallExpr "reactivate_dispatch" [Var "rs"])]
        ]
    Nothing -> pure [Let (Name v) (HostCall (Name f) args')]
compileBodyGoal _ varMap (D.BodyIs v expr) = do
  expr' <- compileTerm varMap expr
  case Map.lookup v varMap of
    Just existing ->
      pure
        [ ExprStmt (Unify existing (HostEval expr')),
          DrainReactivationQueue "rs" [ExprStmt (CallExpr "reactivate_dispatch" [Var "rs"])]
        ]
    Nothing -> pure [Let (Name v) (HostEval expr')]

-- ---------------------------------------------------------------------------
-- reactivate_dispatch
-- ---------------------------------------------------------------------------

genReactivateDispatch :: SymbolTable -> ArityMap -> Procedure
genReactivateDispatch symTab arityMap =
  let body = map genDispatchBranch (symbolTableToList symTab)
   in Procedure "reactivate_dispatch" ["susp"] body
  where
    genDispatchBranch (name, cType) =
      let arity = Map.findWithDefault 0 name arityMap
          argExtracts =
            [ Let (Name ("rx_" <> T'.pack (show i))) (FieldGet (Var "susp") (FieldArg (ArgIndex i)))
            | i <- [0 .. arity - 1]
            ]
          activateCall =
            ExprStmt
              ( CallExpr
                  (procNameFor "activate" name)
                  (Var "susp" : [Var (Name ("rx_" <> T'.pack (show i))) | i <- [0 .. arity - 1]])
              )
       in If
            (IsConstraintType (Var "susp") cType)
            (argExtracts ++ [activateCall])
            []

-- ---------------------------------------------------------------------------
-- Naming helpers
-- ---------------------------------------------------------------------------

procNameFor :: Text -> T.Name -> Name
procNameFor prefix (T.Qualified m n) = Name (prefix <> "_" <> m <> "_" <> n)
procNameFor prefix (T.Unqualified n) = Name (prefix <> "_" <> n)

occProcName :: T.Name -> Int -> Name
occProcName name num =
  let Name base = procNameFor "occurrence" name
   in Name (base <> "_" <> T'.pack (show num))

vmName :: T.Name -> Name
vmName (T.Unqualified n) = Name n
vmName (T.Qualified m n) = Name (m <> "_" <> n)

argNames :: Int -> [Name]
argNames arity = [argName i | i <- [0 .. arity - 1]]

argName :: Int -> Name
argName i = Name ("X_" <> T'.pack (show i))

partSuspName :: Int -> Name
partSuspName k = Name ("susp_" <> T'.pack (show k))

partIdName :: Int -> Name
partIdName k = Name ("pId_" <> T'.pack (show k))

partArgName :: Int -> Int -> Name
partArgName k j = Name ("pA" <> T'.pack (show j) <> "_" <> T'.pack (show k))
