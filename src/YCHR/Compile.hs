{-# LANGUAGE OverloadedStrings #-}

-- | CHR-to-VM Compiler
--
-- Transforms a desugared CHR program into a VM program following the
-- basic compilation scheme from the paper (Section 5.2) with the
-- Early Drop optimization (Section 5.3, Listing 8).
module YCHR.Compile
  ( compile,
  )
where

import Data.Map.Strict qualified as Map
import YCHR.Desugared qualified as D
import YCHR.Types qualified as T
import YCHR.VM

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

type SymbolTable = Map.Map T.Name ConstraintType

type ArityMap = Map.Map T.Name Int

type OccurrenceMap = Map.Map T.Name [Occurrence]

-- ---------------------------------------------------------------------------
-- Public API
-- ---------------------------------------------------------------------------

compile :: D.Program -> SymbolTable -> Program
compile prog symTab =
  let arityMap = buildArityMap prog
      occMap = collectOccurrences symTab prog
      procs = concatMap (genConstraintProcs symTab arityMap occMap) (Map.toList symTab)
      dispatch = genReactivateDispatch symTab arityMap
   in Program
        { progNumTypes = Map.size symTab,
          progProcedures = procs ++ [dispatch]
        }

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

collectOccurrences :: SymbolTable -> D.Program -> OccurrenceMap
collectOccurrences symTab (D.Program rules) =
  let -- Accumulate occurrences per constraint type across all rules
      allOccs = concatMap (ruleOccurrences symTab) (zip [0 ..] rules)
      -- Group by constraint name and assign occurrence numbers
      grouped = foldl' (\m occ -> Map.insertWith (++) (occConName occ) [occ] m) Map.empty allOccs
   in Map.map (assignNumbers . reverse) grouped
  where
    assignNumbers occs = zipWith (\n o -> o {occNumber = n}) [1 ..] occs

ruleOccurrences :: SymbolTable -> (Int, D.Rule) -> [Occurrence]
ruleOccurrences symTab (ruleIdx, rule) =
  let kept = D.headKept (D.ruleHead rule)
      removed = D.headRemoved (D.ruleHead rule)
      -- Combined head list: removed left-to-right, then kept right-to-left
      combined =
        [(i, c, False) | (i, c) <- zip [0 ..] removed]
          ++ [(i, c, True) | (i, c) <- zip [length removed ..] (reverse kept)]
      ruleName' = case D.ruleName rule of
        Just n -> n
        Nothing -> "rule_" ++ show ruleIdx
   in [ mkOccurrence symTab rule ruleName' combined idx con isKept
      | (idx, con, isKept) <- combined
      ]

mkOccurrence ::
  SymbolTable ->
  D.Rule ->
  String ->
  [(Int, T.Constraint, Bool)] ->
  Int ->
  T.Constraint ->
  Bool ->
  Occurrence
mkOccurrence symTab rule _ruleName combined activeIdx activeCon activeIsKept =
  let partners =
        [ Partner
            { partIdx = idx,
              partConstraint = con,
              partIsKept = isKept,
              partCType = lookupCType symTab (T.conName con)
            }
        | (idx, con, isKept) <- combined,
          idx /= activeIdx
        ]
   in Occurrence
        { occConName = T.conName activeCon,
          occNumber = 0, -- assigned later
          occRule = rule,
          occActiveIdx = activeIdx,
          occIsKept = activeIsKept,
          occActiveArgs = T.conArgs activeCon,
          occPartners = partners
        }

lookupCType :: SymbolTable -> T.Name -> ConstraintType
lookupCType symTab name = case Map.lookup name symTab of
  Just ct -> ct
  Nothing -> error $ "Compile: unknown constraint type: " ++ show name

-- ---------------------------------------------------------------------------
-- Procedure generation for each constraint type
-- ---------------------------------------------------------------------------

genConstraintProcs :: SymbolTable -> ArityMap -> OccurrenceMap -> (T.Name, ConstraintType) -> [Procedure]
genConstraintProcs symTab arityMap occMap (name, cType) =
  let arity = Map.findWithDefault 0 name arityMap
      occs = Map.findWithDefault [] name occMap
      tell = genTell name cType arity
      activate = genActivate name arity occs
      occProcs = map (genOccurrence symTab name arity) occs
   in tell : activate : occProcs

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

genOccurrence :: SymbolTable -> T.Name -> Int -> Occurrence -> Procedure
genOccurrence symTab name arity occ =
  let params = Name "id" : argNames arity
      procName' = occProcName name (occNumber occ)
      varMap = buildVarMap occ
      body = genOccurrenceBody symTab varMap occ
   in Procedure procName' params body

buildVarMap :: Occurrence -> Map.Map String Expr
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

genOccurrenceBody :: SymbolTable -> Map.Map String Expr -> Occurrence -> [Stmt]
genOccurrenceBody symTab varMap occ
  | null (occPartners occ) = genNoPartnerBody symTab varMap occ
  | otherwise = genPartnerBody symTab varMap occ 0 ++ [Return (Lit (BoolLit False))]

-- Single-head rule (no partners)
genNoPartnerBody :: SymbolTable -> Map.Map String Expr -> Occurrence -> [Stmt]
genNoPartnerBody symTab varMap occ =
  let guards = D.ruleGuard (occRule occ)
      guardExpr = compileGuards varMap guards
      fireStmts = genFireStmts symTab varMap occ
   in case guardExpr of
        Nothing -> fireStmts ++ [Return (Lit (BoolLit False))]
        Just gExpr -> [If gExpr fireStmts [], Return (Lit (BoolLit False))]

-- Multi-head rule with partners
genPartnerBody :: SymbolTable -> Map.Map String Expr -> Occurrence -> Int -> [Stmt]
genPartnerBody symTab varMap occ k
  | k >= length (occPartners occ) =
      -- Innermost: check guards and fire
      let guards = D.ruleGuard (occRule occ)
          guardExpr = compileGuards varMap guards
          fireStmts = genFireStmts symTab varMap occ
       in case guardExpr of
            Nothing -> fireStmts
            Just gExpr -> [If gExpr fireStmts []]
  | otherwise =
      let partner = occPartners occ !! k
          label = Label ("L" ++ show (k + 1))
          suspVar = partSuspName k
          partArity = length (T.conArgs (partConstraint partner))
          -- Extract fields
          fieldExtracts =
            Let (partIdName k) (FieldGet (Var suspVar) FieldId)
              : [ Let (partArgName k j) (FieldGet (Var suspVar) (FieldArg (ArgIndex j)))
                | j <- [0 .. partArity - 1]
                ]
          -- Alive checks
          aliveCheck = And (Alive (Var "id")) (Alive (Var (partIdName k)))
          -- ID distinctness: not equal to active constraint
          distinctActive = Not (IdEqual (Var (partIdName k)) (Var "id"))
          -- ID distinctness: not equal to earlier partners
          distinctEarlier =
            [ Not (IdEqual (Var (partIdName k)) (Var (partIdName j)))
            | j <- [0 .. k - 1]
            ]
          -- Combine distinctness checks
          distinctAll = foldl' And distinctActive distinctEarlier
          -- Inner body (next partner or fire)
          innerBody = genPartnerBody symTab varMap occ (k + 1)
          -- Nest the checks
          innerWithDistinct = [If distinctAll innerBody []]
          innerWithAlive = [If aliveCheck innerWithDistinct []]
          foreachBody = fieldExtracts ++ innerWithAlive
       in [Foreach label (partCType partner) suspVar [] foreachBody]

-- ---------------------------------------------------------------------------
-- Fire: history check + kill + body + early drop
-- ---------------------------------------------------------------------------

genFireStmts :: SymbolTable -> Map.Map String Expr -> Occurrence -> [Stmt]
genFireStmts symTab varMap occ =
  let rule = occRule occ
      isPropagation = null (D.headRemoved (D.ruleHead rule))
      activeIsRemoved = not (occIsKept occ)
      ruleName' = case D.ruleName rule of
        Just n -> RuleName n
        Nothing -> RuleName "rule_anon" -- should not happen for propagation rules
        -- History IDs: ordered by position in the combined head list
      historyIds = buildHistoryIds occ
      -- Kill removed constraints
      killStmts = genKillStmts occ
      -- Body goals
      bodyStmts = compileBodyGoals symTab varMap (D.ruleBody rule)
      -- Early drop check after body
      earlyDropStmts
        | activeIsRemoved = [Return (Lit (BoolLit True))]
        | otherwise = [If (Not (Alive (Var "id"))) [Return (Lit (BoolLit True))] []]
      -- Core fire sequence
      coreFireStmts = killStmts ++ bodyStmts ++ earlyDropStmts
   in if isPropagation
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

compileTerm :: Map.Map String Expr -> T.Term -> Expr
compileTerm varMap (T.VarTerm v) = case Map.lookup v varMap of
  Just expr -> expr
  Nothing -> error $ "Compile: unbound variable: " ++ v
compileTerm _ (T.IntTerm n) = Lit (IntLit n)
compileTerm _ (T.AtomTerm s) = Lit (AtomLit s)
compileTerm varMap (T.CompoundTerm name args) =
  MakeTerm (vmName name) (map (compileTerm varMap) args)
compileTerm _ T.Wildcard = Lit WildcardLit

-- ---------------------------------------------------------------------------
-- Compile guards
-- ---------------------------------------------------------------------------

compileGuard :: Map.Map String Expr -> D.Guard -> Expr
compileGuard _ (D.GuardCommon D.GoalTrue) = Lit (BoolLit True)
compileGuard _ (D.GuardCommon D.GoalFail) = Lit (BoolLit False)
compileGuard varMap (D.GuardEqual t1 t2) =
  Equal (compileTerm varMap t1) (compileTerm varMap t2)
compileGuard varMap (D.GuardHostCall f args) =
  HostCall (Name f) (map (compileTerm varMap) args)

-- | Combine guards into a single expression, or Nothing if all are trivially true.
compileGuards :: Map.Map String Expr -> [D.Guard] -> Maybe Expr
compileGuards varMap guards =
  let exprs = filter nonTrivialTrue (map (compileGuard varMap) guards)
   in case exprs of
        [] -> Nothing
        [e] -> Just e
        (e : es) -> Just (foldl' And e es)
  where
    nonTrivialTrue (Lit (BoolLit True)) = False
    nonTrivialTrue _ = True

-- ---------------------------------------------------------------------------
-- Compile body goals
-- ---------------------------------------------------------------------------

-- | Compile a list of body goals, threading the varMap so that variables
-- introduced by one goal (via ':=' or new constraint arguments) are visible
-- to all subsequent goals.
compileBodyGoals :: SymbolTable -> Map.Map String Expr -> [D.BodyGoal] -> [Stmt]
compileBodyGoals _ _ [] = []
compileBodyGoals symTab varMap (goal : rest) = case goal of
  D.BodyHostCall v f args ->
    let stmt = Let (Name v) (HostCall (Name f) (map (compileTerm varMap) args))
        varMap' = Map.insert v (Var (Name v)) varMap
     in stmt : compileBodyGoals symTab varMap' rest
  D.BodyConstraint con ->
    let argVars = [v | T.VarTerm v <- T.conArgs con, Map.notMember v varMap]
        newStmts = [Let (Name v) NewVar | v <- argVars]
        varMap' = foldl' (\m v -> Map.insert v (Var (Name v)) m) varMap argVars
        tellName = procNameFor "tell" (T.conName con)
        callArgs = map (compileTerm varMap') (T.conArgs con)
     in newStmts
          ++ [ExprStmt (CallExpr tellName callArgs)]
          ++ compileBodyGoals symTab varMap' rest
  _ ->
    compileBodyGoal symTab varMap goal ++ compileBodyGoals symTab varMap rest

compileBodyGoal :: SymbolTable -> Map.Map String Expr -> D.BodyGoal -> [Stmt]
compileBodyGoal _ _ (D.BodyCommon D.GoalTrue) = []
compileBodyGoal _ _ (D.BodyCommon D.GoalFail) = []
compileBodyGoal _ varMap (D.BodyConstraint con) =
  let tellName = procNameFor "tell" (T.conName con)
      args = map (compileTerm varMap) (T.conArgs con)
   in [ExprStmt (CallExpr tellName args)]
compileBodyGoal _ varMap (D.BodyUnify t1 t2) =
  [ ExprStmt (Unify (compileTerm varMap t1) (compileTerm varMap t2)),
    DrainReactivationQueue "rs" [ExprStmt (CallExpr "reactivate_dispatch" [Var "rs"])]
  ]
compileBodyGoal _ varMap (D.BodyHostStmt f args) =
  [ExprStmt (HostCall (Name f) (map (compileTerm varMap) args))]
compileBodyGoal _ varMap (D.BodyHostCall v f args) =
  [Let (Name v) (HostCall (Name f) (map (compileTerm varMap) args))]

-- ---------------------------------------------------------------------------
-- reactivate_dispatch
-- ---------------------------------------------------------------------------

genReactivateDispatch :: SymbolTable -> ArityMap -> Procedure
genReactivateDispatch symTab arityMap =
  let body = map genDispatchBranch (Map.toList symTab)
   in Procedure "reactivate_dispatch" ["susp"] body
  where
    genDispatchBranch (name, cType) =
      let arity = Map.findWithDefault 0 name arityMap
          argExtracts =
            [ Let (Name ("rx_" ++ show i)) (FieldGet (Var "susp") (FieldArg (ArgIndex i)))
            | i <- [0 .. arity - 1]
            ]
          activateCall =
            ExprStmt
              ( CallExpr
                  (procNameFor "activate" name)
                  (Var "susp" : [Var (Name ("rx_" ++ show i)) | i <- [0 .. arity - 1]])
              )
       in If
            (IsConstraintType (Var "susp") cType)
            (argExtracts ++ [activateCall])
            []

-- ---------------------------------------------------------------------------
-- Naming helpers
-- ---------------------------------------------------------------------------

procNameFor :: String -> T.Name -> Name
procNameFor prefix (T.Qualified m n) = Name (prefix ++ "_" ++ m ++ "_" ++ n)
procNameFor prefix (T.Unqualified n) = Name (prefix ++ "_" ++ n)

occProcName :: T.Name -> Int -> Name
occProcName name num =
  let Name base = procNameFor "occurrence" name
   in Name (base ++ "_" ++ show num)

vmName :: T.Name -> Name
vmName (T.Unqualified n) = Name n
vmName (T.Qualified m n) = Name (m ++ "_" ++ n)

argNames :: Int -> [Name]
argNames arity = [argName i | i <- [0 .. arity - 1]]

argName :: Int -> Name
argName i = Name ("X_" ++ show i)

partSuspName :: Int -> Name
partSuspName k = Name ("susp_" ++ show k)

partIdName :: Int -> Name
partIdName k = Name ("pId_" ++ show k)

partArgName :: Int -> Int -> Name
partArgName k j = Name ("pA" ++ show j ++ "_" ++ show k)
