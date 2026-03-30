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
    funcProcName,
    procNameFor,
  )
where

import Control.Monad (foldM)
import Data.List (partition)
import Data.Map.Strict qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as T
import Data.Traversable (for)
import Effectful (Eff, runPureEff)
import Effectful.Writer.Static.Local (Writer, runWriter, tell)
import YCHR.Compile.Types
import YCHR.Desugared qualified as D
import YCHR.Parsed qualified as P
import YCHR.Pretty (AnnP (..), PrettyE (..))
import YCHR.Types (Constraint, SymbolTable, Term (..), lookupSymbol, symbolTableSize, symbolTableToList)
import YCHR.Types qualified as Types
import YCHR.VM

data CompileError
  = UnknownConstraintType P.SourceLoc PrettyE Types.Name
  | UnboundVariable P.SourceLoc PrettyE Text
  deriving (Show)

-- | Source location and pretty-printable origin, extracted from an 'AnnP' wrapper.
type SrcInfo = (P.SourceLoc, PrettyE)

-- ---------------------------------------------------------------------------
-- Public API
-- ---------------------------------------------------------------------------

compile :: D.Program -> SymbolTable -> Either [CompileError] Program
compile prog symTab =
  let funSet = buildFunctionSet prog
      arityMap = buildArityMap prog
      (occMap, occErrs) = runPureEff . runWriter $ collectOccurrences symTab prog
      (procs, procErrs) = runPureEff . runWriter $ do
        fmap concat $ traverse (genConstraintProcs funSet symTab arityMap occMap) (symbolTableToList symTab)
      (funProcs, funErrs) = runPureEff . runWriter $ do
        traverse (compileFunctionDef funSet) prog.functions
      dispatch = genReactivateDispatch symTab arityMap
      allErrs = occErrs ++ procErrs ++ funErrs
   in if null allErrs
        then
          Right
            Program
              { numTypes = symbolTableSize symTab,
                procedures = procs ++ funProcs ++ [dispatch]
              }
        else Left allErrs

-- | Build the set of qualified function names from the program.
buildFunctionSet :: D.Program -> Set Types.Name
buildFunctionSet prog = Set.fromList [f.name | f <- prog.functions]

-- | Compute the VM procedure name for a function.
funcProcName :: Types.Name -> Name
funcProcName (Types.Qualified m n) = Name ("func_" <> m <> "_" <> n)
funcProcName (Types.Unqualified n) = Name ("func_" <> n)

-- ---------------------------------------------------------------------------
-- Arity map
-- ---------------------------------------------------------------------------

buildArityMap :: D.Program -> ArityMap
buildArityMap prog =
  let rules = prog.rules
   in arityMapFromList
        [ (c.name, Arity (length c.args))
        | r <- rules,
          let AnnP {node = rHead} = r.head
              AnnP {node = rBody} = r.body,
          c <-
            rHead.kept
              ++ rHead.removed
              ++ [c' | D.BodyConstraint c' <- rBody]
        ]

-- ---------------------------------------------------------------------------
-- Occurrence collection
-- ---------------------------------------------------------------------------

collectOccurrences :: SymbolTable -> D.Program -> Eff '[Writer [CompileError]] OccurrenceMap
collectOccurrences symTab prog = do
  let rules = prog.rules
  allOccs <- fmap concat (traverse (ruleOccurrences symTab) (zip [0 ..] rules))
  let grouped = foldl' (\m occ -> occMapAppend occ.conName occ m) occMapEmpty allOccs
  pure (occMapMap (assignNumbers . reverse) grouped)
  where
    assignNumbers occs = zipWith (\n o -> o {number = n}) [OccurrenceNumber 1 ..] occs

ruleOccurrences :: SymbolTable -> (Int, D.Rule) -> Eff '[Writer [CompileError]] [Occurrence]
ruleOccurrences symTab (ruleIdx, rule) = do
  let AnnP {node = ruleHead} = rule.head
      kept = ruleHead.kept
      removed = ruleHead.removed
      combined =
        [(i, c, False) | (i, c) <- zip [HeadPosition 0 ..] removed]
          ++ [(i, c, True) | (i, c) <- zip [HeadPosition (length removed) ..] (reverse kept)]
      ruleName' = case rule.name of
        Just n -> n
        Nothing -> "rule_" <> T.pack (show ruleIdx)
  for combined $ \(idx, con, isKept) ->
    mkOccurrence symTab rule ruleName' combined idx con isKept

mkOccurrence ::
  SymbolTable ->
  D.Rule ->
  Text ->
  [(HeadPosition, Constraint, Bool)] ->
  HeadPosition ->
  Constraint ->
  Bool ->
  Eff '[Writer [CompileError]] Occurrence
mkOccurrence symTab rule _ruleName combined activeIdx activeCon activeIsKept = do
  let partners' = [(idx, con, isKept) | (idx, con, isKept) <- combined, idx /= activeIdx]
      headSi = (rule.head.sourceLoc, rule.head.parsed)
  partners <- for partners' $ \(idx, con, isKept) -> do
    ct <- lookupCType symTab headSi con.name
    pure
      Partner
        { idx = idx,
          constraint = con,
          isKept = isKept,
          cType = ct
        }
  pure
    Occurrence
      { conName = activeCon.name,
        number = OccurrenceNumber 0,
        rule = rule,
        activeIdx = activeIdx,
        isKept = activeIsKept,
        activeArgs = activeCon.args,
        partners = partners
      }

lookupCType :: SymbolTable -> SrcInfo -> Types.Name -> Eff '[Writer [CompileError]] ConstraintType
lookupCType symTab (loc, p) name = case lookupSymbol name symTab of
  Just ct -> pure ct
  Nothing -> do
    tell [UnknownConstraintType loc p name]
    pure (ConstraintType (-1))

-- ---------------------------------------------------------------------------
-- Procedure generation for each constraint type
-- ---------------------------------------------------------------------------

genConstraintProcs :: Set Types.Name -> SymbolTable -> ArityMap -> OccurrenceMap -> (Types.Name, ConstraintType) -> Eff '[Writer [CompileError]] [Procedure]
genConstraintProcs funSet symTab arityMap occMap (name, cType) = do
  let arity = lookupArity name arityMap
      occs = lookupOccurrences name occMap
      tellProc = genTell name cType arity
      activate = genActivate name arity occs
  occProcs <- traverse (genOccurrence funSet symTab name arity) occs
  pure (tellProc : activate : occProcs)

-- ---------------------------------------------------------------------------
-- tell_c
-- ---------------------------------------------------------------------------

genTell :: Types.Name -> ConstraintType -> Arity -> Procedure
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

genActivate :: Types.Name -> Arity -> [Occurrence] -> Procedure
genActivate name arity occs =
  let params = Name "id" : argNames arity
      activateName = procNameFor "activate" name
      body = concatMap (genActivateCall params) occs ++ [Return (Lit (BoolLit False))]
   in Procedure activateName params body
  where
    genActivateCall params' occ =
      let occName = occProcName name occ.number
       in [ Let "d" (CallExpr occName (map Var params')),
            If (Var "d") [Return (Lit (BoolLit True))] []
          ]

-- ---------------------------------------------------------------------------
-- occurrence_c_j
-- ---------------------------------------------------------------------------

genOccurrence :: Set Types.Name -> SymbolTable -> Types.Name -> Arity -> Occurrence -> Eff '[Writer [CompileError]] Procedure
genOccurrence funSet symTab name arity occ = do
  let params = Name "id" : argNames arity
      procName' = occProcName name occ.number
      varMap = buildVarMap occ
  body <- genOccurrenceBody funSet symTab varMap occ
  pure (Procedure procName' params body)

buildVarMap :: Occurrence -> VarMap
buildVarMap occ =
  let activeBindings =
        [ (v, Var (argName i))
        | (i, VarTerm v) <- zip [0 ..] occ.activeArgs
        ]
      partnerBindings =
        [ (v, Var (partArgName k j))
        | (k, partner) <- zip [PartnerIndex 0 ..] occ.partners,
          (j, VarTerm v) <- zip [0 ..] partner.constraint.args
        ]
   in varMapFromList (activeBindings ++ partnerBindings)

genOccurrenceBody :: Set Types.Name -> SymbolTable -> VarMap -> Occurrence -> Eff '[Writer [CompileError]] [Stmt]
genOccurrenceBody funSet symTab varMap occ
  | null occ.partners = genNoPartnerBody funSet symTab varMap occ
  | otherwise = do
      body <- genPartnerBody funSet symTab varMap occ (PartnerIndex 0)
      pure (body ++ [Return (Lit (BoolLit False))])

-- Single-head rule (no partners)
genNoPartnerBody :: Set Types.Name -> SymbolTable -> VarMap -> Occurrence -> Eff '[Writer [CompileError]] [Stmt]
genNoPartnerBody funSet symTab varMap occ = do
  let AnnP {node = guards, sourceLoc = guardLoc, parsed = guardP} = occ.rule.guard
      guardSi = (guardLoc, guardP)
  (wrapper, guardExpr, varMap') <- compileGuards funSet varMap guardSi guards
  fireStmts <- genFireStmts funSet symTab varMap' occ
  let inner = case guardExpr of
        Nothing -> fireStmts
        Just gExpr -> [If gExpr fireStmts []]
  pure (wrapper inner ++ [Return (Lit (BoolLit False))])

-- Multi-head rule with partners
genPartnerBody :: Set Types.Name -> SymbolTable -> VarMap -> Occurrence -> PartnerIndex -> Eff '[Writer [CompileError]] [Stmt]
genPartnerBody funSet symTab varMap occ k
  | k >= PartnerIndex (length occ.partners) = do
      let AnnP {node = guards, sourceLoc = guardLoc, parsed = guardP} = occ.rule.guard
          guardSi = (guardLoc, guardP)
      (wrapper, guardExpr, varMap') <- compileGuards funSet varMap guardSi guards
      fireStmts <- genFireStmts funSet symTab varMap' occ
      let inner = case guardExpr of
            Nothing -> fireStmts
            Just gExpr -> [If gExpr fireStmts []]
      pure (wrapper inner)
  | otherwise = do
      let partner = occ.partners !! k.unPartnerIndex
          label = Label ("L" <> T.pack (show (k.unPartnerIndex + 1)))
          suspVar = partSuspName k
          partArity = length partner.constraint.args
          fieldExtracts =
            Let (partIdName k) (FieldGet (Var suspVar) FieldId)
              : [ Let (partArgName k j) (FieldGet (Var suspVar) (FieldArg (ArgIndex j)))
                | j <- [0 .. partArity - 1]
                ]
          aliveCheck = And (Alive (Var "id")) (Alive (Var (partIdName k)))
          distinctActive = Not (IdEqual (Var (partIdName k)) (Var "id"))
          distinctEarlier =
            [ Not (IdEqual (Var (partIdName k)) (Var (partIdName j)))
            | j <- [PartnerIndex 0 .. k - 1]
            ]
          distinctAll = foldl' And distinctActive distinctEarlier
      innerBody <- genPartnerBody funSet symTab varMap occ (k + 1)
      let innerWithDistinct = [If distinctAll innerBody []]
          innerWithAlive = [If aliveCheck innerWithDistinct []]
          foreachBody = fieldExtracts ++ innerWithAlive
      pure [Foreach label partner.cType suspVar [] foreachBody]

-- ---------------------------------------------------------------------------
-- Fire: history check + kill + body + early drop
-- ---------------------------------------------------------------------------

genFireStmts :: Set Types.Name -> SymbolTable -> VarMap -> Occurrence -> Eff '[Writer [CompileError]] [Stmt]
genFireStmts funSet symTab varMap occ = do
  let rule = occ.rule
      AnnP {node = ruleHead} = rule.head
      isPropagation = null ruleHead.removed
      activeIsRemoved = not occ.isKept
      ruleName' = case rule.name of
        Just n -> RuleName n
        Nothing -> RuleName "rule_anon"
      historyIds = buildHistoryIds occ
      killStmts = genKillStmts occ
  let AnnP {node = ruleBody, sourceLoc = bodyLoc, parsed = bodyP} = rule.body
      bodySi = (bodyLoc, bodyP)
  bodyStmts <- compileBodyGoals funSet symTab varMap bodySi ruleBody
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
        (occ.activeIdx, Var "id")
          : [ (p.idx, Var (partIdName k))
            | (k, p) <- zip [PartnerIndex 0 ..] occ.partners
            ]
      sorted = map snd $ Map.toAscList $ Map.fromList allPositions
   in sorted

genKillStmts :: Occurrence -> [Stmt]
genKillStmts occ =
  let -- Kill removed partners
      partnerKills =
        [ Kill (Var (partIdName k))
        | (k, p) <- zip [PartnerIndex 0 ..] occ.partners,
          not p.isKept
        ]
      -- Kill active if removed
      activeKill = [Kill (Var "id") | not occ.isKept]
   in partnerKills ++ activeKill

-- ---------------------------------------------------------------------------
-- Compile terms
-- ---------------------------------------------------------------------------

compileTerm :: VarMap -> SrcInfo -> Term -> Eff '[Writer [CompileError]] Expr
compileTerm varMap (loc, p) (VarTerm v) = case lookupVar v varMap of
  Just expr -> pure expr
  Nothing -> do
    tell [UnboundVariable loc p v]
    pure (Lit WildcardLit)
compileTerm _ _ (IntTerm n) = pure (Lit (IntLit n))
compileTerm _ _ (AtomTerm s) = pure (Lit (AtomLit s))
compileTerm _ _ (TextTerm s) = pure (Lit (TextLit s))
compileTerm varMap si (CompoundTerm name args) = do
  args' <- traverse (compileTerm varMap si) args
  pure (MakeTerm (vmName name) args')
compileTerm _ _ Wildcard = pure (Lit WildcardLit)

-- | Like 'compileTerm', but also recognises function calls and emits
-- 'CallExpr' for them.
compileExpr :: Set Types.Name -> VarMap -> SrcInfo -> Term -> Eff '[Writer [CompileError]] Expr
compileExpr funSet varMap si (CompoundTerm name args)
  | Set.member name funSet = do
      args' <- traverse (compileExpr funSet varMap si) args
      pure (CallExpr (funcProcName name) args')
  | Types.Qualified "host" f <- name = do
      args' <- traverse (compileExpr funSet varMap si) args
      pure (HostCall (Name f) args')
compileExpr _ varMap si t = compileTerm varMap si t

-- ---------------------------------------------------------------------------
-- Compile guards
-- ---------------------------------------------------------------------------

compileGuards ::
  Set Types.Name ->
  VarMap ->
  SrcInfo ->
  [D.Guard] ->
  Eff '[Writer [CompileError]] ([Stmt] -> [Stmt], Maybe Expr, VarMap)
compileGuards funSet varMap si guards = do
  let (matchGuards, checkGuards) = partition isMatchGuard guards
  (wrapper, varMap') <- foldM (compileMatchGuard si) (id, varMap) matchGuards
  checkExpr <- compileCheckGuards funSet varMap' si checkGuards
  pure (wrapper, checkExpr, varMap')
  where
    isMatchGuard (D.GuardMatch {}) = True
    isMatchGuard (D.GuardGetArg {}) = True
    isMatchGuard _ = False

compileMatchGuard ::
  SrcInfo ->
  ([Stmt] -> [Stmt], VarMap) ->
  D.Guard ->
  Eff '[Writer [CompileError]] ([Stmt] -> [Stmt], VarMap)
compileMatchGuard si (wrapper, varMap) (D.GuardMatch term name arity) = do
  termExpr <- compileTerm varMap si term
  let check body = [If (MatchTerm termExpr (vmName name) arity) body []]
  pure (wrapper . check, varMap)
compileMatchGuard si (wrapper, varMap) (D.GuardGetArg vname term idx) = do
  termExpr <- compileTerm varMap si term
  let binding body = Let (Name vname) (GetArg termExpr idx) : body
      varMap' = insertVar vname (Var (Name vname)) varMap
  pure (wrapper . binding, varMap')
compileMatchGuard _ acc _ = pure acc

compileCheckGuards :: Set Types.Name -> VarMap -> SrcInfo -> [D.Guard] -> Eff '[Writer [CompileError]] (Maybe Expr)
compileCheckGuards funSet varMap si guards = case nonTrivialGuards of
  [] -> pure Nothing
  [g] -> Just <$> compileCheckGuard funSet varMap si g
  gs -> Just . foldl1 And <$> traverse (compileCheckGuard funSet varMap si) gs
  where
    nonTrivialGuards = filter isNonTrivial guards
    isNonTrivial (D.GuardCommon D.GoalTrue) = False
    isNonTrivial _ = True

compileCheckGuard :: Set Types.Name -> VarMap -> SrcInfo -> D.Guard -> Eff '[Writer [CompileError]] Expr
compileCheckGuard _ _ _ (D.GuardCommon D.GoalTrue) = pure (Lit (BoolLit True))
compileCheckGuard _ varMap si (D.GuardEqual t1 t2) = Equal <$> compileTerm varMap si t1 <*> compileTerm varMap si t2
compileCheckGuard funSet varMap si (D.GuardExpr term) = HostEval <$> compileExpr funSet varMap si term
compileCheckGuard _ _ _ _ = pure (Lit (BoolLit True))

-- ---------------------------------------------------------------------------
-- Compile body goals
-- ---------------------------------------------------------------------------

compileBodyGoals :: Set Types.Name -> SymbolTable -> VarMap -> SrcInfo -> [D.BodyGoal] -> Eff '[Writer [CompileError]] [Stmt]
compileBodyGoals _ _ _ _ [] = pure []
compileBodyGoals funSet symTab varMap si (goal : rest) = case goal of
  D.BodyIs v expr -> do
    expr' <- compileExpr funSet varMap si expr
    case lookupVar v varMap of
      Just existing -> do
        let stmts =
              [ ExprStmt (Unify existing (HostEval expr')),
                DrainReactivationQueue "rs" [ExprStmt (CallExpr "reactivate_dispatch" [Var "rs"])]
              ]
        rest' <- compileBodyGoals funSet symTab varMap si rest
        pure (stmts ++ rest')
      Nothing -> do
        let stmt = Let (Name v) (HostEval expr')
            varMap' = insertVar v (Var (Name v)) varMap
        rest' <- compileBodyGoals funSet symTab varMap' si rest
        pure (stmt : rest')
  D.BodyConstraint con -> do
    let argVars = [v | VarTerm v <- con.args, notMemberVar v varMap]
        newStmts = [Let (Name v) NewVar | v <- argVars]
        varMap' = foldl' (\m v -> insertVar v (Var (Name v)) m) varMap argVars
    callArgs <- traverse (compileTerm varMap' si) con.args
    let tellName = procNameFor "tell" con.name
    rest' <- compileBodyGoals funSet symTab varMap' si rest
    pure (newStmts ++ [ExprStmt (CallExpr tellName callArgs)] ++ rest')
  _ -> do
    goal' <- compileBodyGoal funSet symTab varMap si goal
    rest' <- compileBodyGoals funSet symTab varMap si rest
    pure (goal' ++ rest')

compileBodyGoal :: Set Types.Name -> SymbolTable -> VarMap -> SrcInfo -> D.BodyGoal -> Eff '[Writer [CompileError]] [Stmt]
compileBodyGoal _ _ _ _ (D.BodyCommon D.GoalTrue) = pure []
compileBodyGoal _ _ varMap si (D.BodyConstraint con) = do
  conArgs' <- traverse (compileTerm varMap si) con.args
  let tellName = procNameFor "tell" con.name
  pure [ExprStmt (CallExpr tellName conArgs')]
compileBodyGoal _ _ varMap si (D.BodyUnify t1 t2) = do
  t1' <- compileTerm varMap si t1
  t2' <- compileTerm varMap si t2
  pure
    [ ExprStmt (Unify t1' t2'),
      DrainReactivationQueue "rs" [ExprStmt (CallExpr "reactivate_dispatch" [Var "rs"])]
    ]
compileBodyGoal _ _ varMap si (D.BodyHostStmt f args) = do
  args' <- traverse (compileTerm varMap si) args
  pure [ExprStmt (HostCall (Name f) args')]
compileBodyGoal funSet _ varMap si (D.BodyIs v expr) = do
  expr' <- compileExpr funSet varMap si expr
  case lookupVar v varMap of
    Just existing ->
      pure
        [ ExprStmt (Unify existing (HostEval expr')),
          DrainReactivationQueue "rs" [ExprStmt (CallExpr "reactivate_dispatch" [Var "rs"])]
        ]
    Nothing -> pure [Let (Name v) (HostEval expr')]
compileBodyGoal funSet _ varMap si (D.BodyFunctionCall name args) = do
  args' <- traverse (compileExpr funSet varMap si) args
  pure [ExprStmt (CallExpr (funcProcName name) args')]

-- ---------------------------------------------------------------------------
-- Compile function definitions
-- ---------------------------------------------------------------------------

compileFunctionDef :: Set Types.Name -> D.Function -> Eff '[Writer [CompileError]] Procedure
compileFunctionDef funSet func = do
  let procName' = funcProcName func.name
      params = [Name ("arg_" <> T.pack (show i)) | i <- [0 .. func.arity - 1]]
      dummySi = (P.dummyLoc, PrettyE (AtomTerm "function"))
  eqStmts <- traverse (compileEquation funSet params dummySi) func.equations
  let errorStmt = ExprStmt (HostCall "__chr_error" [Lit (AtomLit "no_matching_equation")])
  pure (Procedure procName' params (concat eqStmts ++ [errorStmt]))

-- | Build a VarMap for a function equation: maps each normalized parameter
-- variable to the corresponding procedure parameter name.
buildEquationVarMap :: [Name] -> [Term] -> VarMap
buildEquationVarMap procParams normalizedArgs =
  varMapFromList
    [ (v, Var p)
    | (p, VarTerm v) <- zip procParams normalizedArgs
    ]

compileEquation :: Set Types.Name -> [Name] -> SrcInfo -> D.Equation -> Eff '[Writer [CompileError]] [Stmt]
compileEquation funSet params si eq = do
  let varMap = buildEquationVarMap params eq.params
  (wrapper, guardExpr, varMap') <- compileGuards funSet varMap si eq.guards
  rhsExpr <- compileExpr funSet varMap' si eq.rhs
  let returnStmt = [Return rhsExpr]
      inner = case guardExpr of
        Nothing -> returnStmt
        Just gExpr -> [If gExpr returnStmt []]
  pure (wrapper inner)

-- ---------------------------------------------------------------------------
-- reactivate_dispatch
-- ---------------------------------------------------------------------------

genReactivateDispatch :: SymbolTable -> ArityMap -> Procedure
genReactivateDispatch symTab arityMap =
  let body = map genDispatchBranch (symbolTableToList symTab)
   in Procedure "reactivate_dispatch" ["susp"] body
  where
    genDispatchBranch (name, cType) =
      let arity = lookupArity name arityMap
          argExtracts =
            [ Let (Name ("rx_" <> T.pack (show i))) (FieldGet (Var "susp") (FieldArg (ArgIndex i)))
            | i <- [0 .. arity.unArity - 1]
            ]
          activateCall =
            ExprStmt
              ( CallExpr
                  (procNameFor "activate" name)
                  (Var "susp" : [Var (Name ("rx_" <> T.pack (show i))) | i <- [0 .. arity.unArity - 1]])
              )
       in If
            (IsConstraintType (Var "susp") cType)
            (argExtracts ++ [activateCall])
            []

-- ---------------------------------------------------------------------------
-- Naming helpers
-- ---------------------------------------------------------------------------

procNameFor :: Text -> Types.Name -> Name
procNameFor prefix (Types.Qualified m n) = Name (prefix <> "_" <> m <> "_" <> n)
procNameFor prefix (Types.Unqualified n) = Name (prefix <> "_" <> n)

occProcName :: Types.Name -> OccurrenceNumber -> Name
occProcName name num =
  let Name base = procNameFor "occurrence" name
   in Name (base <> "_" <> T.pack (show num.unOccurrenceNumber))

vmName :: Types.Name -> Name
vmName (Types.Unqualified n) = Name n
vmName (Types.Qualified m n) = Name (m <> "_" <> n)

argNames :: Arity -> [Name]
argNames arity = [argName i | i <- [0 .. arity.unArity - 1]]

argName :: Int -> Name
argName i = Name ("X_" <> T.pack (show i))

partSuspName :: PartnerIndex -> Name
partSuspName k = Name ("susp_" <> T.pack (show k.unPartnerIndex))

partIdName :: PartnerIndex -> Name
partIdName k = Name ("pId_" <> T.pack (show k.unPartnerIndex))

partArgName :: PartnerIndex -> Int -> Name
partArgName k j = Name ("pA" <> T.pack (show j) <> "_" <> T.pack (show k.unPartnerIndex))
