{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}

-- | CHR-to-VM Compiler
--
-- Transforms a desugared CHR program into a VM program following the
-- basic compilation scheme from the paper (Section 5.2) with the
-- Early Drop and Backjumping optimizations (Section 5.3, Listing 8).
module YCHR.Compile
  ( CompileError (..),
    compile,
    funcProcName,
    procNameFor,
    tellProcName,
    activateProcName,
    occProcName,
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
      dispatch = genReactivateDispatch symTab
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
      -- Occurrences are ordered removed-first, right-to-left within each
      -- group, following the ωr refined operational semantics (paper §2.2,
      -- Fig. 2).  This ensures removed occurrences are tried before kept
      -- ones, and within each group the rightmost head constraint gets the
      -- lowest (earliest) occurrence number.
      orderedOccurrences =
        [(i, c, False) | (i, c) <- zip [HeadPosition 0 ..] (reverse removed)]
          ++ [(i, c, True) | (i, c) <- zip [HeadPosition (length removed) ..] (reverse kept)]
      ruleName' = case rule.name of
        Just n -> n
        Nothing -> "rule_" <> T.pack (show ruleIdx)
  for orderedOccurrences $ \(idx, con, isKept) ->
    mkOccurrence symTab rule ruleName' orderedOccurrences idx con isKept

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
      tellName = tellProcName name
      activateName = activateProcName name
   in Procedure
        tellName
        params
        [ Let "id" (CreateConstraint cType (map Var params)),
          Store (Var "id"),
          ExprStmt (CallExpr activateName [Var "id"])
        ]

-- ---------------------------------------------------------------------------
-- activate_c
-- ---------------------------------------------------------------------------

-- | Generate the @activate_c@ procedure.  Takes a single suspension
-- parameter, extracts the constraint arguments into local variables,
-- and tries each occurrence procedure in order (paper §5.2, Listing 2
-- with Early Drop from Listing 8).
genActivate :: Types.Name -> Arity -> [Occurrence] -> Procedure
genActivate name arity occs =
  let activateName = activateProcName name
      occParams = Name "id" : argNames arity
      argExtracts =
        [ Let (argName i) (FieldGet (Var "susp") (FieldArg (ArgIndex i)))
        | i <- [0 .. arity.unArity - 1]
        ]
      body =
        argExtracts
          ++ concatMap (genActivateCall occParams) occs
          ++ [Return (Lit (BoolLit False))]
   in Procedure activateName ["susp"] (Let "id" (Var "susp") : body)
  where
    genActivateCall occParams' occ =
      let occName = occProcName name occ.number
       in [ Let "d" (CallExpr occName (map Var occParams')),
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
  (matchWrapper, guardExpr, varMap') <- compileGuards funSet varMap guardSi guards
  fireStmts <- genFireStmts funSet symTab varMap' occ
  let inner = case guardExpr of
        Nothing -> fireStmts
        Just gExpr -> [If gExpr fireStmts []]
  pure (matchWrapper inner ++ [Return (Lit (BoolLit False))])

-- | Generate the nested partner iteration for a multi-head rule
-- (paper §5.2, Listing 1).  For each partner @k@ this produces:
--
-- @
-- Foreach Lk cType susp_k [] [
--   let pId_k  = susp_k.id
--   let pArg_… = susp_k.arg(…)
--   if pId_k ≠ id ∧ pId_k ≠ pId_0 ∧ … then
--     ‹recurse for partner k+1›
-- ]
-- @
--
-- When all partners have been bound (base case), the guard is checked
-- and 'genFireStmts' emits the rule firing code including early drop
-- and backjumping (paper §5.3).
genPartnerBody :: Set Types.Name -> SymbolTable -> VarMap -> Occurrence -> PartnerIndex -> Eff '[Writer [CompileError]] [Stmt]
genPartnerBody funSet symTab varMap occ k
  | k >= PartnerIndex (length occ.partners) = do
      let AnnP {node = guards, sourceLoc = guardLoc, parsed = guardP} = occ.rule.guard
          guardSi = (guardLoc, guardP)
      (matchWrapper, guardExpr, varMap') <- compileGuards funSet varMap guardSi guards
      fireStmts <- genFireStmts funSet symTab varMap' occ
      let inner = case guardExpr of
            Nothing -> fireStmts
            Just gExpr -> [If gExpr fireStmts []]
      pure (matchWrapper inner)
  | otherwise = do
      -- O(k) indexing; acceptable because partner lists are small
      -- (typically 1–3 elements for most CHR rules).
      let partner = occ.partners !! k.unPartnerIndex
          label = Label ("L" <> T.pack (show (k.unPartnerIndex + 1)))
          suspVar = partSuspName k
          partArity = length partner.constraint.args
          fieldExtracts =
            Let (partIdName k) (FieldGet (Var suspVar) FieldId)
              : [ Let (partArgName k j) (FieldGet (Var suspVar) (FieldArg (ArgIndex j)))
                | j <- [0 .. partArity - 1]
                ]
          -- No alive checks here: the Foreach iterator guarantees that
          -- yielded partners are alive, and the active constraint's
          -- liveness is verified after body execution (early drop /
          -- backjumping in genFireStmts).
          distinctActive = Not (IdEqual (Var (partIdName k)) (Var "id"))
          distinctEarlier =
            [ Not (IdEqual (Var (partIdName k)) (Var (partIdName j)))
            | j <- [PartnerIndex 0 .. k - 1]
            ]
          distinctAll = foldl' And distinctActive distinctEarlier
      innerBody <- genPartnerBody funSet symTab varMap occ (k + 1)
      let innerWithDistinct = [If distinctAll innerBody []]
          foreachBody = fieldExtracts ++ innerWithDistinct
      pure [Foreach label partner.cType suspVar [] foreachBody]

-- ---------------------------------------------------------------------------
-- Fire: history check + kill + body + early drop + backjumping
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
      -- Backjumping (paper §5.3): after body execution, check each
      -- partner's liveness outermost-first.  If a partner died (e.g.
      -- killed by a rule fired during body execution), Continue to its
      -- Foreach loop to skip useless inner iterations.
      --
      -- Removed partners are omitted: they were explicitly killed by
      -- killStmts above, so they are guaranteed dead and the check
      -- would always succeed.  The outermost removed partner's Continue
      -- would be unconditional, making all subsequent checks unreachable
      -- (paper §5.3, "all following alive tests thus becomes redundant").
      --
      -- When activeIsRemoved the early drop is an unconditional Return,
      -- so backjumps are unreachable.
      backjumpStmts
        | activeIsRemoved = []
        | otherwise =
            [ If
                (Not (Alive (Var (partIdName k))))
                [Continue (Label ("L" <> T.pack (show (k.unPartnerIndex + 1))))]
                []
            | (k, p) <- zip [PartnerIndex 0 ..] occ.partners,
              p.isKept
            ]
      coreFireStmts = killStmts ++ bodyStmts ++ earlyDropStmts ++ backjumpStmts
  pure $
    if isPropagation
      then
        [ If
            (NotInHistory ruleName' historyIds)
            (AddHistory ruleName' historyIds : coreFireStmts)
            []
        ]
      else coreFireStmts

-- | Collect constraint identifiers for the propagation history tuple.
-- IDs are sorted by head position so that the same rule with the same
-- partner combination always produces an identical tuple regardless of
-- which occurrence is active (paper §5.2, Listing 1, line 14).
buildHistoryIds :: Occurrence -> [Expr]
buildHistoryIds occ =
  let allPositions =
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

-- | Compile a guard conjunction.  Guards are split into two groups:
--
--   * __Match guards__ ('GuardMatch', 'GuardGetArg') introduce new
--     variable bindings and structural checks.  They are compiled into
--     a wrapper @[Stmt] -> [Stmt]@ that nests the inner code inside
--     conditionals and let-bindings.  Match guards must be processed
--     first so that the variables they bind are in scope for check
--     guards.
--
--   * __Check guards__ ('GuardEqual', 'GuardExpr') are pure boolean
--     tests.  They are compiled into a single 'And'-chained expression.
compileGuards ::
  Set Types.Name ->
  VarMap ->
  SrcInfo ->
  [D.Guard] ->
  Eff '[Writer [CompileError]] ([Stmt] -> [Stmt], Maybe Expr, VarMap)
compileGuards funSet varMap si guards = do
  let (matchGuards, checkGuards) = partition isMatchGuard guards
  (matchWrapper, varMap') <- foldM (compileMatchGuard si) (id, varMap) matchGuards
  checkExpr <- compileCheckGuards funSet varMap' si checkGuards
  pure (matchWrapper, checkExpr, varMap')
  where
    isMatchGuard (D.GuardMatch {}) = True
    isMatchGuard (D.GuardGetArg {}) = True
    isMatchGuard _ = False

compileMatchGuard ::
  SrcInfo ->
  ([Stmt] -> [Stmt], VarMap) ->
  D.Guard ->
  Eff '[Writer [CompileError]] ([Stmt] -> [Stmt], VarMap)
compileMatchGuard si (matchWrapper, varMap) (D.GuardMatch term name arity) = do
  termExpr <- compileTerm varMap si term
  let check body = [If (MatchTerm termExpr (vmName name) arity) body []]
  pure (matchWrapper . check, varMap)
compileMatchGuard si (matchWrapper, varMap) (D.GuardGetArg vname term idx) = do
  termExpr <- compileTerm varMap si term
  let binding body = Let (Name vname) (GetArg termExpr idx) : body
      varMap' = insertVar vname (Var (Name vname)) varMap
  pure (matchWrapper . binding, varMap')
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
compileBodyGoals funSet symTab varMap si goals = do
  (stmts, _) <- foldM step ([], varMap) goals
  pure stmts
  where
    step (acc, vm) goal = do
      (stmts, vm') <- compileBodyGoal funSet symTab vm si goal
      pure (acc ++ stmts, vm')

-- | Compile a single body goal, returning the generated statements and
-- an updated 'VarMap'. The VarMap may grow when a goal introduces new
-- variables (e.g. @is@ binding a fresh variable, or a constraint whose
-- arguments reference not-yet-seen variables that need 'NewVar').
compileBodyGoal :: Set Types.Name -> SymbolTable -> VarMap -> SrcInfo -> D.BodyGoal -> Eff '[Writer [CompileError]] ([Stmt], VarMap)
compileBodyGoal _ _ varMap _ (D.BodyCommon D.GoalTrue) = pure ([], varMap)
compileBodyGoal _ _ varMap si (D.BodyConstraint con) = do
  let argVars = [v | VarTerm v <- con.args, notMemberVar v varMap]
      newStmts = [Let (Name v) NewVar | v <- argVars]
      varMap' = foldl' (\m v -> insertVar v (Var (Name v)) m) varMap argVars
  callArgs <- traverse (compileTerm varMap' si) con.args
  let tellName = tellProcName con.name
  pure (newStmts ++ [ExprStmt (CallExpr tellName callArgs)], varMap')
compileBodyGoal _ _ varMap si (D.BodyUnify t1 t2) = do
  t1' <- compileTerm varMap si t1
  t2' <- compileTerm varMap si t2
  pure
    ( [ ExprStmt (Unify t1' t2'),
        DrainReactivationQueue "rs" [ExprStmt (CallExpr "reactivate_dispatch" [Var "rs"])]
      ],
      varMap
    )
compileBodyGoal _ _ varMap si (D.BodyHostStmt f args) = do
  args' <- traverse (compileTerm varMap si) args
  pure ([ExprStmt (HostCall (Name f) args')], varMap)
compileBodyGoal funSet _ varMap si (D.BodyIs v expr) = do
  expr' <- compileExpr funSet varMap si expr
  case lookupVar v varMap of
    Just existing ->
      pure
        ( [ ExprStmt (Unify existing (HostEval expr')),
            DrainReactivationQueue "rs" [ExprStmt (CallExpr "reactivate_dispatch" [Var "rs"])]
          ],
          varMap
        )
    Nothing ->
      let varMap' = insertVar v (Var (Name v)) varMap
       in pure ([Let (Name v) (HostEval expr')], varMap')
compileBodyGoal funSet _ varMap si (D.BodyFunctionCall name args) = do
  args' <- traverse (compileExpr funSet varMap si) args
  pure ([ExprStmt (CallExpr (funcProcName name) args')], varMap)

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
  (matchWrapper, guardExpr, varMap') <- compileGuards funSet varMap si eq.guards
  rhsExpr <- compileExpr funSet varMap' si eq.rhs
  let returnStmt = [Return rhsExpr]
      inner = case guardExpr of
        Nothing -> returnStmt
        Just gExpr -> [If gExpr returnStmt []]
  pure (matchWrapper inner)

-- ---------------------------------------------------------------------------
-- reactivate_dispatch
-- ---------------------------------------------------------------------------

-- | Dispatch reactivation by constraint type.  Generates a linear
-- if-chain over all constraint types.  Each branch simply calls the
-- appropriate @activate_c@ with the suspension; argument extraction
-- is handled inside @activate_c@ itself.
--
-- The if-chain is inherent to the VM's instruction set (no
-- switch\/dispatch instruction); backends may optimize this to a
-- table dispatch or similar.
genReactivateDispatch :: SymbolTable -> Procedure
genReactivateDispatch symTab =
  let body = map genDispatchBranch (symbolTableToList symTab)
   in Procedure "reactivate_dispatch" ["susp"] body
  where
    genDispatchBranch (name, cType) =
      If
        (IsConstraintType (Var "susp") cType)
        [ExprStmt (CallExpr (activateProcName name) [Var "susp"])]
        []

-- ---------------------------------------------------------------------------
-- Naming helpers
-- ---------------------------------------------------------------------------

procNameFor :: Text -> Types.Name -> Name
procNameFor prefix (Types.Qualified m n) = Name (prefix <> "_" <> m <> "_" <> n)
procNameFor prefix (Types.Unqualified n) = Name (prefix <> "_" <> n)

tellProcName :: Types.Name -> Name
tellProcName = procNameFor "tell"

activateProcName :: Types.Name -> Name
activateProcName = procNameFor "activate"

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

-- | VM variable name for the @j@-th argument of partner @k@: @pArg_k_j@.
partArgName :: PartnerIndex -> Int -> Name
partArgName k j = Name ("pArg_" <> T.pack (show k.unPartnerIndex) <> "_" <> T.pack (show j))
