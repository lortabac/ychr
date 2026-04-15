{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}

-- |
-- Module      : YCHR.Compile
-- Description : Transforms a desugared CHR program into a VM program.
--
-- The Compiler is the transformation pass between the desugared
-- 'YCHR.Desugared.Program' and the abstract 'YCHR.VM.Program' consumed by
-- the backends and the interpreter. It performs, in order:
--
-- 1. /Occurrence collection/: 'collectOccurrences' walks every rule head
--    and produces, for each constraint type, a top-down list of
--    'Occurrence' records numbered as required by the refined operational
--    semantics (paper §2.2, Fig. 2).
--
-- 2. /Per-constraint procedure generation/: for each entry in the symbol
--    table 'genConstraintProcs' emits a @tell_c@, an @activate_c@, and one
--    @occurrence_c_j@ procedure per occurrence (paper §5.2, Listings 1
--    and 2).
--
-- 3. /Function compilation/: 'compileFunctionDef' emits one VM procedure
--    per user-defined function, with equations tried in source order.
--
-- 4. /Reactivation dispatch/: 'genReactivateDispatch' emits a single
--    @reactivate_dispatch@ procedure that selects the right @activate_c@
--    based on a suspension's constraint type (paper §5.3, "Selective
--    Constraint Reactivation").
--
-- 5. /@call@ dispatch/: 'genCallFunDispatches' emits one
--    @call_N@ procedure per supported call arity to dispatch first-class
--    function values (function references and lifted lambda closures).
--
-- The basic compilation scheme is from paper §5.2; the Early Drop and
-- Backjumping optimizations are from §5.3 (Listing 8). Selective
-- Constraint Reactivation is implemented at the runtime level (the
-- observer pattern in 'YCHR.Runtime.Reactivation') — this pass only emits
-- 'DrainReactivationQueue' calls after each tell-side @Unify@.
--
-- Non-obvious design choices are documented in the \"Notes\" block at the
-- bottom of this file.
module YCHR.Compile
  ( CompileError (..),
    compile,
    compileFunctionDef,
    genCallFunDispatches,
    buildFunctionSet,

    -- * Re-exported name builders (see "YCHR.Compile.Names")
    funcProcName,
    vmName,
    procNameFor,
    tellProcName,
    activateProcName,
    occProcName,
  )
where

import Control.Monad (foldM)
import Data.List (partition, sortOn)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as T
import Effectful (Eff, runPureEff)
import Effectful.Writer.Static.Local (Writer, runWriter, tell)
import YCHR.Compile.Names
import YCHR.Compile.Occurrences (collectOccurrences)
import YCHR.Compile.Types
import YCHR.Desugared qualified as D
import YCHR.Loc (SourceLoc)
import YCHR.PExpr (PExpr)
import YCHR.Parsed (AnnP (..))
import YCHR.Parsed qualified as P
import YCHR.Pretty (prettyPExprSrc)
import YCHR.Types (Identifier (..), SymbolTable, Term (..), flattenName, symbolTableSize, symbolTableToList)
import YCHR.Types qualified as Types
import YCHR.VM

-- | Source location and original parsed expression, extracted from an 'AnnP' wrapper.
type SrcInfo = (P.SourceLoc, PExpr)

-- ---------------------------------------------------------------------------
-- Public API
-- ---------------------------------------------------------------------------

-- | Compile a desugared program against the given constraint-type symbol
-- table. Returns 'Right' a 'YCHR.VM.Program' on success, or 'Left' the
-- accumulated errors. Errors from every sub-pass are collected before
-- the function decides to fail, so callers see as much detail as
-- possible in one go.
compile :: D.Program -> SymbolTable -> Either [AnnP CompileError] Program
compile prog symTab =
  let funSet = buildFunctionSet prog
      (occMap, occErrs) = runPureEff . runWriter $ collectOccurrences symTab prog
      (procs, procErrs) = runPureEff . runWriter $ do
        fmap concat $ traverse (genConstraintProcs funSet symTab occMap) (symbolTableToList symTab)
      (funProcs, funErrs) = runPureEff . runWriter $ do
        traverse (compileFunctionDef funSet) prog.functions
      dispatch = genReactivateDispatch symTab
      callFunDispatches = genCallFunDispatches prog.functions
      allErrs = occErrs ++ procErrs ++ funErrs
   in if null allErrs
        then
          Right
            Program
              { numTypes = symbolTableSize symTab,
                typeNames = buildTypeNames symTab,
                procedures = procs ++ funProcs ++ [dispatch] ++ callFunDispatches
              }
        else Left allErrs

-- | Build the set of qualified function identifiers from the program.
buildFunctionSet :: D.Program -> Set Identifier
buildFunctionSet prog = Set.fromList [Identifier f.name f.arity | f <- prog.functions]

-- | Build the list of constraint type source names, indexed by
-- 'Types.ConstraintType'. The list is ordered by the constraint type's
-- integer index, so @typeNames !! i@ is the name of the type with index @i@.
-- Qualified names are flattened via 'flattenName'.
buildTypeNames :: SymbolTable -> [Text]
buildTypeNames symTab =
  [ flattenName ident.name
  | (ident, _) <- sortOn (ctIndex . snd) (symbolTableToList symTab)
  ]
  where
    ctIndex (Types.ConstraintType i) = i

-- ---------------------------------------------------------------------------
-- Procedure generation for each constraint type
-- ---------------------------------------------------------------------------

genConstraintProcs :: Set Identifier -> SymbolTable -> OccurrenceMap -> (Identifier, ConstraintType) -> Eff '[Writer [AnnP CompileError]] [Procedure]
genConstraintProcs funSet symTab occMap (ident, cType) = do
  let occs = lookupOccurrences ident occMap
      tellProc = genTell ident.name cType ident.arity
      activate = genActivate ident.name ident.arity occs
  occProcs <- traverse (genOccurrence funSet symTab ident.name ident.arity) occs
  pure (tellProc : activate : occProcs)

-- ---------------------------------------------------------------------------
-- tell_c
-- ---------------------------------------------------------------------------

genTell :: Types.Name -> ConstraintType -> Int -> Procedure
genTell name cType arity =
  let params = argNames arity
      tellName = tellProcName name arity
      activateName = activateProcName name arity
   in Procedure
        tellName
        params
        [ Let activeName (CreateConstraint cType (map Var params)),
          Store (Var activeName),
          ExprStmt (CallExpr activateName [Var activeName])
        ]

-- ---------------------------------------------------------------------------
-- activate_c
-- ---------------------------------------------------------------------------

-- | Generate the @activate_c@ procedure. Takes the active constraint as
-- its single parameter, extracts the constraint arguments into local
-- variables, and tries each occurrence procedure in order (paper §5.2,
-- Listing 2 with Early Drop from Listing 8).
genActivate :: Types.Name -> Int -> [Occurrence] -> Procedure
genActivate name arity occs =
  let activateName = activateProcName name arity
      occParams = activeName : argNames arity
      argExtracts =
        [ Let (argName i) (FieldGet (Var activeName) (FieldArg (ArgIndex i)))
        | i <- [0 .. arity - 1]
        ]
      body =
        argExtracts
          ++ concatMap (genActivateCall occParams) occs
          ++ [Return (Lit (BoolLit False))]
   in Procedure activateName [activeName] body
  where
    genActivateCall occParams' occ =
      let occName = occProcName name arity occ.number
       in [ Let dropResultName (CallExpr occName (map Var occParams')),
            If (Var dropResultName) [Return (Lit (BoolLit True))] []
          ]

-- ---------------------------------------------------------------------------
-- occurrence_c_j
-- ---------------------------------------------------------------------------

genOccurrence :: Set Identifier -> SymbolTable -> Types.Name -> Int -> Occurrence -> Eff '[Writer [AnnP CompileError]] Procedure
genOccurrence funSet symTab name arity occ = do
  let params = activeName : argNames arity
      procName' = occProcName name arity occ.number
      varMap = buildVarMap occ
  body <- genOccurrenceBody funSet symTab varMap occ
  pure (Procedure procName' params body)

-- | Map every user-written head variable in an 'Occurrence' to the
-- generated VM variable that holds its value (an @X_i@ for the active
-- constraint, a @pArg_k_j@ for partner @k@). Non-variable arguments are
-- ignored: HNF guarantees that head arguments are either 'VarTerm' or
-- 'Wildcard', and wildcards are never referenced from guards or bodies.
-- See the \"Notes\" block at the bottom of this file.
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

-- | Compile the body of an occurrence procedure: build the innermost
-- "guards-then-fire" block, wrap it in one nested 'Foreach' per partner,
-- then append the trailing @Return false@ that signals "no early drop".
genOccurrenceBody :: Set Identifier -> SymbolTable -> VarMap -> Occurrence -> Eff '[Writer [AnnP CompileError]] [Stmt]
genOccurrenceBody funSet symTab varMap occ = do
  (inner, condMap) <- genGuardedFire funSet symTab varMap occ
  let body = wrapInPartnerLoops occ condMap inner
  pure (body ++ [Return (Lit (BoolLit False))])

-- | Compile the guards followed by the rule-firing block. Returns the
-- statements that go at the innermost partner-loop position — any HNF
-- match-guard wrappers (lets and structural @if@s introduced by
-- 'D.GuardMatch' / 'D.GuardGetArg') wrapped around the conditional
-- 'genFireStmts' result — together with the per-partner index
-- conditions lifted out of equality check guards by 'compileCheckGuards'.
genGuardedFire ::
  Set Identifier ->
  SymbolTable ->
  VarMap ->
  Occurrence ->
  Eff '[Writer [AnnP CompileError]] ([Stmt], PartnerCondMap)
genGuardedFire funSet symTab varMap occ = do
  let AnnP {node = guards, sourceLoc = guardLoc, parsed = guardP} = occ.rule.guard
      guardSi = (guardLoc, guardP)
  (matchWrapper, condMap, guardExpr, varMap') <- compileGuards funSet (Just occ) varMap guardSi guards
  fireStmts <- genFireStmts funSet symTab varMap' occ
  let guarded = case guardExpr of
        Nothing -> fireStmts
        Just gExpr -> [If gExpr fireStmts []]
  pure (matchWrapper guarded, condMap)

-- | Wrap a pre-built inner block in one nested 'Foreach' per partner
-- (paper §5.2, Listing 1). For each partner @k@ this produces:
--
-- @
-- Foreach Lk cType susp_k condsK [
--   let pId_k  = susp_k.id
--   let pArg_… = susp_k.arg(…)
--   if pId_k ≠ id ∧ pId_k ≠ pId_0 ∧ … then
--     ‹inner — possibly another Foreach for partner k+1›
-- ]
-- @
--
-- @condsK@ is the index-condition list lifted out of equality check
-- guards by 'compileCheckGuards' (paper §5.3, "Indexing"): the iterator
-- skips candidates whose argument values do not match without ever
-- entering the loop body.
--
-- When @occ@ has no partners the inner block is returned unchanged.
wrapInPartnerLoops :: Occurrence -> PartnerCondMap -> [Stmt] -> [Stmt]
wrapInPartnerLoops occ condMap inner =
  -- Loops are built innermost-first by folding from the right, so the
  -- partner with the highest index ends up as the innermost loop and
  -- partner 0 as the outermost — matching the source order of the head.
  foldr wrapOne inner (zip [PartnerIndex 0 ..] occ.partners)
  where
    wrapOne :: (PartnerIndex, Partner) -> [Stmt] -> [Stmt]
    wrapOne (k, partner) inside =
      let label = partLabel k
          suspVar = partSuspName k
          partArity = length partner.constraint.args
          conds = Map.findWithDefault [] k condMap
          -- Bind the partner's id and arguments as ordinary locals so
          -- the rest of the body can reference them by name.
          fieldExtracts =
            Let (partIdName k) (FieldGet (Var suspVar) FieldId)
              : [ Let (partArgName k j) (FieldGet (Var suspVar) (FieldArg (ArgIndex j)))
                | j <- [0 .. partArity - 1]
                ]
          -- The partner must be distinct from the active constraint and
          -- from every earlier partner: at most one suspension can play
          -- a given role in a rule firing. No alive checks here — the
          -- Foreach iterator guarantees yielded partners are alive, and
          -- the active constraint's liveness is verified after body
          -- execution (early drop / backjumping in 'genFireStmts').
          distinctActive = Not (IdEqual (Var (partIdName k)) (Var activeName))
          distinctEarlier =
            [ Not (IdEqual (Var (partIdName k)) (Var (partIdName j)))
            | j <- [PartnerIndex 0 .. k - 1]
            ]
          distinctAll = foldl' And distinctActive distinctEarlier
          guarded = [If distinctAll inside []]
       in [Foreach label partner.cType suspVar conds (fieldExtracts ++ guarded)]

-- ---------------------------------------------------------------------------
-- Fire: history check + kill + body + early drop + backjumping
-- ---------------------------------------------------------------------------

genFireStmts :: Set Identifier -> SymbolTable -> VarMap -> Occurrence -> Eff '[Writer [AnnP CompileError]] [Stmt]
genFireStmts funSet symTab varMap occ = do
  let rule = occ.rule
      AnnP {node = ruleHead} = rule.head
      isPropagation = null ruleHead.removed
      activeIsRemoved = not occ.isKept
      ruleName' = occ.ruleName
      historyIds = buildHistoryIds occ
      killStmts = genKillStmts occ
  let AnnP {node = ruleBody, sourceLoc = bodyLoc, parsed = bodyP} = rule.body
      bodySi = (bodyLoc, bodyP)
  bodyStmts <- compileBodyGoals funSet symTab varMap bodySi ruleBody
  let earlyDropStmts
        | activeIsRemoved = [Return (Lit (BoolLit True))]
        | otherwise = [If (Not (Alive (Var activeName))) [Return (Lit (BoolLit True))] []]
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
                [Continue (partLabel k)]
                []
            | (k, p) <- zip [PartnerIndex 0 ..] occ.partners,
              p.isKept
            ]
      annotation = mkRuleAnnotation occ
      coreFireStmts = PushAnnotation annotation : killStmts ++ bodyStmts ++ earlyDropStmts ++ backjumpStmts
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
  let positions =
        (occ.activeIdx, Var activeName)
          : [ (p.idx, Var (partIdName k))
            | (k, p) <- zip [PartnerIndex 0 ..] occ.partners
            ]
   in map snd (sortOn fst positions)

-- | Build a 'SourceAnnotation' for a rule firing.
mkRuleAnnotation :: Occurrence -> SourceAnnotation
mkRuleAnnotation occ =
  let label = "rule " <> occ.ruleName.unRuleName
   in mkAnnotation label occ.rule.head.sourceLoc occ.rule.head.parsed

-- | Build a 'SourceAnnotation' from a label, source location, and parsed expression.
mkAnnotation :: Text -> SourceLoc -> PExpr -> SourceAnnotation
mkAnnotation label loc pexpr =
  SourceAnnotation
    { annLabel = label,
      annSourceLoc = loc,
      annSourceCode = T.pack (prettyPExprSrc pexpr)
    }

genKillStmts :: Occurrence -> [Stmt]
genKillStmts occ =
  let -- Kill removed partners
      partnerKills =
        [ Kill (Var (partIdName k))
        | (k, p) <- zip [PartnerIndex 0 ..] occ.partners,
          not p.isKept
        ]
      -- Kill active if removed
      activeKill = [Kill (Var activeName) | not occ.isKept]
   in partnerKills ++ activeKill

-- ---------------------------------------------------------------------------
-- Compile terms
-- ---------------------------------------------------------------------------

compileTerm :: VarMap -> SrcInfo -> Term -> Eff '[Writer [AnnP CompileError]] Expr
compileTerm varMap (loc, p) (VarTerm v) = case lookupVar v varMap of
  Just expr -> pure expr
  Nothing -> do
    tell [AnnP (UnboundVariable v) loc p]
    pure (Lit WildcardLit)
compileTerm _ _ (IntTerm n) = pure (Lit (IntLit n))
compileTerm _ _ (AtomTerm "true") = pure (Lit (BoolLit True))
compileTerm _ _ (AtomTerm "false") = pure (Lit (BoolLit False))
compileTerm _ _ (AtomTerm s) = pure (Lit (AtomLit s))
compileTerm _ _ (TextTerm s) = pure (Lit (TextLit s))
compileTerm varMap si (CompoundTerm name args) = do
  args' <- traverse (compileTerm varMap si) args
  pure (MakeTerm (vmName name) args')
compileTerm _ _ Wildcard = pure (Lit WildcardLit)

-- | Like 'compileTerm', but also recognises @call@, user-defined
-- function calls and @host:f(...)@ at the top level of the term and
-- emits the appropriate 'CallExpr' \/ 'HostCall'. Recursion only happens
-- through these recognised forms; nested compound terms whose head is
-- /not/ a function are compiled as opaque data via 'compileTerm'. See
-- the \"Notes\" block at the bottom of this file.
compileExpr :: Set Identifier -> VarMap -> SrcInfo -> Term -> Eff '[Writer [AnnP CompileError]] Expr
compileExpr funSet varMap si (CompoundTerm (Types.Unqualified "call") args)
  | length args >= 2 = do
      args' <- traverse (compileExpr funSet varMap si) args
      pure (CallExpr (callFunProcName (length args - 1)) args')
compileExpr funSet varMap si (CompoundTerm name args)
  | Set.member (Identifier name (length args)) funSet = do
      args' <- traverse (compileExpr funSet varMap si) args
      pure (CallExpr (funcProcName name (length args')) args')
  | Types.Qualified "host" f <- name = do
      args' <- traverse (compileExpr funSet varMap si) args
      pure (HostCall (Name f) args')
compileExpr _ varMap si t = compileTerm varMap si t

-- ---------------------------------------------------------------------------
-- Compile guards
-- ---------------------------------------------------------------------------

-- | Per-partner index conditions lifted out of check guards by the
-- 'Foreach' index-condition pushdown optimization. Each entry maps a
-- partner index @k@ to the @[(ArgIndex, Expr)]@ list that becomes
-- 'YCHR.VM.Foreach' @k@'s index-conditions argument.
type PartnerCondMap = Map PartnerIndex [(ArgIndex, Expr)]

-- | Free 'Var' names occurring in an 'Expr'. Used by the index-condition
-- pushdown classifier to decide whether the non-partner-arg side of an
-- equality is referenceable at a partner loop's evaluation point.
freeVars :: Expr -> Set Name
freeVars = go
  where
    go (Var n) = Set.singleton n
    go (Lit _) = Set.empty
    go NewVar = Set.empty
    go (CallExpr _ es) = Set.unions (map go es)
    go (HostCall _ es) = Set.unions (map go es)
    go (EvalDeep e) = go e
    go (Not e) = go e
    go (And a b) = go a `Set.union` go b
    go (Or a b) = go a `Set.union` go b
    go (MakeTerm _ es) = Set.unions (map go es)
    go (MatchTerm e _ _) = go e
    go (GetArg e _) = go e
    go (CreateConstraint _ es) = Set.unions (map go es)
    go (Alive e) = go e
    go (IdEqual a b) = go a `Set.union` go b
    go (IsConstraintType e _) = go e
    go (NotInHistory _ es) = Set.unions (map go es)
    go (Unify a b) = go a `Set.union` go b
    go (Equal a b) = go a `Set.union` go b
    go (FieldGet e _) = go e

-- | Set of variable names visible at the moment partner @k@'s
-- 'YCHR.VM.Foreach' evaluates its index-condition expressions: the
-- active constraint's argument names, plus every earlier partner's
-- argument names. Match-guard 'Let' bindings are deliberately /not/
-- included — they live inside the innermost guard wrapper and are not
-- in scope at any 'Foreach' evaluation point.
inScopeBeforeLoop :: Occurrence -> PartnerIndex -> Set Name
inScopeBeforeLoop occ k =
  let activeNames = Set.fromList (argNames occ.conArity)
      earlierPartnerNames =
        Set.fromList
          [ partArgName k' j
          | (k', p) <- zip [PartnerIndex 0 ..] occ.partners,
            k' < k,
            j <- [0 .. length p.constraint.args - 1]
          ]
   in activeNames `Set.union` earlierPartnerNames

-- | Recognise an 'Expr' that is a reference to a partner argument
-- variable. The inverse of 'partArgName' for the partner indices and
-- arities present in @occ@.
asPartnerArg :: Occurrence -> Expr -> Maybe (PartnerIndex, ArgIndex)
asPartnerArg occ (Var n) = Map.lookup n partArgs
  where
    partArgs =
      Map.fromList
        [ (partArgName k j, (k, ArgIndex j))
        | (k, p) <- zip [PartnerIndex 0 ..] occ.partners,
          j <- [0 .. length p.constraint.args - 1]
        ]
asPartnerArg _ _ = Nothing

-- | Try to lift an @Equal a b@ check to an index condition on a partner
-- 'YCHR.VM.Foreach'. Returns @Just (k, j, other)@ when exactly one side
-- is partner @k@'s @j@-th argument and the other side's free variables
-- are all in scope at loop @k@'s evaluation point. Returns @Nothing@ if
-- neither side qualifies — in which case the equality stays in the
-- residual check expression.
classifyEqual ::
  Occurrence ->
  Expr ->
  Expr ->
  Maybe (PartnerIndex, ArgIndex, Expr)
classifyEqual occ a b
  | Just (k, j) <- asPartnerArg occ a,
    freeVars b `Set.isSubsetOf` inScopeBeforeLoop occ k =
      Just (k, j, b)
  | Just (k, j) <- asPartnerArg occ b,
    freeVars a `Set.isSubsetOf` inScopeBeforeLoop occ k =
      Just (k, j, a)
  | otherwise = Nothing

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
--     tests.  Equalities whose shape matches 'classifyEqual' are lifted
--     into per-partner index conditions ('PartnerCondMap'); the rest
--     are compiled into a single 'And'-chained residual expression.
-- | Compile a guard conjunction. The 'Maybe' 'Occurrence' parameter
-- enables the index-condition pushdown classifier when an occurrence
-- context is available; pass 'Nothing' (e.g. when compiling user-defined
-- function equations) to bypass classification — no partners exist so
-- nothing is liftable.
compileGuards ::
  Set Identifier ->
  Maybe Occurrence ->
  VarMap ->
  SrcInfo ->
  [D.Guard] ->
  Eff '[Writer [AnnP CompileError]] ([Stmt] -> [Stmt], PartnerCondMap, Maybe Expr, VarMap)
compileGuards funSet mOcc varMap si guards = do
  let (matchGuards, checkGuards) = partition isMatchGuard guards
  (matchWrapper, varMap') <- foldM (compileMatchGuard si) (id, varMap) matchGuards
  (condMap, checkExpr) <- compileCheckGuards funSet mOcc varMap' si checkGuards
  pure (matchWrapper, condMap, checkExpr, varMap')
  where
    isMatchGuard (D.GuardMatch {}) = True
    isMatchGuard (D.GuardGetArg {}) = True
    isMatchGuard _ = False

compileMatchGuard ::
  SrcInfo ->
  ([Stmt] -> [Stmt], VarMap) ->
  D.Guard ->
  Eff '[Writer [AnnP CompileError]] ([Stmt] -> [Stmt], VarMap)
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

-- | Compile the check guards of an occurrence, classifying each one as
-- either a liftable index condition for a partner 'YCHR.VM.Foreach' or
-- a residual boolean check that stays at the innermost guard position.
--
-- The classification (paper §5.3, "Indexing" / Loop-Invariant Code
-- Motion in spirit) inspects each compiled equality with
-- 'classifyEqual'. Liftable equalities are routed to a per-partner map;
-- the rest are 'And'-folded in source order into the residual check.
compileCheckGuards ::
  Set Identifier ->
  Maybe Occurrence ->
  VarMap ->
  SrcInfo ->
  [D.Guard] ->
  Eff '[Writer [AnnP CompileError]] (PartnerCondMap, Maybe Expr)
compileCheckGuards funSet mOcc varMap si guards = do
  (condMap, residuals) <- foldM step (Map.empty, []) guards
  let residual = case residuals of
        [] -> Nothing
        rs -> Just (foldl1 And rs)
  pure (condMap, residual)
  where
    classify e1 e2 = case mOcc of
      Just occ -> classifyEqual occ e1 e2
      Nothing -> Nothing
    step (cm, rs) (D.GuardEqual t1 t2) = do
      e1 <- compileTerm varMap si t1
      e2 <- compileTerm varMap si t2
      case classify e1 e2 of
        Just (k, j, other) ->
          pure (Map.insertWith (flip (++)) k [(j, other)] cm, rs)
        Nothing ->
          pure (cm, rs ++ [Equal e1 e2])
    step (cm, rs) (D.GuardExpr term) = do
      e <- EvalDeep <$> compileExpr funSet varMap si term
      pure (cm, rs ++ [e])
    step acc _ = pure acc

-- ---------------------------------------------------------------------------
-- Compile body goals
-- ---------------------------------------------------------------------------

compileBodyGoals :: Set Identifier -> SymbolTable -> VarMap -> SrcInfo -> [D.BodyGoal] -> Eff '[Writer [AnnP CompileError]] [Stmt]
compileBodyGoals funSet symTab varMap si goals = do
  (stmts, _) <- foldM step ([], varMap) goals
  pure stmts
  where
    step (acc, vm) goal = do
      (stmts, vm') <- compileBodyGoal funSet symTab vm si goal
      pure (acc ++ stmts, vm')

-- | Tell-unify two terms and immediately drain the resulting
-- reactivation queue. Used by 'D.BodyUnify' and the re-binding case of
-- 'D.BodyIs'. Wrapped in a helper because the dispatch shape is not
-- something a casual reader should have to re-derive every time.
unifyAndReactivate :: Expr -> Expr -> [Stmt]
unifyAndReactivate l r =
  [ ExprStmt (Unify l r),
    DrainReactivationQueue
      pendingName
      [ExprStmt (CallExpr reactivateDispatchName [Var pendingName])]
  ]

-- | Compile a single body goal, returning the generated statements and
-- an updated 'VarMap'. The VarMap may grow when a goal introduces new
-- variables (e.g. @is@ binding a fresh variable, or a constraint whose
-- arguments reference not-yet-seen variables that need 'NewVar').
compileBodyGoal :: Set Identifier -> SymbolTable -> VarMap -> SrcInfo -> D.BodyGoal -> Eff '[Writer [AnnP CompileError]] ([Stmt], VarMap)
compileBodyGoal _ _ varMap _ D.BodyTrue = pure ([], varMap)
compileBodyGoal _ _ varMap si (D.BodyConstraint con) = do
  let argVars = [v | VarTerm v <- con.args, notMemberVar v varMap]
      newStmts = [Let (Name v) NewVar | v <- argVars]
      varMap' = foldl' (\m v -> insertVar v (Var (Name v)) m) varMap argVars
  callArgs <- traverse (compileTerm varMap' si) con.args
  let tellName = tellProcName con.name (length callArgs)
  pure (newStmts ++ [ExprStmt (CallExpr tellName callArgs)], varMap')
compileBodyGoal _ _ varMap si (D.BodyUnify t1 t2) = do
  t1' <- compileTerm varMap si t1
  t2' <- compileTerm varMap si t2
  pure (unifyAndReactivate t1' t2', varMap)
compileBodyGoal _ _ varMap si (D.BodyHostStmt f args) = do
  args' <- traverse (compileTerm varMap si) args
  pure ([ExprStmt (HostCall (Name f) args')], varMap)
compileBodyGoal funSet _ varMap si (D.BodyIs v expr) = do
  expr' <- compileExpr funSet varMap si expr
  case lookupVar v varMap of
    -- Re-binding a variable already bound by the head: tell-unify so any
    -- existing constraints observing it are reactivated.
    Just existing -> pure (unifyAndReactivate existing (EvalDeep expr'), varMap)
    -- First binding of this variable: an ordinary 'Let' is enough; no
    -- observers can exist yet.
    Nothing ->
      let varMap' = insertVar v (Var (Name v)) varMap
       in pure ([Let (Name v) (EvalDeep expr')], varMap')
compileBodyGoal funSet _ varMap si (D.BodyFunctionCall (Types.Unqualified "call") args) = do
  args' <- traverse (compileExpr funSet varMap si) args
  pure ([ExprStmt (CallExpr (callFunProcName (length args - 1)) args')], varMap)
compileBodyGoal funSet _ varMap si (D.BodyFunctionCall name args) = do
  args' <- traverse (compileExpr funSet varMap si) args
  pure ([ExprStmt (CallExpr (funcProcName name (length args')) args')], varMap)

-- ---------------------------------------------------------------------------
-- Compile function definitions
-- ---------------------------------------------------------------------------

compileFunctionDef :: Set Identifier -> D.Function -> Eff '[Writer [AnnP CompileError]] Procedure
compileFunctionDef funSet func = do
  let procName' = funcProcName func.name func.arity
      params = [Name ("arg_" <> T.pack (show i)) | i <- [0 .. func.arity - 1]]
      funcSi = (func.equations.sourceLoc, func.equations.parsed)
      annotation =
        mkAnnotation
          ("function " <> flattenName func.name <> "/" <> T.pack (show func.arity))
          func.equations.sourceLoc
          func.equations.parsed
  eqStmts <- traverse (compileEquation funSet params funcSi) func.equations.node
  let errorStmt = ExprStmt (HostCall chrErrorName [Lit (AtomLit "no_matching_equation")])
  pure (Procedure procName' params (PushAnnotation annotation : concat eqStmts ++ [errorStmt]))

-- | Build a VarMap for a function equation: maps each normalized parameter
-- variable to the corresponding procedure parameter name.
buildEquationVarMap :: [Name] -> [Term] -> VarMap
buildEquationVarMap procParams normalizedArgs =
  varMapFromList
    [ (v, Var p)
    | (p, VarTerm v) <- zip procParams normalizedArgs
    ]

compileEquation :: Set Identifier -> [Name] -> SrcInfo -> D.Equation -> Eff '[Writer [AnnP CompileError]] [Stmt]
compileEquation funSet params si eq = do
  let varMap = buildEquationVarMap params eq.params
  -- Equations have no partners, so the index-condition pushdown
  -- classifier never fires; pass 'Nothing' to short-circuit it.
  (matchWrapper, _condMap, guardExpr, varMap') <- compileGuards funSet Nothing varMap si eq.guards
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
   in Procedure reactivateDispatchName [suspParamName] body
  where
    genDispatchBranch (ident, cType) =
      If
        (IsConstraintType (Var suspParamName) cType)
        [ExprStmt (CallExpr (activateProcName ident.name ident.arity) [Var suspParamName])]
        []

-- ---------------------------------------------------------------------------
-- call dispatch
-- ---------------------------------------------------------------------------

-- | Generate @call_1@ and @call_2@ dispatch procedures.
-- Each procedure pattern-matches on the closure/function-reference term
-- and dispatches to the appropriate compiled function.
genCallFunDispatches :: [D.Function] -> [Procedure]
genCallFunDispatches functions =
  [genCallFunDispatch functions callArity | callArity <- [1, 2]]

genCallFunDispatch :: [D.Function] -> Int -> Procedure
genCallFunDispatch functions callArity =
  let closureParam = Name "closure"
      argParams = [Name ("arg_" <> T.pack (show i)) | i <- [0 .. callArity - 1]]
      funRefBranches = concatMap (genFunRefBranch callArity argParams) functions
      lambdaBranches = concatMap (genLambdaBranch callArity argParams) functions
      errorStmt = ExprStmt (HostCall chrErrorName [Lit (AtomLit "call: no matching closure")])
   in Procedure
        (callFunProcName callArity)
        (closureParam : argParams)
        (funRefBranches ++ lambdaBranches ++ [errorStmt])

-- | Generate a dispatch branch for a function reference (@name/arity@).
-- Only emits a branch when the function's arity matches @callArity@.
genFunRefBranch :: Int -> [Name] -> D.Function -> [Stmt]
genFunRefBranch callArity argParams func
  | func.arity /= callArity = []
  | otherwise =
      let flatName = flattenName func.name
          pName = funcProcName func.name func.arity
          condition =
            And
              (MatchTerm (Var (Name "closure")) (Name "/") 2)
              ( And
                  (Equal (GetArg (Var (Name "closure")) 0) (Lit (AtomLit flatName)))
                  (Equal (GetArg (Var (Name "closure")) 1) (Lit (IntLit func.arity)))
              )
       in [If condition [Return (CallExpr pName (map Var argParams))] []]

-- | Generate a dispatch branch for a lifted lambda closure.
-- Only emits a branch for functions whose name starts with @__lambda_@.
--
-- Closures are self-describing terms of the form
-- @__closure(LambdaId, SourceForm, Cap1, …, CapN)@.
-- The first two arguments are the lambda identifier and the quoted
-- source form (for pretty-printing); captured variables start at
-- index 2, hence the @+ 2@ offset in 'captureBinds' below.
genLambdaBranch :: Int -> [Name] -> D.Function -> [Stmt]
genLambdaBranch callArity argParams func
  | not (isLambdaFunc func) = []
  | numCaptures < 0 = []
  | otherwise =
      let Name lambdaVmText = vmName func.name
          pName = funcProcName func.name func.arity
          -- The closure has 2 header fields (lambdaId, sourceForm) followed
          -- by the captured free variables, so its total arity is
          -- numCaptures + 2.
          condition =
            And
              (MatchTerm (Var (Name "closure")) (Name "__closure") (numCaptures + 2))
              (Equal (GetArg (Var (Name "closure")) 0) (Lit (AtomLit lambdaVmText)))
          -- Captures are stored after the 2 header fields (lambdaId at
          -- index 0, sourceForm at index 1), so capture i lives at
          -- index i + 2.
          captureBinds =
            [ Let (Name ("cap_" <> T.pack (show i))) (GetArg (Var (Name "closure")) (i + 2))
            | i <- [0 .. numCaptures - 1]
            ]
          captureVars = [Var (Name ("cap_" <> T.pack (show i))) | i <- [0 .. numCaptures - 1]]
          allArgs = captureVars ++ map Var argParams
       in [If condition (captureBinds ++ [Return (CallExpr pName allArgs)]) []]
  where
    numCaptures = func.arity - callArity

-- | Check if a function was generated by lambda lifting.
isLambdaFunc :: D.Function -> Bool
isLambdaFunc func = case func.name of
  Types.Qualified _ n -> T.isPrefixOf "__lambda_" n
  Types.Unqualified n -> T.isPrefixOf "__lambda_" n

{- ---------------------------------------------------------------------------
Notes
-----------------------------------------------------------------------------

Why occurrences are reversed before numbering: 'collectOccurrences' folds
each rule's occurrences into the 'OccurrenceMap' with 'occMapAppend',
which is implemented on top of @Map.insertWith (++)@ and therefore
prepends. Reversing the resulting list before 'assignNumbers' restores
top-down rule order so that occurrence number 1 is the textually first
occurrence of the constraint, matching the convention in the paper's
Listings.

Why partner ordering is "removed first, right-to-left" inside
'ruleOccurrences': this is the ωr refined operational semantics from
Duck et al. (2004) and the paper §2.2, Fig. 2. Removed occurrences are
tried before kept ones so that simplifications fire eagerly, and within
each group the rightmost head constraint gets the lowest occurrence
number so that join order matches a left-to-right scan of the body when
the rule is read as a Horn clause.

Why 'buildVarMap' only inspects 'VarTerm' arguments: HNF
('YCHR.Desugar.normalizeHead') guarantees that every head argument is
either a 'VarTerm' or a 'Wildcard'. Non-variable patterns have been
lifted into 'D.GuardMatch' and 'D.GuardGetArg' guards by the desugarer
and replaced with fresh variables in the head. The list-comprehension
patterns silently drop wildcards (which are never referenced from
guards or bodies anyway) and would silently drop other shapes too — the
HNF invariant is what makes that safe.

Why the active constraint is called @active@ everywhere: at runtime
"constraint identifier" and "constraint suspension" are the same value
(a pointer to a heap-allocated 'YCHR.Runtime.Types.Suspension'). The
compiler picks the paper's terminology — "active constraint" — and uses
'activeName' as the single local-variable name in @tell_c@, @activate_c@,
and inside every @occurrence_c_j@ procedure. The only places that still
talk about a "suspension" are @reactivate_dispatch@ ('suspParamName')
and 'DrainReactivationQueue' ('pendingName'), where the value really is
"a suspension we received from somewhere else".

Why 'compileExpr' does not recurse through non-function compound terms:
function calls are only resolved at the top level of an expression
context (an @is@ RHS, a guard expression, or an argument of a recognised
function call). Inside an opaque data constructor like
@pair(foo(X), bar(Y))@, the @foo@ and @bar@ subterms are /terms/, not
calls — Prolog and CHR both treat data constructors and function symbols
as syntactically indistinguishable, and the recogniser uses the
'funSet' membership test to decide which is which. The fall-through
'compileTerm' branch is therefore intentional: it compiles such subterms
as 'MakeTerm' nodes regardless of whether their head /happens/ to share a
name with a declared function.

Why 'genFireStmts' skips the alive check for removed partners during
backjumping: 'genKillStmts' has just emitted an unconditional 'Kill' for
every removed partner, so they are guaranteed dead by the time the body
runs. Emitting an alive check for them would always fail and the
resulting unconditional 'Continue' would make every later check
unreachable (paper §5.3, "all following alive tests thus becomes
redundant"). Backjumping is only useful for kept partners.

Why anonymous rules get a synthetic @rule_N@ name in 'ruleOccurrences':
the propagation history is keyed on (rule name, constraint id tuple).
If two anonymous propagation rules shared a single placeholder name,
they would collide in the history and prevent each other from firing.
The synthetic name uses the rule's program-wide source position, which
is stable as long as the source order is.

Why 'extractSymbolTable' lives in 'YCHR.Desugar' rather than here: the
constraint-type indices it produces are needed both by this module and
by 'YCHR.Compile.compile', but they are derivable purely from the
desugared program's rule heads. Computing them in the desugarer keeps
the compilation pipeline single-pass over the desugared AST.
--------------------------------------------------------------------------- -}
