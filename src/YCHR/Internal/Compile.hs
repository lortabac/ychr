{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}

-- |
-- Module      : YCHR.Internal.Compile
-- Description : Transforms a desugared CHR program into a VM program.
--
-- The Compiler is the transformation pass between the desugared
-- 'YCHR.Internal.Desugared.Program' and the abstract 'YCHR.Internal.VM.Program' consumed by
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
-- 5. /@$call@ dispatch/: 'genCallFunDispatches' emits one
--    @call_N@ procedure per supported call arity to dispatch first-class
--    function values (function references and lifted lambda closures).
--
-- The basic compilation scheme is from paper §5.2; the Early Drop and
-- Backjumping optimizations are from §5.3 (Listing 8). Selective
-- Constraint Reactivation is implemented at the runtime level (the
-- observer pattern in 'YCHR.Internal.Runtime.Reactivation') — this pass only emits
-- 'DrainReactivationQueue' calls after each tell-side @Unify@.
--
-- Non-obvious design choices are documented in the \"Notes\" block at the
-- bottom of this file.
module YCHR.Internal.Compile
  ( -- * Errors
    CompileError (..),

    -- * Compilation
    compile,

    -- * Function compilation
    compileFunctionDef,

    -- * Call dispatch
    genCallFunDispatches,

    -- * Re-exported name builders (see "YCHR.Internal.Compile.Names")
    funcProcName,
    vmName,
    procNameFor,
    tellProcName,
    activateProcName,
    occProcName,
  )
where

import Control.Monad (foldM)
import Control.Monad.Trans.Writer.CPS (Writer, runWriter, tell)
import Data.List (nub, partition, sortOn)
import Data.List qualified as List
import Data.Map.Strict qualified as Map
import Data.Maybe (isJust)
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as T
import YCHR.Internal.Compile.Names
import YCHR.Internal.Compile.Occurrences (collectOccurrences)
import YCHR.Internal.Compile.Types
import YCHR.Internal.Desugared qualified as D
import YCHR.Internal.Diagnostic (Diagnostic (..))
import YCHR.Internal.Loc (SourceLoc)
import YCHR.Internal.PExpr (PExpr)
import YCHR.Internal.Parsed (AnnP (..))
import YCHR.Internal.Parsed qualified as P
import YCHR.Internal.Pretty (prettyPExprSrc)
import YCHR.Internal.Resolved qualified as R
import YCHR.Internal.Types
  ( HeadArg (..),
    Identifier (..),
    SymbolTable,
    Term (..),
    flattenName,
    symbolTableSize,
    symbolTableToList,
  )
import YCHR.Internal.Types qualified as Types
import YCHR.Internal.VM

-- | Source location, original parsed expression, and optional context
-- label, extracted from an 'AnnP' wrapper.
data SrcInfo = SrcInfo
  { -- | Source location attached to the originating 'AnnP'.
    srcLoc :: P.SourceLoc,
    -- | Pretty-printable parsed form, used to render diagnostics.
    srcParsed :: PExpr,
    -- | Optional context label (e.g. @"rule foo"@ or
    -- @"function bar/2"@) prefixed onto diagnostic messages.
    srcLabel :: Maybe Text
  }

-- ---------------------------------------------------------------------------
-- Public API
-- ---------------------------------------------------------------------------

-- | Compile a desugared program against the given constraint-type symbol
-- table. Returns 'Right' a 'YCHR.Internal.VM.Program' on success, or 'Left' the
-- accumulated errors. Errors from every sub-pass are collected before
-- the function decides to fail, so callers see as much detail as
-- possible in one go.
compile :: D.Program -> SymbolTable -> Either [Diagnostic CompileError] Program
compile prog symTab =
  let ( (occMap, ruleDisplayNames),
        occErrs
        ) = runWriter (collectOccurrences symTab prog)
      (procs, procErrs) = runWriter $ do
        fmap concat $
          traverse (genConstraintProcs symTab occMap) (symbolTableToList symTab)
      (funProcs, funErrs) = runWriter $ do
        traverse compileFunctionDef prog.functions
      dispatch = genReactivateDispatch symTab
      callFunDispatches = genCallFunDispatches prog.functions
      allErrs = occErrs ++ procErrs ++ funErrs
   in if null allErrs
        then
          Right
            Program
              { numTypes = symbolTableSize symTab,
                typeNames = buildTypeNames symTab,
                numRules = length ruleDisplayNames,
                ruleNames = ruleDisplayNames,
                procedures = procs ++ funProcs ++ [dispatch] ++ callFunDispatches,
                evaluables = buildEvaluables prog.functions
              }
        else Left allErrs

-- | Build the dispatch table consumed by the runtime @is@
-- deep-evaluator. Each user-defined function contributes one entry
-- mapping its 'EvaluableKey' (VM-encoded functor + arity, matching
-- the form stored on a @VTerm@) to the mangled 'funcProcName' that
-- resolves the compiled procedure.
--
-- The list may carry one entry per source function, which means the
-- @(functor, arity)@ key is unique by construction: the language
-- already forbids two functions of the same name and arity (an
-- @open_function@ across modules still has a single equation set
-- under the same qualified name, so it surfaces here as one entry).
-- The runtime's @Map.fromList@ would otherwise pick the last entry
-- silently.
buildEvaluables :: [D.Function] -> [(EvaluableKey, Name)]
buildEvaluables functions =
  [ ( EvaluableKey {functor = vmName funcName, arity = func.arity},
      funcProcName funcName func.arity
    )
  | func <- functions,
    let funcName = Types.qualifiedToName func.name
  ]

-- | Build the list of constraint type source names, indexed by
-- 'Types.ConstraintType'. The list is ordered by the constraint type's
-- integer index, so @typeNames !! i@ is the name of the type with index @i@.
buildTypeNames :: SymbolTable -> [Types.Name]
buildTypeNames symTab =
  [ ident.name
  | (ident, _) <- sortOn (ctIndex . snd) (symbolTableToList symTab)
  ]
  where
    ctIndex (Types.ConstraintType i) = i

-- ---------------------------------------------------------------------------
-- Procedure generation for each constraint type
-- ---------------------------------------------------------------------------

genConstraintProcs ::
  SymbolTable ->
  OccurrenceMap ->
  ( Identifier,
    ConstraintType
  ) ->
  Writer [Diagnostic CompileError] [Procedure]
genConstraintProcs symTab occMap (ident, cType) = do
  -- Passive occurrences (paper §5.3, marked by 'YCHR.Internal.Compile.Passive')
  -- can never fire when this constraint is active, so we emit neither
  -- their occurrence procedure nor the call to it from activate. They
  -- keep their ωr numbers, so the surviving procedures' names are stable.
  let occs = filter (not . (.passive)) (lookupOccurrences ident occMap)
      tellProc = genTell ident.name cType ident.arity
      activate = genActivate ident.name cType ident.arity occs
  occProcs <- traverse (genOccurrence symTab ident.name cType ident.arity) occs
  pure (tellProc : activate : occProcs)

-- ---------------------------------------------------------------------------
-- tell_c
-- ---------------------------------------------------------------------------

-- | Generate the @tell_c@ procedure. Allocates the suspension and hands
-- it straight to @activate_c@ — deliberately without a 'Store': storage
-- is postponed to the latest point that could observe the constraint
-- (Late Storage, paper §5.3). A constraint whose activation removes it
-- is never stored at all, skipping the store append and the observer
-- registration walk over its arguments.
genTell :: Types.Name -> ConstraintType -> Int -> Procedure
genTell name cType arity =
  let params = argNames arity
      tellName = tellProcName name arity
      activateName = activateProcName name arity
   in Procedure
        { name = tellName,
          params = params,
          body =
            [ LetId activeName (CreateConstraint cType (map Var params)),
              ExprStmt (CallExpr activateName [AId (IdVar activeName)])
            ],
          procKind = PKTell cType
        }

-- ---------------------------------------------------------------------------
-- activate_c
-- ---------------------------------------------------------------------------

-- | Generate the @activate_c@ procedure. Takes the active constraint as
-- its single parameter, extracts the constraint arguments into local
-- variables, and tries each occurrence procedure in order (paper §5.2,
-- Listing 2 with Early Drop from Listing 8).
genActivate :: Types.Name -> ConstraintType -> Int -> [Occurrence] -> Procedure
genActivate name cType arity occs =
  let activateName = activateProcName name arity
      argExtracts =
        [ LetVal (argName i) (FieldArg (IdVar activeName) (ArgIndex i))
        | i <- [0 .. arity - 1]
        ]
      -- Late Storage (paper §5.3): a constraint that survives every
      -- occurrence must be in the store — findable as a partner and
      -- observing its variables — before activation returns. 'Store' is
      -- idempotent, so re-activation of an already-stored constraint
      -- (via @reactivate_dispatch@) passes through here harmlessly. The
      -- early-drop returns above skip this on purpose: a dropped
      -- constraint is dead and dead constraints are never stored.
      body =
        argExtracts
          ++ concatMap genActivateCall occs
          ++ [Store (IdVar activeName), Return (Lit (BoolLit False))]
   in Procedure
        { name = activateName,
          params = [activeName],
          body = body,
          procKind = PKActivate cType
        }
  where
    occCallArgs =
      AId (IdVar activeName) : map (AVal . Var) (argNames arity)
    genActivateCall occ =
      let occName = occProcName name arity occ.number
       in [ LetVal dropResultName (CallExpr occName occCallArgs),
            If (BFromVal (Var dropResultName)) [Return (Lit (BoolLit True))] []
          ]

-- ---------------------------------------------------------------------------
-- occurrence_c_j
-- ---------------------------------------------------------------------------

genOccurrence ::
  SymbolTable ->
  Types.Name ->
  ConstraintType ->
  Int ->
  Occurrence ->
  Writer [Diagnostic CompileError] Procedure
genOccurrence symTab name cType arity occ = do
  let params = activeName : argNames arity
      procName' = occProcName name arity occ.number
      varMap = buildVarMap occ
  body <- genOccurrenceBody symTab varMap occ
  pure
    Procedure
      { name = procName',
        params = params,
        body = body,
        procKind = PKOccurrence cType occ.number.unOccurrenceNumber occ.ruleId occ.ruleDisplay
      }

-- | Map every user-written head variable in an 'Occurrence' to the
-- generated VM variable that holds its value (an @X_i@ for the active
-- constraint, a @pArg_k_j@ for partner @k@). 'HeadWildcard' arguments
-- contribute no binding: wildcards are never referenced from guards
-- or bodies. See the \"Notes\" block at the bottom of this file.
buildVarMap :: Occurrence -> VarMap
buildVarMap occ =
  let activeBindings =
        [ (v, Var (argName i))
        | (i, HeadVar v) <- zip [0 ..] occ.activeArgs
        ]
      partnerBindings =
        [ (v, Var (partArgName k j))
        | (k, partner) <- zip [PartnerIndex 0 ..] occ.partners,
          (j, HeadVar v) <- zip [0 ..] partner.constraint.args
        ]
   in varMapFromList (activeBindings ++ partnerBindings)

-- | Compile the body of an occurrence procedure: build the innermost
-- "guards-then-fire" block, wrap it in one nested 'Foreach' per partner,
-- then append the trailing @Return false@ that signals "no early drop".
genOccurrenceBody ::
  SymbolTable ->
  VarMap ->
  Occurrence ->
  Writer [Diagnostic CompileError] [Stmt]
genOccurrenceBody symTab varMap occ = do
  (inner, condMap) <- genGuardedFire symTab varMap occ
  let body = wrapInPartnerLoops occ condMap inner
  -- Push the rule frame at procedure entry, so it is live during guard
  -- evaluation (and the history check) as well as body execution. A guard
  -- that errors (e.g. evaluates to a non-boolean) then reports the rule's
  -- source location and label, just like a body error. The frame is scoped
  -- to this call: the interpreter restores the frames it found when the
  -- call returns, so it does not accumulate.
  pure (PushFrame (mkRuleFrame occ) : body ++ [Return (Lit (BoolLit False))])

-- | Compile the guards followed by the rule-firing block. Returns the
-- statements that go at the innermost partner-loop position — any HNF
-- match-guard wrappers (lets and structural @if@s introduced by
-- 'D.GuardMatch' / 'D.GuardGetArg') wrapped around the conditional
-- 'genFireStmts' result — together with the per-partner index
-- conditions lifted out of equality check guards by 'compileCheckGuards'.
genGuardedFire ::
  SymbolTable ->
  VarMap ->
  Occurrence ->
  Writer [Diagnostic CompileError] ([Stmt], PartnerCondMap)
genGuardedFire symTab varMap occ = do
  let AnnP {node = guards, sourceLoc = guardLoc, parsed = guardP} = occ.rule.guard
      ruleLabel = Just ("rule " <> occ.ruleDisplay)
      guardSi = SrcInfo guardLoc guardP ruleLabel
  compiled <- compileGuards (Just occ) Nothing varMap guardSi guards
  fireStmts <- genFireStmts symTab compiled.extendedVarMap occ
  let guarded = case compiled.residualCheck of
        Nothing -> fireStmts
        Just gExpr -> [If (softenGuard gExpr) fireStmts []]
  pure (compiled.matchWrapper guarded, compiled.indexConditions)

-- | Wrap a rule-occurrence guard residual in 'BSoftGuard', so that an
-- instantiation failure inside it (an unbound variable reached a
-- decision point) makes the guard evaluate to 'False' instead of
-- aborting the query. The rule does not fire; binding the variable
-- later reactivates the constraint and retries the occurrence.
--
-- The wrapper is emitted only when the residual can actually raise.
-- A residual built purely from 'BEqual' conjuncts is ask-semantics
-- structural equality, which is total — it answers 'False' on unbound
-- operands rather than failing — so wrapping it would cost a catch
-- frame on a hot path for no behavioural difference. Only 'BFromVal'
-- (user-written guard expressions: host primitives, function calls,
-- @'$call'@ dispatch) can raise here.
softenGuard :: BoolExpr -> BoolExpr
softenGuard gExpr
  | canRaise gExpr = BSoftGuard gExpr
  | otherwise = gExpr
  where
    canRaise (BFromVal _) = True
    canRaise (BAnd a b) = canRaise a || canRaise b
    canRaise (BOr a b) = canRaise a || canRaise b
    canRaise (BNot a) = canRaise a
    canRaise (BEvalDeep a) = canRaise a
    canRaise (BSoftGuard _) = False
    canRaise _ = False

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
          conds = [(c.argIndex, c.expectedValue) | c <- Map.findWithDefault [] k condMap]
          -- Bind the partner's id and arguments as ordinary locals so
          -- the rest of the body can reference them by name. The id is
          -- the suspension itself: 'IdVar suspVar' is renamed to
          -- 'IdVar (partIdName k)' for symmetry with subsequent uses.
          fieldExtracts =
            LetId (partIdName k) (IdVar suspVar)
              : [ LetVal (partArgName k j) (FieldArg (IdVar suspVar) (ArgIndex j))
                | j <- [0 .. partArity - 1]
                ]
          -- The partner must be distinct from the active constraint and
          -- from every earlier partner: at most one suspension can play
          -- a given role in a rule firing. No alive checks here — the
          -- Foreach iterator guarantees yielded partners are alive, and
          -- the active constraint's liveness is verified after body
          -- execution (early drop / backjumping in 'genFireStmts').
          distinctActive = BNot (BIdEqual (IdVar (partIdName k)) (IdVar activeName))
          distinctEarlier =
            [ BNot (BIdEqual (IdVar (partIdName k)) (IdVar (partIdName j)))
            | j <- [PartnerIndex 0 .. k - 1]
            ]
          distinctAll = List.foldl' BAnd distinctActive distinctEarlier
          guarded = [If distinctAll inside []]
       in [Foreach label partner.cType suspVar conds (fieldExtracts ++ guarded)]

-- ---------------------------------------------------------------------------
-- Fire: history check + kill + body + early drop + backjumping
-- ---------------------------------------------------------------------------

genFireStmts ::
  SymbolTable ->
  VarMap ->
  Occurrence ->
  Writer [Diagnostic CompileError] [Stmt]
genFireStmts symTab varMap occ = do
  let rule = occ.rule
      AnnP {node = ruleHead} = rule.head
      isPropagation = null ruleHead.removed
      activeIsRemoved = not occ.isKept
      ruleId' = occ.ruleId
      historyIds = buildHistoryIds occ
      killStmts = genKillStmts occ
  let AnnP {node = ruleBody, sourceLoc = bodyLoc, parsed = bodyP} = rule.body
      ruleLabel = Just ("rule " <> occ.ruleDisplay)
      bodySi = SrcInfo bodyLoc bodyP ruleLabel
  bodyStmts <- compileBodyGoals symTab varMap bodySi ruleBody
  let earlyDropStmts
        | activeIsRemoved = [Return (Lit (BoolLit True))]
        | otherwise = [If (BNot (BAlive (IdVar activeName))) [Return (Lit (BoolLit True))] []]
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
                (BNot (BAlive (IdVar (partIdName k))))
                [Continue (partLabel k)]
                []
            | (k, p) <- zip [PartnerIndex 0 ..] occ.partners,
              p.isKept
            ]
      -- Late Storage (paper §5.3): a kept active constraint must be in
      -- the store before a non-empty body runs — the body may tell
      -- constraints that need it as a partner, or unify variables it
      -- must be reactivated on. A removed active was just killed, and
      -- an empty body observes nothing, so both leave storage to the
      -- end of @activate_c@. Sound only because guard residuals do not
      -- tell (dev-docs/INVARIANTS.md): nothing can mutate the store or
      -- bind variables while the constraint is alive but unstored.
      -- (The store can still be *read* in that window — a guard
      -- reaching @write_store_to_list@ through a host call will not
      -- list the active constraint; see INVARIANTS.md §Scope.)
      storeStmts =
        [Store (IdVar activeName) | not activeIsRemoved, not (null bodyStmts)]
      -- The rule frame is pushed at occurrence-procedure entry (see
      -- 'genOccurrenceBody'), so it is already on the call stack here.
      coreFireStmts =
        killStmts
          ++ storeStmts
          ++ bodyStmts
          ++ earlyDropStmts
          ++ backjumpStmts
  pure $
    if isPropagation
      then
        [ If
            (BNotInHistory ruleId' historyIds)
            (AddHistory ruleId' historyIds : coreFireStmts)
            []
        ]
      else coreFireStmts

-- | Collect constraint identifiers for the propagation history tuple.
-- Each id is tagged with its head position and handed to
-- 'mkHistoryIds', which orders them, so that the same rule with the
-- same partner combination always produces an identical tuple
-- regardless of which occurrence is active (paper §5.2, Listing 1,
-- line 14).
buildHistoryIds :: Occurrence -> HistoryIds
buildHistoryIds occ =
  mkHistoryIds $
    (occ.activeIdx, IdVar activeName)
      : [ (p.idx, IdVar (partIdName k))
        | (k, p) <- zip [PartnerIndex 0 ..] occ.partners
        ]

-- | Build a 'StackFrame' for a rule firing.
mkRuleFrame :: Occurrence -> StackFrame
mkRuleFrame occ =
  let label = "rule " <> occ.ruleDisplay
   in mkFrame label occ.rule.head.sourceLoc occ.rule.head.parsed

-- | Build a 'StackFrame' from a label, source location, and parsed expression.
mkFrame :: Text -> SourceLoc -> PExpr -> StackFrame
mkFrame label loc pexpr =
  StackFrame
    { frameLabel = label,
      frameSourceLoc = loc,
      frameSourceCode = T.pack (prettyPExprSrc pexpr)
    }

genKillStmts :: Occurrence -> [Stmt]
genKillStmts occ =
  let -- Kill removed partners
      partnerKills =
        [ Kill (IdVar (partIdName k))
        | (k, p) <- zip [PartnerIndex 0 ..] occ.partners,
          not p.isKept
        ]
      -- Kill active if removed
      activeKill = [Kill (IdVar activeName) | not occ.isKept]
   in partnerKills ++ activeKill

-- ---------------------------------------------------------------------------
-- Compile terms
-- ---------------------------------------------------------------------------

compileTerm :: VarMap -> SrcInfo -> Term -> Writer [Diagnostic CompileError] ValExpr
compileTerm varMap si (VarTerm v) = case lookupVar v varMap of
  Just expr -> pure expr
  Nothing -> do
    tell [Diagnostic si.srcLabel (AnnP (UnboundVariable v) si.srcLoc si.srcParsed)]
    pure (Lit WildcardLit)
compileTerm _ _ (IntTerm n) = pure (Lit (IntLit n))
compileTerm _ _ (FloatTerm n) = pure (Lit (FloatLit n))
compileTerm _ _ (TextTerm s) = pure (Lit (TextLit s))
-- Native-bool fast path: source @true@/@false@ reach @compileTerm@ only
-- as the renamer-canonicalized @prelude:true@ / @prelude:false@ form
-- ('Types.preludeBool'). Match the canonical compound shape so the @If@
-- instruction can dispatch on @VBool@ without boxing.
compileTerm _ _ (CompoundTerm name [])
  | Just b <- Types.preludeBool name =
      pure (Lit (BoolLit b))
-- 0-arity compounds normalize to atom literals: at the runtime layer
-- the canonical form is 'VAtom' (no empty-args vector), and 'AtomLit'
-- is the cheap VM constructor for that value. 'BMatchTerm' accepts
-- 'VAtom' for arity-0 tests so the dispatch invariant is preserved at
-- the matcher layer rather than via a parallel runtime representation.
-- The two prelude booleans are the exception on both sides: they are
-- values here, and 'compileMatchGuard' gives them a matching
-- boolean-valued pattern test instead of a 'BMatchTerm'.
--
-- Qualified 0-arity uses 'vmName' for the @m__n@ mangled functor;
-- unqualified 0-arity (user-quoted atoms, undeclared bare names)
-- keeps the raw name so unicode is preserved as data — 'vmName' would
-- escape non-ASCII to @%%u\<hex\>@, which is appropriate for
-- qualified-name mangling but not for atom values.
compileTerm _ _ (CompoundTerm name@(Types.Qualified _ _) []) =
  pure (Lit (AtomLit (vmName name).unName))
compileTerm _ _ (CompoundTerm (Types.Unqualified n) []) =
  pure (Lit (AtomLit n))
compileTerm varMap si (CompoundTerm name args) = do
  args' <- traverse (compileTerm varMap si) args
  pure (MakeTerm (vmName name) args')
compileTerm _ _ Wildcard = pure (Lit WildcardLit)

-- | Lower a typed 'D.Expr' to a VM 'ValExpr'. Each constructor maps to
-- exactly one runtime behavior:
--
--   * 'D.CallExpr' / 'D.ApplyExpr' / 'D.HostExpr' produce 'CallExpr' /
--     'HostCall' instructions.
--   * 'D.CtorExpr' produces a 'MakeTerm', with its arguments recursively
--     lowered. The native-bool fast path and the @quote\/1@ quoting form
--     are the only structural special cases.
--   * 'D.FunRefExpr' produces the canonical @'/'(<flatname>, <arity>)@
--     compound that 'genCallFunDispatches' pattern-matches at runtime.
--   * 'D.LambdaExpr' is removed by lambda lifting before compilation
--     and is therefore unreachable here.
compileExpr ::
  VarMap ->
  SrcInfo ->
  D.Expr ->
  Writer [Diagnostic CompileError] ValExpr
compileExpr varMap si e = case e of
  R.VarExpr v -> case lookupVar v varMap of
    Just expr -> pure expr
    Nothing -> do
      tell [Diagnostic si.srcLabel (AnnP (UnboundVariable v) si.srcLoc si.srcParsed)]
      pure (Lit WildcardLit)
  R.IntExpr n -> pure (Lit (IntLit n))
  R.FloatExpr n -> pure (Lit (FloatLit n))
  R.TextExpr s -> pure (Lit (TextLit s))
  R.WildcardExpr -> pure (Lit WildcardLit)
  -- Native-bool fast path: the renamer canonicalizes source @true@ /
  -- @false@ to @prelude:true@ / @prelude:false@ ('Types.preludeBool').
  -- Matching them structurally lets 'If' dispatch on 'VBool' without
  -- boxing.
  R.CtorExpr name []
    | Just b <- Types.preludeBool name ->
        pure (Lit (BoolLit b))
  -- @quote\/1@ short-circuit: the subtree stays opaque (no calls are
  -- evaluated). Delegate to 'compileTerm' on the surface 'Term' shape
  -- of the argument; the user opts into this with @quote(foo(X))@ when
  -- they want @foo@ kept structural even if it is also a declared
  -- function.
  R.CtorExpr (Types.Unqualified "quote") [arg] ->
    compileTerm varMap si (R.exprToTerm arg)
  -- 0-arity ctors collapse to atom literals at runtime (see comment
  -- in 'compileTerm'). Compiler never emits @MakeTerm name []@.
  R.CtorExpr name@(Types.Qualified _ _) [] ->
    pure (Lit (AtomLit (vmName name).unName))
  R.CtorExpr (Types.Unqualified n) [] ->
    pure (Lit (AtomLit n))
  -- Other constructor compounds: arguments stay in expression context
  -- so nested calls (e.g. @foo(X)@ inside @pair(foo(X), bar)@) are
  -- evaluated.
  R.CtorExpr name args -> do
    args' <- traverse (compileExpr varMap si) args
    pure (MakeTerm (vmName name) args')
  R.CallExpr qn args -> do
    args' <- traverse (compileExpr varMap si) args
    let funcName = Types.qualifiedToName qn
    pure (CallExpr (funcProcName funcName (length args')) (map AVal args'))
  R.ApplyExpr f args -> do
    fAndArgs <- traverse (compileExpr varMap si) (f : args)
    pure (CallExpr (callFunProcName (length args)) (map AVal fAndArgs))
  R.HostExpr f args -> do
    args' <- traverse (compileExpr varMap si) args
    pure (HostCall (Name f) args')
  R.FunRefExpr qn arity ->
    pure
      ( MakeTerm
          (Name "/")
          [ Lit (AtomLit (flattenName (Types.qualifiedToName qn))),
            Lit (IntLit (fromIntegral arity))
          ]
      )
  R.LambdaExpr {} ->
    error "Compile.compileExpr: LambdaExpr survived lambda lifting"

-- ---------------------------------------------------------------------------
-- Compile guards
-- ---------------------------------------------------------------------------

-- | Free 'Var' / 'IdVar' names occurring in a 'ValExpr'. Used by the
-- index-condition pushdown classifier to decide whether the
-- non-partner-arg side of an equality is referenceable at a partner
-- loop's evaluation point. Walks through 'IdExpr' children too: even
-- though their bindings live in a separate environment slot at
-- runtime, scope-wise they share a single source-level namespace.
freeVars :: ValExpr -> Set Name
freeVars = goV
  where
    goV (Var n) = Set.singleton n
    goV (Lit _) = Set.empty
    goV NewVar = Set.empty
    goV (CallExpr _ args) = Set.unions (map goA args)
    goV (HostCall _ es) = Set.unions (map goV es)
    goV (EvalDeep e) = goV e
    goV (EvalIs e) = goV e
    goV (MakeTerm _ es) = Set.unions (map goV es)
    goV (GetArg e _) = goV e
    goV (FieldArg e _) = goI e
    goV (FieldType e) = goI e

    goI (IdVar n) = Set.singleton n
    goI (CreateConstraint _ es) = Set.unions (map goV es)

    goA (AVal e) = goV e
    goA (AId e) = goI e

-- | Set of variable names visible at the moment partner @k@'s
-- 'YCHR.Internal.VM.Foreach' evaluates its index-condition expressions: the
-- active constraint's argument names, plus every earlier partner's
-- argument names. Match-guard 'LetVal' bindings are deliberately /not/
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

-- | Recognise a 'ValExpr' that is a reference to a partner argument
-- variable. The inverse of 'partArgName' for the partner indices and
-- arities present in @occ@.
asPartnerArg :: Occurrence -> ValExpr -> Maybe (PartnerIndex, ArgIndex)
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
-- 'YCHR.Internal.VM.Foreach'. Returns @Just (k, j, other)@ when exactly one side
-- is partner @k@'s @j@-th argument and the other side's free variables
-- are all in scope at loop @k@'s evaluation point. Returns @Nothing@ if
-- neither side qualifies — in which case the equality stays in the
-- residual check expression.
classifyEqual ::
  Occurrence ->
  ValExpr ->
  ValExpr ->
  Maybe (PartnerIndex, ArgIndex, ValExpr)
classifyEqual occ a b
  | Just (k, j) <- asPartnerArg occ a,
    freeVars b `Set.isSubsetOf` inScopeBeforeLoop occ k =
      Just (k, j, b)
  | Just (k, j) <- asPartnerArg occ b,
    freeVars a `Set.isSubsetOf` inScopeBeforeLoop occ k =
      Just (k, j, a)
  | otherwise = Nothing

-- | Compile a guard conjunction. Guards are split into two groups:
--
--   * __Match guards__ ('D.GuardMatch', 'D.GuardGetArg') introduce new
--     variable bindings and structural checks. They are compiled into
--     a wrapper @[Stmt] -> [Stmt]@ that nests the inner code inside
--     conditionals and let-bindings. Match guards must be processed
--     first so that the variables they bind are in scope for check
--     guards.
--
--   * __Check guards__ ('D.GuardEqual', 'D.GuardExpr') are pure boolean
--     tests. Equalities whose shape matches 'classifyEqual' are lifted
--     into per-partner index conditions ('PartnerCondMap'); the rest
--     are compiled into a single 'And'-chained residual expression.
--
-- The 'Maybe' 'Occurrence' parameter enables the index-condition
-- pushdown classifier when an occurrence context is available; pass
-- 'Nothing' (e.g. when compiling user-defined function equations) to
-- bypass classification — no partners exist so nothing is liftable.
--
-- The 'Maybe' 'EqDispatch' parameter switches on /equation mode/, used
-- when compiling a user-defined function's equations. It has two
-- effects. First, 'D.GuardEqual' is treated as a match guard rather
-- than a check guard: inside an equation every @GuardEqual@ is
-- pattern-origin (HNF emits them for literal and non-linear patterns;
-- user-written guards always desugar to 'D.GuardExpr'), so it belongs
-- with the structural tests it accompanies. HNF emits each one
-- immediately after the 'D.GuardGetArg' that binds its fresh variable,
-- so in-order nesting preserves scoping. Second, every pattern test
-- gets an else branch that records whether the test failed because the
-- value it inspected was unbound — see 'inconclusiveElse'.
compileGuards ::
  Maybe Occurrence ->
  Maybe EqDispatch ->
  VarMap ->
  SrcInfo ->
  [D.Guard] ->
  Writer [Diagnostic CompileError] CompiledGuards
compileGuards mOcc mEq varMap si guards = do
  let (matchGuards, checkGuards) = partition isMatchGuard guards
      initial = MatchAcc {wrapper = id, varMap = varMap, dispatch = mEq}
  acc <- foldM (compileMatchGuard si) initial matchGuards
  (condMap, checkExpr) <- compileCheckGuards mOcc acc.varMap si checkGuards
  pure
    CompiledGuards
      { matchWrapper = acc.wrapper,
        indexConditions = condMap,
        residualCheck = checkExpr,
        extendedVarMap = acc.varMap
      }
  where
    isMatchGuard (D.GuardMatch {}) = True
    isMatchGuard (D.GuardGetArg {}) = True
    isMatchGuard (D.GuardEqual {}) = isJust mEq
    isMatchGuard _ = False

-- | Equation-dispatch context: everything 'compileMatchGuard' needs to
-- distinguish an /inconclusive/ pattern test (the inspected value was
-- an unbound logical variable, so no verdict is possible) from a
-- definite mismatch. Present only when compiling a user-defined
-- function's equations; 'Nothing' at rule-occurrence sites, where the
-- constraint store — not equation dispatch — decides what matches.
data EqDispatch = EqDispatch
  { -- | Boolean local set by the first inconclusive test in the
    -- procedure.
    flagVar :: Name,
    -- | Integer local holding the 1-based parameter index that test was
    -- reached through, or @0@ when unattributable.
    blockedArgVar :: Name,
    -- | Maps each in-scope pattern variable to the 1-based index of the
    -- function parameter it was extracted from. Seeded from the
    -- equation's parameters and extended by every 'D.GuardGetArg'.
    rootArgIndex :: Map.Map Text Int
  }

-- | Accumulator threaded through the match-guard fold: the wrapper
-- built so far, the 'VarMap' extended with the bindings the wrapper
-- introduces, and the equation-dispatch context (whose
-- 'rootArgIndex' grows as arguments are destructured).
data MatchAcc = MatchAcc
  { wrapper :: [Stmt] -> [Stmt],
    varMap :: VarMap,
    dispatch :: Maybe EqDispatch
  }

-- | The 1-based function parameter a pattern-test operand was reached
-- through, or @0@ when the operand is not a variable we tracked.
rootIndexOf :: Maybe EqDispatch -> R.Expr -> Int
rootIndexOf (Just eq) (R.VarExpr v) = Map.findWithDefault 0 v eq.rootArgIndex
rootIndexOf _ _ = 0

-- | Else branch for a failed pattern test in equation mode: if no
-- earlier test has already claimed the blame, and one of the values the
-- test inspected is an unbound logical variable, mark dispatch
-- inconclusive and remember which parameter blocked it.
--
-- Each scrutinee gets its own guarded assignment; because every one of
-- them is conditional on the flag still being unset, the first unbound
-- value encountered wins. Only variable operands are inspected — a
-- literal cannot be unbound.
--
-- The flag short-circuit only helps /after/ the flag is set, which
-- never happens on a call that eventually matches. So a call that
-- succeeds still pays one @__chr_is_unbound@ host call per equation it
-- had to reject — the shape of every list recursion
-- (@f([]) -> …; f([H|T]) -> …@ rejects the nil test on every cons
-- cell). Measured at +8% on @sum_list_test@. Lowering the test to a
-- 'YCHR.Internal.VM.BoolExpr' primitive would remove the host-call
-- overhead (registry lookup, argument list, exception frame, 'VBool'
-- box) in the Haskell interpreter; that was considered and declined in
-- favour of keeping the VM instruction set unchanged. Do not
-- "optimize" this into a new VM constructor without revisiting that
-- decision.
--
-- Outside equation mode this is empty, which is exactly the
-- fall-through behaviour rule occurrences and pre-existing code rely
-- on.
inconclusiveElse :: Maybe EqDispatch -> [(ValExpr, Int)] -> [Stmt]
inconclusiveElse Nothing _ = []
inconclusiveElse (Just eq) scrutinees = concatMap check scrutinees
  where
    check (e, idx) =
      [ If
          ( BAnd
              (BNot (BFromVal (Var eq.flagVar)))
              (BFromVal (HostCall chrIsUnboundName [e]))
          )
          [ AssignVal eq.flagVar (Lit (BoolLit True)),
            AssignVal eq.blockedArgVar (Lit (IntLit (fromIntegral idx)))
          ]
          []
      ]

-- | 'inconclusiveElse' specialized to a pattern test with a single
-- scrutinee, attributed to the parameter its operand was reached
-- through.
operandElse :: MatchAcc -> R.Expr -> ValExpr -> [Stmt]
operandElse acc operand e =
  inconclusiveElse acc.dispatch [(e, rootIndexOf acc.dispatch operand)]

compileMatchGuard ::
  SrcInfo ->
  MatchAcc ->
  D.Guard ->
  Writer [Diagnostic CompileError] MatchAcc
-- The pattern side of the native-bool fast path. HNF sees @true@ /
-- @false@ as ordinary 0-arity constructor patterns and emits a
-- 'D.GuardMatch' for them like any other, but their values are compiled
-- to 'BoolLit' (see 'compileTerm'), so a functor test would be asking
-- whether a 'VBool' is the atom @prelude__true@ — always false. Lower
-- the test to the boolean equality that matches the representation the
-- value side produces. The arity-0 restriction matters: an explicit
-- @prelude:true(X)@ is a different, undeclared constructor and keeps
-- the functor test.
compileMatchGuard si acc (D.GuardMatch operand name 0)
  | Just b <- Types.preludeBool name = do
      operandExpr <- compileExpr acc.varMap si operand
      let orElse = operandElse acc operand operandExpr
          check body = [If (BEqual operandExpr (Lit (BoolLit b))) body orElse]
      pure acc {wrapper = acc.wrapper . check}
compileMatchGuard si acc (D.GuardMatch operand name arity) = do
  -- HNF only emits 'GuardMatch' with a 'VarExpr' operand, but
  -- 'compileExpr' handles every 'Expr' constructor structurally, so
  -- delegating is safe and keeps the invariant unenforced-but-honoured.
  operandExpr <- compileExpr acc.varMap si operand
  let orElse = operandElse acc operand operandExpr
      check body = [If (BMatchTerm operandExpr (vmName name) arity) body orElse]
  pure acc {wrapper = acc.wrapper . check}
compileMatchGuard si acc (D.GuardGetArg vname operand idx) = do
  operandExpr <- compileExpr acc.varMap si operand
  let binding body = LetVal (Name vname) (GetArg operandExpr idx) : body
  pure
    acc
      { wrapper = acc.wrapper . binding,
        varMap = insertVar vname (Var (Name vname)) acc.varMap,
        -- The extracted variable is reached through the same top-level
        -- parameter as the compound it came out of.
        dispatch = inheritRootIndex vname operand <$> acc.dispatch
      }
-- Only reached in equation mode; rule occurrences keep routing
-- 'D.GuardEqual' through 'compileCheckGuards' (see 'compileGuards').
compileMatchGuard si acc (D.GuardEqual t1 t2) = do
  e1 <- compileExpr acc.varMap si t1
  e2 <- compileExpr acc.varMap si t2
  let isVarExpr (R.VarExpr _) = True
      isVarExpr _ = False
      scrutinees =
        [(e, rootIndexOf acc.dispatch t) | (t, e) <- [(t1, e1), (t2, e2)], isVarExpr t]
      orElse = inconclusiveElse acc.dispatch scrutinees
      check body = [If (BEqual e1 e2) body orElse]
  pure acc {wrapper = acc.wrapper . check}
compileMatchGuard _ acc _ = pure acc

-- | Propagate the root-parameter attribution of a destructured operand
-- to the variable bound to one of its arguments.
inheritRootIndex :: Text -> R.Expr -> EqDispatch -> EqDispatch
inheritRootIndex vname operand eq =
  eq {rootArgIndex = Map.insert vname (rootIndexOf (Just eq) operand) eq.rootArgIndex}

-- | Compile the check guards of an occurrence, classifying each one as
-- either a liftable index condition for a partner 'YCHR.Internal.VM.Foreach' or
-- a residual boolean check that stays at the innermost guard position.
--
-- The classification (paper §5.3, "Indexing" / Loop-Invariant Code
-- Motion in spirit) inspects each compiled equality with
-- 'classifyEqual'. Liftable equalities are routed to a per-partner map;
-- the rest are 'And'-folded in source order into the residual check.
compileCheckGuards ::
  Maybe Occurrence ->
  VarMap ->
  SrcInfo ->
  [D.Guard] ->
  Writer [Diagnostic CompileError] (PartnerCondMap, Maybe BoolExpr)
compileCheckGuards mOcc varMap si guards = do
  (condMap, residuals) <- foldM step (Map.empty, []) guards
  let residual = case residuals of
        [] -> Nothing
        r : rest -> Just (foldl BAnd r rest)
  pure (condMap, residual)
  where
    classify e1 e2 = case mOcc of
      Just occ -> classifyEqual occ e1 e2
      Nothing -> Nothing
    step (cm, rs) (D.GuardEqual t1 t2) = do
      e1 <- compileExpr varMap si t1
      e2 <- compileExpr varMap si t2
      case classify e1 e2 of
        Just (k, j, other) ->
          let cond = IndexCondition {argIndex = j, expectedValue = other}
           in pure (Map.insertWith (flip (++)) k [cond] cm, rs)
        Nothing ->
          pure (cm, rs ++ [BEqual e1 e2])
    step (cm, rs) (D.GuardExpr expr) = do
      e <- BFromVal . EvalDeep <$> compileExpr varMap si expr
      pure (cm, rs ++ [e])
    step acc _ = pure acc

-- ---------------------------------------------------------------------------
-- Compile body goals
-- ---------------------------------------------------------------------------

compileBodyGoals ::
  SymbolTable ->
  VarMap ->
  SrcInfo ->
  [D.BodyGoal] ->
  Writer [Diagnostic CompileError] [Stmt]
compileBodyGoals symTab varMap si goals = do
  (stmts, _) <- foldM step ([], varMap) goals
  pure stmts
  where
    step (acc, vm) goal = do
      (stmts, vm') <- compileBodyGoal symTab vm si goal
      pure (acc ++ stmts, vm')

-- | Tell-unify two terms and immediately drain the resulting
-- reactivation queue. Used by 'D.BodyUnify' and the re-binding case of
-- 'D.BodyIs'. Wrapped in a helper because the dispatch shape is not
-- something a casual reader should have to re-derive every time.
unifyAndReactivate :: ValExpr -> ValExpr -> [Stmt]
unifyAndReactivate l r =
  [ BoolExprStmt (BUnify l r),
    DrainReactivationQueue
      pendingName
      [ExprStmt (CallExpr reactivateDispatchName [AId (IdVar pendingName)])]
  ]

-- | Free variables that appear in /term position/ within an
-- expression — i.e. positions where 'compileTerm' will consume the
-- value structurally rather than evaluating it. Under non-evaluating
-- '=' every sub-expression of an '=' operand is a term position, so
-- this recurses through every compound shape ('CtorExpr',
-- 'CallExpr', 'HostExpr', 'ApplyExpr'). Used by
-- 'compileBodyGoal' for 'D.BodyUnify' to decide which fresh
-- 'NewVar's the unification itself must allocate before
-- 'compileTerm' sees an unbound name and raises @YCHR-40002@.
termPositionVars :: R.Expr -> [Text]
termPositionVars (R.VarExpr v) = [v]
termPositionVars (R.CtorExpr _ args) = concatMap termPositionVars args
termPositionVars (R.CallExpr _ args) = concatMap termPositionVars args
termPositionVars (R.HostExpr _ args) = concatMap termPositionVars args
termPositionVars (R.ApplyExpr f args) =
  termPositionVars f ++ concatMap termPositionVars args
termPositionVars _ = []

-- | Free variables inside a @quote(...)@ subtree of an /evaluated/
-- expression. A quote is a term position nested in an evaluating one:
-- 'compileExpr' hands the quoted subtree straight to 'compileTerm',
-- which consumes it structurally and raises @YCHR-40002@ on a name it
-- has not seen. A tell argument may therefore introduce a variable
-- under a quote, the way an '=' operand may introduce one anywhere —
-- and 'YCHR.Internal.Desugar.Disjunction' relies on it, since a
-- variable local to one branch first appears inside the quoted
-- disjunct call.
--
-- Deliberately narrower than 'termPositionVars': only what a quote
-- covers, and (at the call site) only for tell arguments. An unbound
-- name in an evaluated position elsewhere stays the error it is.
quotedTermVars :: R.Expr -> [Text]
quotedTermVars (R.CtorExpr (Types.Unqualified "quote") [arg]) =
  termPositionVars arg
quotedTermVars (R.CtorExpr _ args) = concatMap quotedTermVars args
quotedTermVars (R.CallExpr _ args) = concatMap quotedTermVars args
quotedTermVars (R.HostExpr _ args) = concatMap quotedTermVars args
quotedTermVars (R.ApplyExpr f args) =
  quotedTermVars f ++ concatMap quotedTermVars args
quotedTermVars _ = []

-- | Compile a single body goal, returning the generated statements and
-- an updated 'VarMap'. The VarMap may grow when a goal introduces new
-- variables (e.g. @is@ binding a fresh variable, or a constraint whose
-- arguments reference not-yet-seen variables that need 'NewVar').
compileBodyGoal ::
  SymbolTable ->
  VarMap ->
  SrcInfo ->
  D.BodyGoal ->
  Writer [Diagnostic CompileError] ([Stmt], VarMap)
compileBodyGoal _ varMap _ D.BodyTrue = pure ([], varMap)
-- 'YCHR.Internal.Desugar.Disjunction.lowerDisjunctions' runs in the
-- pipeline before this, and rewrites every 'D.BodyOr' into a tell of
-- @search:alt@; a query rejects @;@ outright. Reaching one here means
-- the lowering pass was skipped, not that the user wrote something the
-- compiler should diagnose.
compileBodyGoal _ _ _ (D.BodyOr _) =
  error "Compile.compileBodyGoal: BodyOr survived lowerDisjunctions"
compileBodyGoal _ varMap si (D.BodyTell qn args) = do
  -- A top-level bare 'VarExpr' in a tell argument refers to a logical
  -- variable that may not yet exist (e.g. 'foo(X)' on its first
  -- appearance); introduce a fresh 'NewVar' before evaluating the
  -- argument list. Variables nested inside a 'CallExpr' / 'CtorExpr'
  -- argument are evaluated by 'compileExpr', which runtime-errors if
  -- they are unbound. Tell arguments are evaluated, so the
  -- introduction is top-level only; contrast 'BodyUnify' below,
  -- whose operands are unification terms and may introduce variables
  -- under a 'CtorExpr' as well.
  -- 'nub' guards against repeated top-level 'VarExpr's like
  -- 'foo(X, X)' that would otherwise emit two consecutive 'LetVal
  -- X NewVar' (shadowing the first and leaking its allocation).
  let freshVars =
        nub
          [ v
          | v <- [v' | R.VarExpr v' <- args] ++ concatMap quotedTermVars args,
            notMemberVar v varMap
          ]
      newStmts = [LetVal (Name v) NewVar | v <- freshVars]
      varMap' = List.foldl' (\m v -> insertVar v (Var (Name v)) m) varMap freshVars
  callArgs <- traverse (compileExpr varMap' si) args
  let tellName = tellProcName (Types.qualifiedToName qn) (length callArgs)
  pure (newStmts ++ [ExprStmt (CallExpr tellName (map AVal callArgs))], varMap')
compileBodyGoal _ varMap si (D.BodyUnify t1 t2) = do
  -- '=' is pure structural unification: both operands are compiled as
  -- terms, not expressions. Function-call shapes ('CallExpr',
  -- 'HostExpr', 'ApplyExpr') do not evaluate — they become symbolic
  -- compounds via 'R.exprToTerm' + 'compileTerm'. The 'quote/1' quoting
  -- form is preserved as ordinary compound data here (no strip),
  -- matching head/equation patterns and the REPL's 'termToValue'.
  -- Mirrors the query-side 'Run.exprToValue' so '=' has the same
  -- semantics in rule bodies and queries. Use 'is' for arithmetic
  -- evaluation.
  --
  -- Any variable appearing anywhere inside an operand that is not yet
  -- in scope is introduced by the unification itself: it becomes a
  -- fresh logical variable slot that 'BUnify' then binds. 'nub' guards
  -- against repeated occurrences like 'X = X' that would otherwise
  -- allocate two 'NewVar's for the same name.
  let freshVars =
        nub [v | v <- termPositionVars t1 ++ termPositionVars t2, notMemberVar v varMap]
      newStmts = [LetVal (Name v) NewVar | v <- freshVars]
      varMap' = List.foldl' (\m v -> insertVar v (Var (Name v)) m) varMap freshVars
  t1' <- compileTerm varMap' si (R.exprToTerm t1)
  t2' <- compileTerm varMap' si (R.exprToTerm t2)
  pure (newStmts ++ unifyAndReactivate t1' t2', varMap')
compileBodyGoal _ varMap si (D.BodyHostStmt f args) = do
  args' <- traverse (compileExpr varMap si) args
  pure ([ExprStmt (HostCall (Name f) args')], varMap)
compileBodyGoal _ varMap si (D.BodyIs v expr) = do
  expr' <- compileExpr varMap si expr
  -- A bare-variable RHS (@R is X@) needs the dereferenced compound to
  -- be walked at runtime: emit 'EvalIs' to trigger 'deepEvalValue'.
  -- Any other RHS shape (host call, user function call, term ctor)
  -- already returns an evaluated value from its outer operation;
  -- 'EvalDeep' (deep-deref only) is sufficient. The type checker gates
  -- on the same syntactic shape (@body_is@ in
  -- @typechecker\/walk.chr@) — same pattern, same widening rule.
  let rhs = case expr of
        R.VarExpr _ -> EvalIs expr'
        _ -> EvalDeep expr'
  case lookupVar v varMap of
    -- Re-binding a variable already bound by the head: tell-unify so any
    -- existing constraints observing it are reactivated.
    Just existing -> pure (unifyAndReactivate existing rhs, varMap)
    -- First binding of this variable: an ordinary 'LetVal' is enough; no
    -- observers can exist yet.
    Nothing ->
      let varMap' = insertVar v (Var (Name v)) varMap
       in pure ([LetVal (Name v) rhs], varMap')
compileBodyGoal _ varMap si (D.BodyCall qn args) = do
  args' <- traverse (compileExpr varMap si) args
  let funcName = Types.qualifiedToName qn
  pure ([ExprStmt (CallExpr (funcProcName funcName (length args')) (map AVal args'))], varMap)
compileBodyGoal _ varMap si (D.BodyApply f args) = do
  fAndArgs <- traverse (compileExpr varMap si) (f : args)
  pure ([ExprStmt (CallExpr (callFunProcName (length args)) (map AVal fAndArgs))], varMap)

-- ---------------------------------------------------------------------------
-- Compile function definitions
-- ---------------------------------------------------------------------------

compileFunctionDef ::
  D.Function ->
  Writer [Diagnostic CompileError] Procedure
compileFunctionDef func = do
  let funcName = Types.qualifiedToName func.name
      procName' = funcProcName funcName func.arity
      params = [Name ("arg_" <> T.pack (show i)) | i <- [0 .. func.arity - 1]]
      funcLabel =
        Just
          ( "function "
              <> flattenName funcName
              <> "/"
              <> T.pack (show func.arity)
          )
      funcSi = SrcInfo func.equations.sourceLoc func.equations.parsed funcLabel
      frame =
        mkFrame
          ("function " <> flattenName funcName <> "/" <> T.pack (show func.arity))
          func.equations.sourceLoc
          func.equations.parsed
      -- Dispatch tracking: every equation's pattern tests record, in
      -- two procedure-level locals, whether a test failed only because
      -- the value it inspected was still unbound. Falling off the end
      -- of the procedure then reports insufficient instantiation
      -- instead of a definite mismatch — the ISO Prolog distinction,
      -- which matters for programs (a CHR-based type checker, say)
      -- whose data is full of unification variables.
      --
      -- A function whose every parameter is a plain variable or
      -- wildcard has no pattern test that could ever be inconclusive,
      -- so it gets neither the locals nor the branching tail. That
      -- exempts the hot path: the prelude's arithmetic and comparison
      -- functions, and any single-equation helper, are all in this
      -- class.
      tracksDispatch = any hasPatternTest func.equations.node
  eqStmts <- traverse (compileEquation tracksDispatch params funcSi) func.equations.node
  let fnLabel = flattenName funcName <> "/" <> T.pack (show func.arity)
      dispatchInit
        | tracksDispatch =
            [ LetVal inconclusiveName (Lit (BoolLit False)),
              LetVal blockedArgName (Lit (IntLit 0))
            ]
        | otherwise = []
      noMatchStmt =
        ExprStmt
          ( HostCall
              chrErrorName
              [Lit (AtomLit ("no matching equation in " <> fnLabel))]
          )
      errorStmt
        | tracksDispatch =
            If
              (BFromVal (Var inconclusiveName))
              [ ExprStmt
                  ( HostCall
                      chrInstErrorName
                      [Lit (AtomLit fnLabel), Var blockedArgName]
                  )
              ]
              [noMatchStmt]
        | otherwise = noMatchStmt
  pure
    Procedure
      { name = procName',
        params = params,
        body = PushFrame frame : dispatchInit ++ concat eqStmts ++ [errorStmt],
        procKind = PKFunction func.name func.arity
      }

-- | Build a VarMap for a function equation: maps each normalized parameter
-- variable to the corresponding procedure parameter name.
buildEquationVarMap :: [Name] -> [HeadArg] -> VarMap
buildEquationVarMap procParams normalizedArgs =
  varMapFromList
    [ (v, Var p)
    | (p, HeadVar v) <- zip procParams normalizedArgs
    ]

-- | Does this equation carry a pattern test that can fail? Guard
-- expressions do not count: a user-written guard is a decision about
-- values already in hand, so failing one is a definite mismatch rather
-- than an inconclusive dispatch.
hasPatternTest :: D.Equation -> Bool
hasPatternTest eq = any isPatternTest eq.guards
  where
    isPatternTest (D.GuardMatch {}) = True
    isPatternTest (D.GuardEqual {}) = True
    isPatternTest _ = False

-- | Compile one equation of a function into the statements that try it.
-- The 'Bool' is 'compileFunctionDef'\'s @tracksDispatch@: when 'False'
-- the enclosing procedure has no inconclusiveness locals, so pattern
-- tests must not reference them.
compileEquation ::
  Bool ->
  [Name] ->
  SrcInfo ->
  D.Equation ->
  Writer [Diagnostic CompileError] [Stmt]
compileEquation tracksDispatch params si eq = do
  let varMap = buildEquationVarMap params eq.params
      -- Attribute each pattern variable to the parameter it came from,
      -- so a failed test can name the argument that blocked dispatch.
      -- Wildcard parameters contribute nothing: they never fail a test.
      eqDispatch =
        EqDispatch
          { flagVar = inconclusiveName,
            blockedArgVar = blockedArgName,
            rootArgIndex =
              Map.fromList [(v, i) | (i, HeadVar v) <- zip [1 ..] eq.params]
          }
      mEqDispatch
        | tracksDispatch = Just eqDispatch
        | otherwise = Nothing
  -- Equations have no partners, so the index-condition pushdown
  -- classifier never fires; pass 'Nothing' to short-circuit it.
  compiled <- compileGuards Nothing mEqDispatch varMap si eq.guards
  (preludeStmts, varMap1) <-
    compilePrelude compiled.extendedVarMap si eq.prelude
  rhsExpr <- compileExpr varMap1 si eq.rhs
  let returnStmts = preludeStmts ++ [Return rhsExpr]
      inner = case compiled.residualCheck of
        Nothing -> returnStmts
        Just gExpr -> [If gExpr returnStmts []]
  pure (compiled.matchWrapper inner)

-- | Compile a function-body prelude: lower each 'D.FunStmt' to its VM
-- statements, threading the 'VarMap' so that an @X is E@ binding becomes
-- visible to later statements and to the trailing return expression.
-- Mirrors a subset of 'compileBodyGoal' but skips the rule-body-only
-- reactivation-on-rebind path: a function has no constraint store to
-- reactivate against. An @is@ that shadows a same-named parameter is
-- intentional and works via the host language's lexical scoping —
-- 'LetVal' lowers to a let binding that shadows the outer name for
-- the rest of the procedure body.
compilePrelude ::
  VarMap ->
  SrcInfo ->
  [D.FunStmt] ->
  Writer [Diagnostic CompileError] ([Stmt], VarMap)
compilePrelude varMap si = foldM step ([], varMap)
  where
    step (acc, vm) stmt = do
      (stmts, vm') <- compileFunStmt vm si stmt
      pure (acc ++ stmts, vm')

compileFunStmt ::
  VarMap ->
  SrcInfo ->
  D.FunStmt ->
  Writer [Diagnostic CompileError] ([Stmt], VarMap)
compileFunStmt varMap si (D.FunHostStmt f args) = do
  args' <- traverse (compileExpr varMap si) args
  pure ([ExprStmt (HostCall (Name f) args')], varMap)
compileFunStmt varMap si (D.FunIs v expr) = do
  expr' <- compileExpr varMap si expr
  let rhs = case expr of
        R.VarExpr _ -> EvalIs expr'
        _ -> EvalDeep expr'
      varMap' = insertVar v (Var (Name v)) varMap
  pure ([LetVal (Name v) rhs], varMap')
compileFunStmt varMap si (D.FunCall qn args) = do
  args' <- traverse (compileExpr varMap si) args
  let funcName = Types.qualifiedToName qn
  pure
    ( [ExprStmt (CallExpr (funcProcName funcName (length args')) (map AVal args'))],
      varMap
    )
compileFunStmt varMap si (D.FunApply f args) = do
  fAndArgs <- traverse (compileExpr varMap si) (f : args)
  pure
    ( [ExprStmt (CallExpr (callFunProcName (length args)) (map AVal fAndArgs))],
      varMap
    )

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
   in Procedure
        { name = reactivateDispatchName,
          params = [suspParamName],
          body = body,
          procKind = PKReactivateDispatch
        }
  where
    genDispatchBranch (ident, cType) =
      If
        (BIsConstraintType (IdVar suspParamName) cType)
        [ ExprStmt
            ( CallExpr
                (activateProcName ident.name ident.arity)
                [AId (IdVar suspParamName)]
            )
        ]
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
      -- Same distinction as function-equation dispatch, but the blocked
      -- position is static here: only the closure operand is ever
      -- pattern-tested, so the whole message is known at compile time.
      errorStmt =
        If
          (BFromVal (HostCall chrIsUnboundName [Var closureParam]))
          [ ExprStmt
              ( HostCall
                  chrInstErrorName
                  [ Lit
                      ( AtomLit
                          ( "'$call': closure argument is not sufficiently"
                              <> " instantiated (unbound variable)"
                          )
                      )
                  ]
              )
          ]
          [ExprStmt (HostCall chrErrorName [Lit (AtomLit "call: no matching closure")])]
   in Procedure
        { name = callFunProcName callArity,
          params = closureParam : argParams,
          body = funRefBranches ++ lambdaBranches ++ [errorStmt],
          procKind = PKCallDispatch callArity
        }

-- | Generate a dispatch branch for a function reference (@name/arity@).
-- Only emits a branch when the function's arity matches @callArity@.
genFunRefBranch :: Int -> [Name] -> D.Function -> [Stmt]
genFunRefBranch callArity argParams func
  | func.arity /= callArity = []
  | otherwise =
      let funcName = Types.qualifiedToName func.name
          flatName = flattenName funcName
          pName = funcProcName funcName func.arity
          condition =
            BAnd
              (BMatchTerm (Var (Name "closure")) (Name "/") 2)
              ( BAnd
                  (BEqual (GetArg (Var (Name "closure")) 0) (Lit (AtomLit flatName)))
                  ( BEqual
                      (GetArg (Var (Name "closure")) 1)
                      (Lit (IntLit (fromIntegral func.arity)))
                  )
              )
       in [ If
              condition
              [Return (CallExpr pName (map (AVal . Var) argParams))]
              []
          ]

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
      let funcName = Types.qualifiedToName func.name
          Name lambdaVmText = vmName funcName
          pName = funcProcName funcName func.arity
          -- The closure has 2 header fields (lambdaId, sourceForm) followed
          -- by the captured free variables, so its total arity is
          -- numCaptures + 2.
          condition =
            BAnd
              (BMatchTerm (Var (Name "closure")) (Name "__closure") (numCaptures + 2))
              (BEqual (GetArg (Var (Name "closure")) 0) (Lit (AtomLit lambdaVmText)))
          -- Captures are stored after the 2 header fields (lambdaId at
          -- index 0, sourceForm at index 1), so capture i lives at
          -- index i + 2.
          captureBinds =
            [ LetVal
                (Name ("cap_" <> T.pack (show i)))
                (GetArg (Var (Name "closure")) (i + 2))
            | i <- [0 .. numCaptures - 1]
            ]
          captureVars =
            [Var (Name ("cap_" <> T.pack (show i))) | i <- [0 .. numCaptures - 1]]
          allArgs = captureVars ++ map Var argParams
       in [ If
              condition
              ( captureBinds
                  ++ [Return (CallExpr pName (map AVal allArgs))]
              )
              []
          ]
  where
    numCaptures = func.arity - callArity

-- | Check if a function was generated by lambda lifting.
isLambdaFunc :: D.Function -> Bool
isLambdaFunc func = T.isPrefixOf "__lambda_" func.name.baseName

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

Why 'buildVarMap' only inspects 'HeadVar' arguments: occurrence head
arguments are 'HeadArg', so the only two cases are 'HeadVar' (binds a
name) and 'HeadWildcard' (contributes nothing). Non-variable patterns
have been lifted into 'D.GuardMatch' and 'D.GuardGetArg' guards by the
desugarer ('YCHR.Internal.Desugar.normalizeHead') and replaced with fresh
'HeadVar's in the head — the type-level narrowing makes that
invariant explicit instead of trusted by discipline.

Why the active constraint is called @active@ everywhere: at runtime
"constraint identifier" and "constraint suspension" are the same value
(a pointer to a heap-allocated 'YCHR.Internal.Runtime.Types.Suspension'). The
compiler picks the paper's terminology — "active constraint" — and uses
'activeName' as the single local-variable name in @tell_c@, @activate_c@,
and inside every @occurrence_c_j@ procedure. The only places that still
talk about a "suspension" are @reactivate_dispatch@ ('suspParamName')
and 'DrainReactivationQueue' ('pendingName'), where the value really is
"a suspension we received from somewhere else".

How 'compileExpr' handles compound forms: each 'D.Expr' constructor
maps to one runtime behavior. 'D.CallExpr' / 'D.ApplyExpr' /
'D.HostExpr' lower to 'CallExpr' / 'HostCall' (and their arguments
stay in expression context); 'D.CtorExpr' lowers to 'MakeTerm', with
its arguments recursively re-entered through 'compileExpr' so a
nested call inside @pair(foo(X), bar(Y))@ is still evaluated when
@foo@ is a declared function. The user opts out of this with
@quote\/1@: @quote(foo(X))@ delegates to 'compileTerm' on the surface
'Term' shape and keeps the subterm opaque regardless of whether
@foo@ happens to be a declared function. The call-vs-constructor
distinction was once made by a 'funSet' membership check at every
compound; it is now structural at the 'D.Expr' level
('YCHR.Internal.Resolve' commits to it once, in 'YCHR.Internal.Resolve.termToExpr').

Why 'genFireStmts' skips the alive check for removed partners during
backjumping: 'genKillStmts' has just emitted an unconditional 'Kill' for
every removed partner, so they are guaranteed dead by the time the body
runs. Emitting an alive check for them would always fail and the
resulting unconditional 'Continue' would make every later check
unreachable (paper §5.3, "all following alive tests thus becomes
redundant"). Backjumping is only useful for kept partners.

Why anonymous rules get a synthetic @__rule_N@ name in 'ruleOccurrences':
the propagation history is keyed on (rule name, constraint id tuple).
If two anonymous propagation rules shared a single placeholder name,
they would collide in the history and prevent each other from firing.
The synthetic name uses the rule's program-wide source position, which
is stable as long as the source order is.

Semantics of @quote(X)@ — the quoting operator:

@quote@ is a reserved keyword that prevents evaluation of its argument in
expression contexts (@is@ RHS, guard expressions, function arguments).
Normally, 'compileExpr' recursively evaluates recognised function calls
and host calls inside an expression; @quote(E)@ instead compiles @E@ via
'compileTerm', producing an opaque data term ('MakeTerm' \/ 'Lit' \/
'Var') regardless of whether @E@ contains function or operator names.

The effect is visible in three places:

  1. /Renamer/ ('YCHR.Internal.Rename.renameTerm'): inside @quote(...)@, the
     argument is renamed in 'NoResolve' mode, so functor names stay
     unqualified.  This means @quote(1 + 1)@ preserves the surface-level
     @+(1, 1)@ rather than producing the internal @prelude:+(1, 1)@
     representation.  Variables are still tracked (they need runtime
     bindings) but are not resolved against the module's declarations.

  2. /Compiler/ ('compileExpr'): the @quote\/1@ clause delegates to
     'compileTerm', which never emits 'CallExpr' or 'HostCall'.

  3. /REPL evaluator/ ('YCHR.Run.evalNestedExpr'): a parallel clause
     delegates to 'termToValue' instead of recursively evaluating.

@quote@ is forbidden as a user-defined constraint or function name
('YCHR.Internal.Resolve.checkReservedNames', error code YCHR-16003).

Example: @R is compound_to_list(quote(1 + 1))@ yields @R = [\'+\', 1, 1]@
because @1 + 1@ is compiled as the compound term @+(1, 1)@ instead of
being evaluated to @2@.

Why 'extractSymbolTable' lives in 'YCHR.Internal.Desugar' rather than here: the
constraint-type indices it produces are needed both by this module and
by 'YCHR.Internal.Compile.compile', but they are derivable from the desugared
program's rule heads together with its 'constraintTypes' map.
Computing them in the desugarer keeps the compilation pipeline
single-pass over the desugared AST.
--------------------------------------------------------------------------- -}
