{-# LANGUAGE OverloadedStrings #-}

-- |
-- Module      : YCHR.Internal.Compile
-- Description : Transforms a desugared CHR program into a VM program.
--
-- The Compiler is the transformation pass between the desugared
-- 'YCHR.Internal.Desugared.Program' and the abstract
-- 'YCHR.Internal.VM.Program' consumed by the backends and the
-- interpreter. It performs, in order:
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
-- 5. /@$call@ dispatch/: 'buildCallables' emits the program's callables
--    dispatch table — one entry per user-defined function and per lifted
--    lambda, keyed by the shape of the closure value that designates it.
--    Dynamic calls compile to the 'ApplyClosure' construct, which the
--    runtime resolves through that table in one lookup.
--
-- The basic compilation scheme is from paper §5.2; the Early Drop and
-- Backjumping optimizations are from §5.3 (Listing 8). Selective
-- Constraint Reactivation is implemented at the runtime level (the
-- observer pattern in 'YCHR.Internal.Runtime.Reactivation') — this pass only emits
-- 'DrainReactivationQueue' calls after each tell-side @Unify@.
--
-- Non-obvious design choices are documented in the @Note [...]@ blocks at
-- the bottom of this file; definitions reference them by title.
module YCHR.Internal.Compile
  ( -- * Errors
    CompileError (..),

    -- * Compilation
    compile,

    -- * Function compilation
    compileFunctionDef,

    -- * Call dispatch
    buildCallables,

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
import Data.List.NonEmpty qualified as NE
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe (fromMaybe, isJust, mapMaybe)
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
import YCHR.Internal.PExpr (PExpr (Atom))
import YCHR.Internal.Parsed (AnnP (..))
import YCHR.Internal.Parsed qualified as P
import YCHR.Internal.Pretty (prettyPExprSrc)
import YCHR.Internal.Resolved qualified as R
import YCHR.Internal.Types
  ( ConstraintKey (..),
    HeadArg (..),
    HeadConstraint (..),
    Identifier (..),
    SymbolTable,
    Term (..),
    flattenName,
    symbolTableToList,
  )
import YCHR.Internal.Types qualified as Types
import YCHR.Internal.VM
-- Hidden so '.head' resolves under MicroHs (dev-docs/MICROHS_GAPS.md, gap 1).
import Prelude hiding (head)

-- | Source location, original parsed expression, and optional context
-- label, extracted from an 'AnnP' wrapper.
data SrcInfo = SrcInfo
  { -- | Source location attached to the originating 'AnnP'.
    loc :: P.SourceLoc,
    -- | Pretty-printable parsed form, used to render diagnostics.
    parsed :: PExpr,
    -- | Optional context label (e.g. @"rule foo"@ or
    -- @"function bar/2"@) prefixed onto diagnostic messages.
    label :: Maybe Text
  }

-- ---------------------------------------------------------------------------
-- Public API
-- ---------------------------------------------------------------------------

-- | Compile a desugared program against the given constraint-type symbol
-- table. Returns 'Right' a 'YCHR.Internal.VM.Program' on success, or 'Left' the
-- accumulated errors. Errors from every sub-pass are collected before
-- the function decides to fail, so callers see as much detail as
-- possible in one go.
--
-- See Note [extractSymbolTable placement] for why the symbol table is
-- built by the desugarer rather than here.
compile :: D.Program -> SymbolTable -> Either [Diagnostic CompileError] Program
compile prog symTab =
  let (collected, occErrs) = runWriter (collectOccurrences symTab prog)
      occMap = collected.occurrenceMap
      ruleDisplayNames = collected.ruleDisplayNames
      (constraintProcs, procErrs) = runWriter $ do
        traverse (genConstraintProcs symTab occMap) (symbolTableToList symTab)
      procs = concatMap (.constraintProcedures) constraintProcs
      (funProcs, funErrs) = runWriter $ do
        traverse compileFunctionDef prog.functions
      -- One procedure per aggregate, nested ones included, in rule order.
      -- A rule without aggregates contributes nothing.
      aggregateWork =
        [ (display, rule, plan)
        | (display, rule, plans) <-
            zip3 ruleDisplayNames prog.rules collected.aggregatePlans,
          plan <- concatMap planTree plans
        ]
      planTree p = p : concatMap (planTree . snd) p.nested
      (aggProcs, aggErrs) = runWriter $ do
        traverse
          (\(display, rule, plan) -> genAggregateProcedure symTab display (rule, plan))
          aggregateWork
      dispatch = genReactivateDispatch symTab
      allErrs = occErrs ++ procErrs ++ funErrs ++ aggErrs
   in if null allErrs
        then
          Right
            Program
              { typeNames = buildTypeNames symTab,
                ruleNames = ruleDisplayNames,
                procedures = procs ++ funProcs ++ aggProcs ++ [dispatch],
                evaluables = buildEvaluables prog.functions,
                callables = buildCallables prog.functions,
                tellables = buildTellables prog,
                tellablesUnqualified = buildTellablesUnqualified prog,
                inertTypes = sortOn ctIndex (mapMaybe (.inertType) constraintProcs)
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
buildEvaluables :: [D.Function] -> [Evaluable]
buildEvaluables functions =
  [ Evaluable
      { key = EvaluableKey {functor = vmName funcName, arity = func.arity},
        procName = funcProcName funcName func.arity
      }
  | func <- functions,
    let funcName = Types.qualifiedToName func.name
  ]

-- | Build the dispatch table consumed by the runtime's closure-apply
-- construct. Each user-defined function contributes one entry mapping
-- the 'CallableKey' of its closure value — the term functor and
-- identity field the compiler bakes into @fun name\/arity@ and into a
-- lifted lambda's closure, plus the arity the callable was declared at
-- — to the mangled 'funcProcName' that resolves the compiled
-- procedure.
--
-- Ordinary functions and lifted lambdas need different keys because
-- their closures have different shapes (see 'CallableKey'): a function
-- reference identifies itself by its flattened source name and records
-- its arity, while a lambda closure identifies itself by the lifted
-- function's VM name and leaves its declared arity to the table. The
-- two identity encodings cannot collide: a flattened name always
-- contains @:@, which a lifted name never does.
--
-- The key is unique by construction. Function names and arities are
-- unique per declaration, and a lambda's VM name is unique per lambda.
buildCallables :: [D.Function] -> [Callable]
buildCallables functions =
  [ Callable {key, procName = funcProcName funcName func.arity}
  | func <- functions,
    let funcName = Types.qualifiedToName func.name,
    Just key <- [callableKey funcName func]
  ]
  where
    -- A lifted lambda whose 'lambdaArity' is unset contributes no
    -- entry: the runtime keys a lambda on the arity its source lambda
    -- declared, and only 'lambdaArity' records that. The desugarer sets
    -- it on every lambda it lifts, so this arm is unreachable. A table
    -- built before any closure exists cannot recover the arity by
    -- testing the closure term at run time.
    callableKey funcName func
      | isLambdaFunc func =
          ( \declaredArity ->
              CallableKey
                { functor = lambdaClosureFunctor,
                  identity = vmName funcName,
                  arity = declaredArity
                }
          )
            <$> func.lambdaArity
      | otherwise =
          Just
            CallableKey
              { functor = funRefFunctor,
                identity = Name (flattenName funcName),
                arity = func.arity
              }

-- | Build the dispatch table consumed by 'TellTerm', the dynamic
-- @tell\/N@. A module contributes entries only if one of its rule
-- bodies contains a dynamic tell, so a program that never uses one
-- pays nothing for the table at session start or library load.
--
-- Within such a module, every constraint it can name contributes its
-- qualified spelling, and the bare spelling as well when nothing else
-- visible — constraint or function — shares the name and arity: the
-- choice the renamer makes for a goal written in that module's source,
-- so a term told dynamically resolves as it would have statically. An
-- ambiguous bare name has no entry and is reported as not visible.
--
-- A bare name has two runtime spellings when it is not ASCII: a
-- compound's functor is 'vmName'-encoded, while an atom keeps the raw
-- name ('compileTerm'). Both are registered, so @tell(G)@ finds the
-- constraint whichever shape @G@ has.
--
-- The tier this builds is the scoped one. 'buildTellablesUnqualified'
-- adds the origin-less one a prelude rule's dynamic tell needs.
buildTellables :: D.Program -> [Tellable]
buildTellables prog =
  [ Tellable
      { key = TellableKey {scope = Just sc, functor = functor, arity = arity},
        procName = tellProcName (Types.qualifiedToName qn) arity
      }
  | sc <- Set.toList (tellScopes prog),
    ((n, arity), providers) <-
      Map.toList (Map.findWithDefault Map.empty sc prog.nameVisibility),
    qn <- providers,
    Map.member (ConstraintKey qn arity) prog.constraintTypes,
    functor <-
      vmName (Types.qualifiedToName qn)
        : concat [nub [vmName (Types.Unqualified n), Name n] | [_] <- [providers]]
  ]

-- | Build the origin-less tier of the dynamic @tell\/N@ dispatch: one
-- entry per constraint the program declares, keyed by its bare functor
-- and arity.
--
-- This is the tier a rule cannot reach through its own module's
-- visibility, because the goal it is handed was named by its caller. A
-- prelude rule such as @tell_list\/N@ is the motivating case: it is
-- compiled once, in a module that declares none of the constraints its
-- callers tell.
--
-- A constraint is included only when some scoped tier carries its bare
-- spelling, so the table holds exactly the pairs the renamer would
-- resolve as a bare name somewhere in the program — an unexported
-- constraint a module keeps to itself has no bare entry and stays
-- unreachable, as it must. A qualified goal never has an entry here:
-- it named its module, so the scoped lookup is the only tier that can
-- be right about whether that module is visible.
--
-- Two exported constraints of the same bare name and arity in
-- different modules are genuinely ambiguous here, and the runtime
-- reports that rather than resolving to whichever entry the map
-- happened to keep. One constraint registered under both its run-time
-- spellings — see 'buildTellables' — shares one procedure, so it stays
-- unambiguous.
buildTellablesUnqualified :: D.Program -> Map TellableKey TellableResolution
buildTellablesUnqualified prog =
  Map.map resolve (groupByPair candidates)
  where
    candidates :: [(TellableKey, (Name, Types.QualifiedName))]
    candidates =
      [ ( TellableKey {scope = Just (bareText qn), functor = name, arity = arity},
          (tellProcName (Types.qualifiedToName qn) arity, qn)
        )
      | (ConstraintKey qn arity, _) <- Map.toList prog.constraintTypes,
        Set.member (Name (bareText qn), arity) bareKeys,
        -- A non-ASCII name has two spellings, the same pair
        -- 'buildTellables' registers: the compound's encoded functor
        -- and the atom's raw one. Both are present, so a goal resolves
        -- whichever shape it has.
        name <-
          nub [vmName (Types.Unqualified (bareText qn)), Name (bareText qn)]
      ]

    bareKeys =
      Set.fromList
        [ (Name n, arity)
        | qns <- Map.elems prog.nameVisibility,
          ((n, arity), providers) <- Map.toList qns,
          [qn] <- [nub providers],
          Map.member (ConstraintKey qn arity) prog.constraintTypes
        ]

    -- Group by the goal a runtime looks up: the functor text and the
    -- arity. The first key of a group represents it; every other groups
    -- under the same (functor, arity) but may differ in the scope text
    -- only.
    groupByPair =
      Map.fromListWith
        (\new old -> old <> new)
        . map (\(key, entry) -> (key {scope = Nothing}, [(key, entry)]))

    resolve entries = case nub [procName | (_, (procName, _)) <- entries] of
      [procName] -> UniqueTell procName
      _ ->
        -- Sorted, not in the map's order, so the message does not depend
        -- on the grouping fold. The Scheme backend's registration
        -- renderer sorts the same spellings, so both runtimes print one
        -- order.
        AmbiguousTell
          ( sortOn
              (Types.flattenName . Types.qualifiedToName)
              [qn | (_, (_, qn)) <- entries]
          )

-- | The bare source name of a qualified constraint name, the text a
-- goal's functor carries for an unqualified reference.
bareText :: Types.QualifiedName -> Text
bareText (Types.QualifiedName _ n) = n

-- | The modules in which some rule body contains a dynamic tell: the
-- scopes the scoped 'tellables' tier carries entries for.
tellScopes :: D.Program -> Set Text
tellScopes prog =
  Set.fromList [sc | r <- prog.rules, sc <- concatMap goalScopes r.body.node]
  where
    goalScopes (D.BodyTellDynamic sc _ _) = [sc]
    goalScopes (D.BodyOr branches) = concatMap (concatMap goalScopes) (NE.toList branches)
    goalScopes _ = []

-- | Build the list of constraint type source names, indexed by
-- 'Types.ConstraintType'. The list is ordered by the constraint type's
-- integer index, so @typeNames !! i@ is the name of the type with index @i@.
buildTypeNames :: SymbolTable -> [Types.Name]
buildTypeNames symTab =
  [ ident.name
  | (ident, _) <- sortOn (ctIndex . snd) (symbolTableToList symTab)
  ]

-- | The integer a 'Types.ConstraintType' wraps, for ordering the
-- index-keyed lists in the program header.
ctIndex :: ConstraintType -> Int
ctIndex (ConstraintType i) = i

-- ---------------------------------------------------------------------------
-- Procedure generation for each constraint type
-- ---------------------------------------------------------------------------

-- | What compiling one constraint type contributes to the program.
data ConstraintProcs = ConstraintProcs
  { -- | Its @tell@, @activate@ and occurrence procedures.
    constraintProcedures :: [Procedure],
    -- | The type itself when it is inert, i.e. when it has no
    -- occurrence procedure to run — see 'Program'.'inertTypes'.
    --
    -- Today that is only ever the zero-occurrence case. The other
    -- half of the definition, "all of its occurrences are passive",
    -- cannot arise under the current analysis: both passivity sources
    -- ("YCHR.Internal.Compile.Passive") require the two heads to have
    -- the same type and leave the ωr-earlier occurrence of that type
    -- non-passive. A future source that does not could produce one,
    -- and it would still be inert by the same argument — an
    -- activation with no occurrence procedure to call.
    inertType :: Maybe ConstraintType
  }

-- | Generate the procedures for one constraint type: its @tell@, its
-- @activate@, and one occurrence procedure per non-passive occurrence.
-- The type is reported as inert when it has no occurrence to run.
genConstraintProcs ::
  SymbolTable ->
  OccurrenceMap ->
  ( Identifier,
    ConstraintType
  ) ->
  Writer [Diagnostic CompileError] ConstraintProcs
genConstraintProcs symTab occMap (ident, cType) = do
  -- Passive occurrences (paper §5.3, marked by 'YCHR.Internal.Compile.Passive')
  -- can never fire when this constraint is active, so we emit neither
  -- their occurrence procedure nor the call to it from activate. They
  -- keep their ωr numbers, so the surviving procedures' names are stable.
  let occs = filter (not . (.passive)) (lookupOccurrences ident occMap)
      tellProc = genTell ident.name cType ident.arity
      activate = genActivate ident.name cType ident.arity occs
  occProcs <- traverse (genOccurrence symTab occMap ident.name cType ident.arity) occs
  pure
    ConstraintProcs
      { constraintProcedures = tellProc : activate : occProcs,
        -- An activation with nothing to try is a no-op beyond the
        -- 'Store' that ends it, so nothing observes a binding of this
        -- constraint's arguments.
        inertType = if null occs then Just cType else Nothing
      }

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
        [ LetVal (argName i) (FieldArg (IdVar activeName) (ArgIndex (fromIntegral i)))
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
    -- A goal occurrence takes one more argument: the removal-step flag.
    -- 'activate_c' always calls it with 'false' (see 'genFireStmts' for
    -- the 'true' caller).
    genActivateCall occ =
      let occName = occProcName name arity occ.number
          callArgs = occCallArgs ++ [AVal (Lit (BoolLit False)) | isJust occ.goalOcc]
       in [ LetVal dropResultName (CallExpr occName callArgs),
            If (BFromVal (Var dropResultName)) [Return (Lit (BoolLit True))] []
          ]

-- ---------------------------------------------------------------------------
-- occurrence_c_j
-- ---------------------------------------------------------------------------

-- | Generate the @occurrence_c_j@ procedure for one occurrence of a
-- constraint type.
--
-- A goal occurrence (see 'GoalOccurrence') takes one more parameter, the
-- removal-step flag, and its body is built by 'genOccurrenceBody'.
genOccurrence ::
  SymbolTable ->
  OccurrenceMap ->
  Types.Name ->
  ConstraintType ->
  Int ->
  Occurrence ->
  Writer [Diagnostic CompileError] Procedure
genOccurrence symTab occMap name cType arity occ = do
  let params =
        activeName
          : argNames arity
          ++ [removalParamName | isJust occ.goalOcc]
      procName' = occProcName name arity occ.number
      varMap = buildVarMap occ
  body <- genOccurrenceBody symTab occMap cType varMap occ
  pure
    Procedure
      { name = procName',
        params = params,
        body = body,
        procKind =
          PKOccurrence cType occ.number.unOccurrenceNumber occ.ruleId occ.ruleDisplay
      }

-- | Map every user-written head variable in an 'Occurrence' to the
-- generated VM variable that holds its value (a @$X_i@ for the active
-- constraint, a @pArg_k_j@ for partner @k@). 'HeadWildcard' arguments
-- contribute no binding: wildcards are never referenced from guards
-- or bodies. See Note [Head variable extraction].
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
--
-- A goal occurrence is different: its active constraint is one conjunct
-- of an aggregate goal, so the loop nest is the rest of that goal (and
-- the enclosing goals) outside the head partner loops, and the active
-- conjunct's own guards are checked in place. See 'genGoalOccurrenceBody'.
genOccurrenceBody ::
  SymbolTable ->
  OccurrenceMap ->
  ConstraintType ->
  VarMap ->
  Occurrence ->
  Writer [Diagnostic CompileError] [Stmt]
genOccurrenceBody symTab occMap cType varMap occ = do
  (inner, condMap) <- genGuardedFire symTab occMap varMap occ
  body <-
    case occ.goalOcc of
      Nothing -> pure (wrapInPartnerLoops cType occ condMap inner)
      Just goal -> genGoalOccurrenceBody symTab cType goal condMap occ inner
  -- Push the rule frame at procedure entry, so it is live during guard
  -- evaluation (and the history check) as well as body execution. A guard
  -- that errors (e.g. evaluates to a non-boolean) then reports the rule's
  -- source location and label, just like a body error. The frame is scoped
  -- to this call: the interpreter restores the frames it found when the
  -- call returns, so it does not accumulate.
  pure (PushFrame (mkRuleFrame occ) : body ++ [Return (Lit (BoolLit False))])

-- | Compile the location phase of a goal occurrence: bind the active
-- conjunct's arguments, then nest the goal's conjuncts — the active one's
-- guards in their goal-order place, the others as loops — outside the head
-- partner loops.
--
-- The variable map that seeds the conjuncts holds only the active
-- conjunct's arguments. Every other goal variable — including one that
-- also occurs in a regular head — is bound by its own loop, because the
-- head loops are nested /inside/ these loops and their @pArg@ names do
-- not exist yet at this point. The spec allows this: the fire step
-- recomputes the aggregates from the regular heads and discards the
-- goal's bindings, so a pairing the goal does not really support is only
-- an extra try, never a wrong answer.
genGoalOccurrenceBody ::
  SymbolTable ->
  ConstraintType ->
  GoalOccurrence ->
  PartnerCondMap ->
  Occurrence ->
  [Stmt] ->
  Writer [Diagnostic CompileError] [Stmt]
genGoalOccurrenceBody symTab cType goal condMap occ fire = do
  let rule = occ.rule
      si =
        SrcInfo
          rule.head.sourceLoc
          rule.head.parsed
          (Just ("rule " <> occ.ruleDisplay))
      seed =
        varMapFromList
          [ (v, Var (argName i))
          | (i, HeadVar v) <- zip [0 ..] occ.activeArgs
          ]
      headLoops = wrapInPartnerLoops cType occ condMap fire
  -- One nest per goal level: the active conjunct's goal, then each
  -- enclosing goal from the innermost outward, then the head loops. Each
  -- level has its own loop names and its own distinctness tests, since
  -- two conjuncts only have to differ within one goal.
  --
  -- Going out one level, only the inner aggregate's shared inputs stay in
  -- the variable map. Everything else the inner goal bound is local to it,
  -- or is an output (a result, a selection's goal variables) whose value
  -- the fold takes from the whole goal and not from this match. Joining
  -- the outer goal on such a value could skip a combination the fold
  -- accepts.
  let depth = length goal.enclosing
      outer =
        [ (depth - 1 - i, LocateGoal Nothing, g, shared)
        | (i, g, shared) <- zip3 [0 ..] goal.enclosing goal.levelShared
        ]
      only shared vm = varMapFromList [(v, e) | v <- shared, Just e <- [lookupVar v vm]]
      nest [] _ = pure headLoops
      nest ((level, mode, conjuncts, shared) : more) vm =
        wrapGoalConjuncts
          symTab
          si
          (levelLoopNames goal.aggregateIndex level)
          mode
          conjuncts
          (only shared vm)
          (nest more)
  wrapGoalConjuncts
    symTab
    si
    (levelLoopNames goal.aggregateIndex depth)
    (LocateGoal (Just (goal.activeIndex, activeName, cType)))
    goal.conjuncts
    seed
    (nest outer)

-- | Compile the guards followed by the rule-firing block. Returns the
-- statements that go at the innermost partner-loop position — any HNF
-- match-guard wrappers (lets and structural @if@s introduced by
-- 'D.GuardMatch' / 'D.GuardGetArg') wrapped around the conditional
-- 'genFireStmts' result — together with the per-partner index
-- conditions lifted out of equality check guards by 'compileCheckGuards'.
--
-- A rule with aggregates extends the guard: one out-cell local per result
-- variable the aggregate binds is created here, the aggregate's procedure
-- is called from the guard condition, and the rule's own guard follows it.
-- Everything sits inside the match-guard wrapper, so a shared variable that
-- only the head's HNF guards bind is already in scope when the aggregate
-- reads it.
genGuardedFire ::
  SymbolTable ->
  OccurrenceMap ->
  VarMap ->
  Occurrence ->
  Writer [Diagnostic CompileError] ([Stmt], PartnerCondMap)
genGuardedFire symTab occMap varMap occ = do
  let AnnP {node = guards, sourceLoc = guardLoc, parsed = guardP} = occ.rule.guard
      ruleLabel = Just ("rule " <> occ.ruleDisplay)
      guardSi = SrcInfo guardLoc guardP ruleLabel
      AnnP {sourceLoc = headLoc, parsed = headP} = occ.rule.head
      headSi = SrcInfo headLoc headP ruleLabel
      cellStmts = concatMap aggregateOutCellStmts occ.aggregates
      -- The cells are in scope for the rule's guard as well as for the body:
      -- an aggregate's result is readable from both.
      varMapWithCells =
        List.foldl' aggregateOutCellVars varMap occ.aggregates
  compiled <- compileGuards (Just occ) Nothing varMapWithCells guardSi guards
  aggTests <-
    traverse (aggregateTest headSi compiled.extendedVarMap) occ.aggregates
  fire <- genFireStmts symTab occMap compiled.extendedVarMap occ
  let residual = fromMaybe (BLit True) compiled.residualCheck
      -- Aggregates are computed left to right, before the rule's own guard,
      -- and 'BAnd' short-circuits in the same order.
      condition = List.foldr BAnd residual aggTests
      guarded stmts = [If (softenGuard condition) stmts []]
      -- Late Storage, moved: a rule with aggregates stores its active
      -- constraint before computing them, so a fold sees the constraint
      -- being activated in its true store position and counts it once.
      -- The store is idempotent, and the partner loops have taken their
      -- snapshot before it, so storing the active cannot change the
      -- combinations they enumerate. A goal occurrence whose active
      -- constraint was already stored can match it as a regular head,
      -- which is allowed (goal distinctness never compares a goal
      -- conjunct with a head) and only an extra try, since the fold
      -- recomputes from the store. A goal occurrence may also be called
      -- by the removal step with a constraint that is already dead, so
      -- its store is liveness-guarded: a dead suspension must not enter
      -- the store, where a fold would count it.
      aggregateStoreStmts
        | null occ.aggregates = []
        | isJust occ.goalOcc =
            [If (BAlive (IdVar activeName)) [Store (IdVar activeName)] []]
        | otherwise = [Store (IdVar activeName)]
      -- Both checks are pure, so their order is unobservable; putting the
      -- history in front keeps a combination that already fired from
      -- refolding. Without aggregates the history check goes inside the
      -- guard.
      body = case (null occ.aggregates, fire.history) of
        (True, Nothing) -> guarded fire.stmts
        (True, Just (rid, ids)) ->
          guarded [If (BNotInHistory rid ids) (AddHistory rid ids : fire.stmts) []]
        (False, Nothing) ->
          aggregateStoreStmts ++ cellStmts ++ guarded fire.stmts
        (False, Just (rid, ids)) ->
          [ If
              (BNotInHistory rid ids)
              ( aggregateStoreStmts
                  ++ cellStmts
                  ++ guarded (AddHistory rid ids : fire.stmts)
              )
              []
          ]
  pure (compiled.matchWrapper body, compiled.indexConditions)

-- ---------------------------------------------------------------------------
-- Aggregates
-- ---------------------------------------------------------------------------

-- | The out-cell locals one aggregate's call needs: one fresh unbound
-- variable per variable it binds. The aggregate's procedure binds them, so
-- the rule's guard and body can read the results. A @takemin@\/@takemax@
-- gets one more, for the position of the match it selected, which the
-- firing needs to find that match again ('genSelectStmts').
aggregateOutCellStmts :: AggregatePlan -> [Stmt]
aggregateOutCellStmts plan =
  [LetVal (aggregateOutCell plan.position v) NewVar | v <- plan.bind]
    ++ [LetVal (selectionPosCell plan.position) NewVar | isTakePlan plan]

-- | The out-cells a call passes, in parameter order.
aggregateOutCellArgs :: AggregatePlan -> [CallArg]
aggregateOutCellArgs plan =
  [AVal (Var (aggregateOutCell plan.position v)) | v <- plan.bind]
    ++ [AVal (Var (selectionPosCell plan.position)) | isTakePlan plan]

-- | Extend a variable map with the cells one aggregate binds, so a later
-- aggregate and the rule's guard read its result.
aggregateOutCellVars :: VarMap -> AggregatePlan -> VarMap
aggregateOutCellVars vm plan =
  List.foldl'
    (\m v -> insertVar v (Var (aggregateOutCell plan.position v)) m)
    vm
    plan.bind

-- | The guard conjunct that computes one aggregate: a call to its procedure
-- inside 'BFromVal', so 'softenGuard' puts the whole fold under a soft
-- boundary and an instantiation error anywhere in it makes the aggregate
-- undefined instead of aborting the query.
--
-- The call's arguments are the out-cells the caller created, in the order
-- the procedure's parameters expect them, followed by the values of the
-- aggregate's shared variables.
aggregateTest ::
  SrcInfo ->
  VarMap ->
  AggregatePlan ->
  Writer [Diagnostic CompileError] BoolExpr
aggregateTest si varMap plan = aggregateCall si varMap plan (aggregateOutCellArgs plan)

-- | A call to an aggregate's procedure, as a boolean: the out-cells given,
-- then the values of the aggregate's shared variables from @varMap@.
aggregateCall ::
  SrcInfo ->
  VarMap ->
  AggregatePlan ->
  [CallArg] ->
  Writer [Diagnostic CompileError] BoolExpr
aggregateCall si varMap plan cells = do
  shared <- traverse sharedArg plan.shared
  pure (BFromVal (CallExpr plan.procName (cells ++ map AVal shared)))
  where
    -- A shared variable is in scope by construction (a head variable, or
    -- one the enclosing goal bound). A missing one is a compiler invariant
    -- violation, reported as an unbound variable rather than crashing.
    sharedArg v = case lookupVar v varMap of
      Just expr -> pure expr
      Nothing -> do
        tell [Diagnostic si.label (AnnP (UnboundVariable v) si.loc si.parsed) []]
        pure unreachableValue

-- | Generate the procedure that computes one aggregate, top-level or
-- nested.
--
-- Parameters: the out-cells the caller created (one per variable the
-- aggregate binds, plus a position cell for a @takemin@\/@takemax@), then
-- the values of the aggregate's shared variables. It returns a boolean —
-- @true@ when the aggregate is defined and its result pattern matched,
-- @false@ when it is undefined or did not.
--
-- For the core form the body evaluates the aggregator, folds the goal's
-- matches into a local working value, applies the aggregator's @Final@
-- closure, decodes the @maybe@ it returns, and matches the result pattern.
-- A selection form picks one match instead ('genSelectionBody'). Apart
-- from binding its out-cells the procedure is read-only: no store, kill,
-- history, tell or reactivation statement is reachable from it, which is
-- what lets an occurrence call it from inside a guard. See Note
-- [Guard-window bindings].
genAggregateProcedure ::
  SymbolTable ->
  Text ->
  (D.Rule, AggregatePlan) ->
  Writer [Diagnostic CompileError] Procedure
genAggregateProcedure symTab display (rule, plan) = do
  let outCount = length (aggregateOutCellArgs plan)
      outParams = [aggregateOutParam i | i <- [0 .. outCount - 1]]
      sharedParams =
        [aggregateSharedParam i | i <- [0 .. length plan.shared - 1]]
      params = outParams ++ sharedParams
      sharedMap = varMapFromList (zip plan.shared (map Var sharedParams))
      ruleLabel = Just ("rule " <> display)
      si = SrcInfo rule.head.sourceLoc rule.head.parsed ruleLabel
  body <-
    if isSelectionPlan plan
      then genSelectionBody symTab si sharedMap plan
      else genFoldBody symTab si sharedMap plan
  pure
    Procedure
      { name = plan.procName,
        params = params,
        body = body,
        procKind =
          PKFunction
            (Types.QualifiedName "$aggregate" plan.procName.unName)
            (length params)
      }

-- | The body of a core-form aggregate procedure: evaluate the aggregator,
-- fold the goal's matches, then decode and match the result.
genFoldBody ::
  SymbolTable ->
  SrcInfo ->
  VarMap ->
  AggregatePlan ->
  Writer [Diagnostic CompileError] [Stmt]
genFoldBody symTab si sharedMap plan = do
  -- Only a malformed aggregate has no aggregator, and that is reported by
  -- the renamer, so the placeholder never runs.
  aggExpr <- maybe (pure unreachableValue) (compileExpr sharedMap si) plan.agg
  foldStmts <-
    wrapGoalConjuncts
      symTab
      si
      (aggregateLoopNames plan.position)
      (FoldGoal plan.nested)
      plan.goal
      sharedMap
      $ \innermost -> do
        elementExpr <- compileExpr innermost si plan.element
        pure
          [ AssignVal
              aggregateAccName
              ( ApplyClosure
                  (Var aggregateIncName)
                  [Var aggregateAccName, elementExpr]
              )
          ]
  pure
    ( [ LetVal aggregateAggName aggExpr,
        If
          (BNot (BMatchTerm (Var aggregateAggName) aggregateAggFunctor 3))
          [ ExprStmt
              ( HostCall
                  chrErrorName
                  [ Lit
                      ( AtomLit
                          ( "aggregate: the Agg expression is not an"
                              <> " aggregator(Init, Inc, Final)"
                          )
                      )
                  ]
              )
          ]
          [],
        LetVal aggregateAccName (GetArg (Var aggregateAggName) 0),
        LetVal aggregateIncName (GetArg (Var aggregateAggName) 1),
        LetVal aggregateFinalName (GetArg (Var aggregateAggName) 2)
      ]
        ++ foldStmts
        ++ maybeValueStmts plan.resultMatch
    )

-- | The body of a selection procedure: walk the goal's matches in goal
-- order and keep the first one with the smallest (or largest) key.
--
-- The comparison is the prelude's @<@ (or @>@), strict, so a later match
-- with an equal key does not replace an earlier one. The first match is
-- compared with itself, so a key that is unbound, or that @<@ does not
-- accept, raises on the first match too and not only once there is a
-- second one. The call sits in a soft guard, so an instantiation error
-- makes the aggregate undefined.
--
-- When some match was found, the out-cells are bound to the kept match's
-- values, and for a @takemin@\/@takemax@ the last cell to its 1-based
-- position in goal order. With no match the rule does not apply.
genSelectionBody ::
  SymbolTable ->
  SrcInfo ->
  VarMap ->
  AggregatePlan ->
  Writer [Diagnostic CompileError] [Stmt]
genSelectionBody symTab si sharedMap plan = do
  let takes = isTakePlan plan
      cmp = Name (if selectsMax plan then ">" else "<")
      vals = zip [0 ..] plan.bind
      falseLit = Lit (BoolLit False)
      initStmts =
        [ LetVal selectionFoundName falseLit,
          LetVal selectionBestName falseLit
        ]
          ++ ( if takes
                 then
                   [ LetVal selectionCountName (Lit (IntLit 0)),
                     LetVal selectionPosName (Lit (IntLit 0))
                   ]
                 else []
             )
          ++ [LetVal (selectionValName i) falseLit | (i, _) <- vals]
      compareWith other =
        EvalDeep (HostCall cmp [Var selectionKeyName, other])
  loops <-
    wrapGoalConjuncts
      symTab
      si
      (aggregateLoopNames plan.position)
      (FoldGoal plan.nested)
      plan.goal
      sharedMap
      $ \innermost -> do
        key <- compileExpr innermost si plan.element
        values <- traverse (goalValue innermost) plan.bind
        let keep =
              [ AssignVal selectionFoundName (Lit (BoolLit True)),
                AssignVal selectionBestName (Var selectionKeyName)
              ]
                ++ [AssignVal (selectionValName i) e | (i, e) <- zip [0 ..] values]
                ++ [AssignVal selectionPosName (Var selectionCountName) | takes]
        pure
          ( [LetVal selectionKeyName key]
              ++ [AssignVal selectionCountName (increment selectionCountName) | takes]
              ++ [ If
                     (BNot (BFromVal (Var selectionFoundName)))
                     (ExprStmt (compareWith (Var selectionKeyName)) : keep)
                     [If (BFromVal (compareWith (Var selectionBestName))) keep []]
                 ]
          )
  let binds =
        [ BoolExprStmt (BUnify (Var (aggregateOutParam i)) (Var (selectionValName i)))
        | (i, _) <- vals
        ]
          ++ [ BoolExprStmt
                 ( BUnify
                     (Var (aggregateOutParam (length vals)))
                     (Var selectionPosName)
                 )
             | takes
             ]
  pure
    ( initStmts
        ++ loops
        ++ [ If
               (BFromVal (Var selectionFoundName))
               (binds ++ [Return (Lit (BoolLit True))])
               [Return (Lit (BoolLit False))]
           ]
    )
  where
    -- A visible goal variable is bound by the goal's own loops by
    -- construction. A missing one is a compiler invariant violation,
    -- reported as an unbound variable rather than crashing.
    goalValue vm v = case lookupVar v vm of
      Just e -> pure e
      Nothing -> do
        tell [Diagnostic si.label (AnnP (UnboundVariable v) si.loc si.parsed) []]
        pure unreachableValue

-- | @local + 1@, for a match counter.
increment :: Name -> ValExpr
increment n = HostCall "+" [Var n, Lit (IntLit 1)]

-- | The tail of an aggregate procedure: apply @Final@, decode the @maybe@
-- it returned, and match the result pattern against the payload.
--
-- The pattern's tests run first and a failed one returns @false@ (the rule
-- does not apply) before any out-cell is bound. A value that is neither
-- @just\/1@ nor @nothing@ is a runtime error naming the protocol: silently
-- treating it as undefined would turn a missing @library(maybe)@ import
-- into a rule that never fires.
maybeValueStmts :: ResultMatch -> [Stmt]
maybeValueStmts resultMatch =
  [ LetVal
      aggregateMaybeName
      (ApplyClosure (Var aggregateFinalName) [Var aggregateAccName]),
    If
      (BMatchTerm (Var aggregateMaybeName) aggregateJustFunctor 1)
      ( LetVal aggregatePayloadName (GetArg (Var aggregateMaybeName) 0)
          : matchedStmts
      )
      [ If
          (BEqual (Var aggregateMaybeName) (Lit aggregateNothingAtom))
          [Return (Lit (BoolLit False))]
          [ ExprStmt
              ( HostCall
                  chrErrorName
                  [ Lit
                      ( AtomLit
                          ( "aggregate: Final returned neither just(Result) nor"
                              <> " nothing, so it is not library(maybe)'s maybe"
                          )
                      )
                  ]
              )
          ]
      ]
  ]
  where
    -- Every test runs before any binding: a pattern that cannot match
    -- must leave the out-cells untouched. The tests are a short-circuiting
    -- 'BAnd' chain in pattern order, so a compound test precedes the field
    -- extractions that depend on it.
    matchedStmts =
      let bindAll =
            bindsStmts resultMatch.binds ++ [Return (Lit (BoolLit True))]
       in case resultMatch.tests of
            [] -> bindAll
            t : ts ->
              [ If
                  (List.foldl' BAnd t ts)
                  bindAll
                  [Return (Lit (BoolLit False))]
              ]

-- | The out-cell bindings a result match asks for, in the order the
-- procedure's out parameters were declared.
bindsStmts :: [(Text, ValExpr)] -> [Stmt]
bindsStmts binds =
  [ BoolExprStmt (BUnify (Var (aggregateOutParam i)) rhs)
  | (i, (_, rhs)) <- zip [0 ..] binds
  ]

-- | Wrap a block in the loops and the in-place guards that match a goal's
-- conjuncts, left to right, and hand the innermost block the variable map
-- in scope there.
--
-- A conjunct's own HNF guards are evaluated inside its loop, right after
-- its arguments are bound, so they filter candidates before the conjuncts
-- that follow are searched. Source order is the loop order: the first
-- conjunct's loop is the outermost.
--
-- A shared variable is an index condition on the conjunct's argument
-- position — evaluated before the loop body, so the iterator can skip
-- candidates without entering it — while a variable the goal binds is read
-- out of the candidate with @field-arg@. A variable bound by an earlier
-- conjunct is an index condition too, since it is in scope at this loop's
-- evaluation point.
--
-- @names@ picks the loop labels, the loop variables and the locals the
-- goal's variables are bound to, so that two nests in one procedure do not
-- clash (see 'GoalLoopNames'). @mode@ says what to do with @?@ guards and
-- nested aggregates (see 'GoalMode'), and in the location phase it names
-- the active conjunct of a goal occurrence when that is in this goal. Its
-- loop is not built — the active constraint already is it — but its own
-- guards are evaluated in place there, so a guard that compares a variable
-- of an earlier conjunct with a fresh name sees the earlier binding, and a
-- later conjunct sees whatever the active guards bound.
--
-- Two conjuncts of the same type inside one goal must match /different/
-- suspensions, like two head conjuncts of the same type. The fold needs
-- those tests as much as the location phase does, so that the two agree on
-- what a match is. A goal conjunct and a regular head are deliberately not
-- compared (see 'wrapInPartnerLoops').
wrapGoalConjuncts ::
  SymbolTable ->
  SrcInfo ->
  GoalLoopNames ->
  GoalMode ->
  [D.AggregateConjunct] ->
  VarMap ->
  (VarMap -> Writer [Diagnostic CompileError] [Stmt]) ->
  Writer [Diagnostic CompileError] [Stmt]
wrapGoalConjuncts symTab si names mode conjuncts varMap0 inner =
  go 0 [] varMap0 conjuncts
  where
    (locating, mActive) = case mode of
      FoldGoal _ -> (False, Nothing)
      LocateGoal m -> (True, m)

    go _ _ vm [] = inner vm
    go j seen vm (conjunct : rest) = case conjunct of
      D.AggConstraint hcon guards
        | Just (activeIdx, _activeSusp, _activeCType) <- mActive,
          j == activeIdx -> do
            -- The active conjunct: its constraint is the one being
            -- activated, so only its guards need compiling here. It is
            -- deliberately not added to @seen@: it has no loop variable,
            -- and distinctness against it is emitted from 'mActive'.
            compiled <- compileGuards Nothing Nothing vm si guards
            restStmts <- go (j + 1) seen compiled.extendedVarMap rest
            pure (compiled.matchWrapper (withResidual compiled restStmts))
        | otherwise -> do
            mCType <- lookupGoalCType symTab si hcon
            case mCType of
              -- The miss is already reported: keep going so the rest of the
              -- program still produces diagnostics.
              Nothing -> go (j + 1) seen vm rest
              Just cType -> do
                let suspName = names.loopSusp j
                    (conds, lettStmts, vm') =
                      bindGoalArgs names.loopLocal suspName vm hcon
                    distinct = distinctTests seen cType suspName
                compiled <- compileGuards Nothing Nothing vm' si guards
                -- The conjunct's HNF guards bind the variables they
                -- decompose (a compound or literal argument), and the
                -- conjuncts after this one, and the element, need those
                -- bindings.
                restStmts <-
                  go (j + 1) ((j, cType) : seen) compiled.extendedVarMap rest
                let body =
                      lettStmts
                        ++ compiled.matchWrapper
                          (withResidual compiled (guardedDistinct distinct restStmts))
                pure [Foreach (names.loopLabel j) cType suspName conds body]
      -- A @? Guard@ is checked in place: it sees the variables the conjuncts
      -- before it bound, and filters before the ones after it are searched.
      --
      -- The location phase drops every @?@ guard, so that it is a true
      -- over-approximation: a guard there could be inconclusive (a shared
      -- input is not bound yet, or a match's argument is still unbound) and
      -- skipping the combination would lose a firing that the fold, run
      -- later against a different store, would have found. The fold always
      -- evaluates the guard, and it reports a variable that is genuinely
      -- unbound at its goal-order position.
      D.AggGuard g
        | locating -> go (j + 1) seen vm rest
        | otherwise -> do
            compiled <- compileGuards Nothing Nothing vm si [g]
            restStmts <- go (j + 1) seen vm rest
            pure (compiled.matchWrapper (withResidual compiled restStmts))
      -- A nested aggregate is computed in place, once per partial match:
      -- the match goes on only if it is defined and its result matched,
      -- and what it binds is in scope for the conjuncts after it and for
      -- the element. The call is not soft-guarded here, so an
      -- instantiation error inside it makes the whole top-level aggregate
      -- undefined rather than dropping one match.
      --
      -- The location phase skips it, as it skips a @?@ guard: it is only a
      -- filter, and the fire step recomputes it. What it would bind is then
      -- unbound, so a later conjunct binds it as a local.
      D.AggNested _
        | FoldGoal nested <- mode,
          Just plan <- lookup j nested -> do
            let cells = [(v, nestedOutCell plan.path v) | v <- plan.bind]
                vm' = List.foldl' (\m (v, c) -> insertVar v (Var c) m) vm cells
            call <- aggregateCall si vm plan [AVal (Var c) | (_, c) <- cells]
            restStmts <- go (j + 1) seen vm' rest
            pure ([LetVal c NewVar | (_, c) <- cells] ++ [If call restStmts []])
        | otherwise -> go (j + 1) seen vm rest

    -- One @not (susp_j = susp_j')@ per earlier conjunct of the same type,
    -- plus one against the constraint being tried when that is a conjunct
    -- of this goal.
    distinctTests seen cType suspName =
      [ BNot (BIdEqual (IdVar suspName) (IdVar (names.loopSusp j')))
      | (j', cType') <- seen,
        cType' == cType
      ]
        ++ [ BNot (BIdEqual (IdVar suspName) (IdVar activeSusp))
           | Just (_, activeSusp, activeCType) <- [mActive],
             activeCType == cType
           ]

    guardedDistinct [] stmts = stmts
    guardedDistinct (c : cs) stmts = [If (List.foldl' BAnd c cs) stmts []]

    withResidual compiled stmts = case compiled.residualCheck of
      Nothing -> stmts
      Just cond -> [If cond stmts []]

-- | The names one nest of goal loops uses: the label of the loop over
-- conjunct @j@, the loop variable it binds, and the local a goal variable
-- is read into.
--
-- A fold and a goal occurrence's location phase use the aggregate names.
-- The firing of a @takemin@\/@takemax@ has its own labels and loop
-- variables, because its loops can sit inside the location loops of the
-- same aggregate, in the same procedure. 'loopLocal' only names the
-- direct constraint arguments: a variable an HNF guard pulls out of a
-- compound argument keeps its source name. Rebinding such a name there
-- is harmless, since nothing after the firing's loops reads it.
data GoalLoopNames = GoalLoopNames
  { loopLabel :: Int -> Label,
    loopSusp :: Int -> Name,
    loopLocal :: Text -> Name
  }

-- | The names a fold or a location phase uses for aggregate @k@. A goal
-- variable is read into a local of its own source name.
aggregateLoopNames :: Int -> GoalLoopNames
aggregateLoopNames k = GoalLoopNames (aggregateLabel k) aggregateSuspName Name

-- | The names the location phase uses for goal level @d@ of aggregate @k@.
-- Level 0, the top-level goal, keeps 'aggregateLoopNames'; a nested goal's
-- loops get names of their own, since they share one procedure with the
-- loops of the goals around it. A goal variable keeps its source name at
-- every level, so a variable shared across levels joins through the
-- variable map.
levelLoopNames :: Int -> Int -> GoalLoopNames
levelLoopNames k 0 = aggregateLoopNames k
levelLoopNames k d =
  GoalLoopNames (aggregateLevelLabel k d) (aggregateLevelSuspName d) Name

-- | How 'wrapGoalConjuncts' treats the conjuncts that are not loops.
data GoalMode
  = -- | A fold, or a take form's firing: every @?@ guard is checked, and
    -- every nested aggregate is computed in place with its plan, keyed by
    -- its position in the goal.
    FoldGoal [(Int, AggregatePlan)]
  | -- | A goal occurrence's location phase: @?@ guards and nested
    -- aggregates are skipped. Carries the active conjunct when it is in
    -- this goal: its position, the constraint being tried, and its type.
    LocateGoal (Maybe (Int, Name, ConstraintType))

-- | The names the firing uses to find selection @k@'s match again.
selectionLoopNames :: Int -> GoalLoopNames
selectionLoopNames k =
  GoalLoopNames (selectionLabel k) (selectionLoopSuspName k) (selectionLocalName k)

-- | Bind one goal conjunct's arguments against the candidate suspension:
-- index conditions for the values already in scope, @field-arg@ reads for
-- the variables the goal binds, nothing for a wildcard.
bindGoalArgs ::
  (Text -> Name) ->
  Name ->
  VarMap ->
  HeadConstraint ->
  ([IndexCondition], [Stmt], VarMap)
bindGoalArgs localName suspName vm0 hcon =
  List.foldl' step ([], [], vm0) (zip [0 ..] hcon.args)
  where
    step (conds, lets, vm) (i, arg) = case arg of
      HeadWildcard -> (conds, lets, vm)
      HeadVar v -> case lookupVar v vm of
        Just expr ->
          ( conds ++ [IndexCondition {argIndex = ArgIndex i, expectedValue = expr}],
            lets,
            vm
          )
        Nothing ->
          ( conds,
            lets ++ [LetVal (localName v) (FieldArg (IdVar suspName) (ArgIndex i))],
            insertVar v (Var (localName v)) vm
          )

-- | The constraint type of an aggregate-goal conjunct, reported like a head
-- constraint's when the type is unknown.
lookupGoalCType ::
  SymbolTable ->
  SrcInfo ->
  HeadConstraint ->
  Writer [Diagnostic CompileError] (Maybe ConstraintType)
lookupGoalCType symTab si hcon =
  case Types.lookupSymbol ident symTab of
    Just cType -> pure (Just cType)
    Nothing -> do
      tell
        [ Diagnostic
            si.label
            (AnnP (UnknownConstraintType ident.name) si.loc si.parsed)
            []
        ]
      pure Nothing
  where
    ident =
      Identifier
        (Types.qualifiedToName hcon.name)
        (length hcon.args)

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
-- The @if@ guard holds only the distinctness tests that can actually
-- fail: a test comparing the partner with a constraint of a different
-- type is statically true and is dropped. See @wrapOne@ below.
--
-- When @occ@ has no partners the inner block is returned unchanged.
wrapInPartnerLoops :: ConstraintType -> Occurrence -> PartnerCondMap -> [Stmt] -> [Stmt]
wrapInPartnerLoops activeCType occ condMap inner =
  -- Loops are built innermost-first by folding from the right, so the
  -- partner with the highest index ends up as the innermost loop and
  -- partner 0 as the outermost — matching the source order of the head.
  foldr wrapOne inner (zip [PartnerIndex 0 ..] occ.partners)
  where
    partnerTypes = [(k, p.cType) | (k, p) <- zip [PartnerIndex 0 ..] occ.partners]

    partnerCType :: PartnerIndex -> Maybe ConstraintType
    partnerCType j = lookup j partnerTypes

    wrapOne :: (PartnerIndex, Partner) -> [Stmt] -> [Stmt]
    wrapOne (k, partner) inside =
      let label = partLabel k
          suspVar = partSuspName k
          partArity = length partner.constraint.args
          conds = Map.findWithDefault [] k condMap
          -- Bind the partner's id and arguments as ordinary locals so
          -- the rest of the body can reference them by name. The id is
          -- the suspension itself: 'IdVar suspVar' is renamed to
          -- 'IdVar (partIdName k)' for symmetry with subsequent uses.
          fieldExtracts =
            LetId (partIdName k) (IdVar suspVar)
              : [ LetVal
                    (partArgName k j)
                    (FieldArg (IdVar suspVar) (ArgIndex (fromIntegral j)))
                | j <- [0 .. partArity - 1]
                ]
          -- The partner must be distinct from the active constraint and
          -- from every earlier partner: at most one suspension can play
          -- a given role in a rule firing. No alive checks here — the
          -- Foreach iterator guarantees yielded partners are alive, and
          -- the active constraint's liveness is verified after body
          -- execution (early drop / backjumping in 'genFireStmts').
          --
          -- Each test compares two suspension identifiers, and a
          -- suspension has exactly one identity: 'createConstraint' in
          -- both runtimes allocates ids from a monotone counter that
          -- backtracking does not rewind and that search forks share, so
          -- no two live suspensions — of the same type or not — ever
          -- share one. A test whose two sides are of *different*
          -- constraint types is therefore statically true and is not
          -- emitted at all. (When every test drops out the enclosing
          -- @if@ goes with them.) The surviving tests are exactly the
          -- same-type pairs, the only case where one suspension could be
          -- mistaken for another.
          -- Distinctness is only ever within one group. A goal
          -- occurrence's active constraint is not a head, and the spec
          -- lets a goal conjunct and a regular head be the same
          -- suspension (`task(T), \+ depends(T, _) \ depends(U, T)`), so
          -- the test against the active is suppressed for a goal
          -- occurrence. That can only add tries — the fire step
          -- recomputes and the history rejects a combination that
          -- already fired — never change which firings happen.
          distinctActive
            | isJust occ.goalOcc = []
            | partner.cType == activeCType =
                [BNot (BIdEqual (IdVar (partIdName k)) (IdVar activeName))]
            | otherwise = []
          distinctEarlier =
            [ BNot (BIdEqual (IdVar (partIdName k)) (IdVar (partIdName j)))
            | j <- [PartnerIndex 0 .. k - 1],
              partnerCType j == Just partner.cType
            ]
          guarded = case distinctActive ++ distinctEarlier of
            [] -> inside
            c : cs -> [If (List.foldl' BAnd c cs) inside []]
       in [Foreach label partner.cType suspVar conds (fieldExtracts ++ guarded)]

-- ---------------------------------------------------------------------------
-- Fire: history check + kill + body + early drop + backjumping
-- ---------------------------------------------------------------------------

-- | Compile a rule firing: the removal step, the history check and kills
-- for a propagation rule, Late Storage, the body goals, early drop, and
-- backjumping.
genFireStmts ::
  SymbolTable ->
  OccurrenceMap ->
  VarMap ->
  Occurrence ->
  Writer [Diagnostic CompileError] CompiledFire
genFireStmts symTab occMap varMap occ = do
  let rule = occ.rule
      activeIsRemoved = not occ.isKept
      isGoal = isJust occ.goalOcc
      killStmts = genKillStmts occ
      removalStmts = genRemovalStmts occMap occ
  let AnnP {node = ruleBody, sourceLoc = bodyLoc, parsed = bodyP} = rule.body
      ruleLabel = Just ("rule " <> occ.ruleDisplay)
      bodySi = SrcInfo bodyLoc bodyP ruleLabel
      headSi = SrcInfo rule.head.sourceLoc rule.head.parsed ruleLabel
  selectStmts <-
    concat
      <$> traverse
        (genSelectStmts symTab headSi varMap)
        (filter isTakePlan occ.aggregates)
  bodyStmts <- compileBodyGoals symTab varMap bodySi ruleBody
  let aliveCheck =
        If (BNot (BAlive (IdVar activeName))) [Return (Lit (BoolLit True))] []
      earlyDropStmts
        | activeIsRemoved = [Return (Lit (BoolLit True))]
        -- A removal-step call passes a constraint the firing already
        -- removed, so it is dead on entry and the liveness test would
        -- abandon every later combination of regular heads.
        | isGoal =
            [If (BFromVal (Var removalParamName)) [] [aliveCheck]]
        | otherwise = [aliveCheck]
      -- Backjumping (paper §5.3): after body execution, check each
      -- partner's liveness outermost-first.  If a partner died (e.g.
      -- killed by a rule fired during body execution), Continue to its
      -- Foreach loop to skip useless inner iterations.
      -- See Note [Backjumping skips removed partners] for why removed
      -- partners are omitted from these checks.
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
      -- the store before a non-empty body — or a removal step — runs: the
      -- body may tell constraints that need it as a partner, or unify
      -- variables it must be reactivated on, and a fold the removal step
      -- triggers has to see it. A removed active was just killed, and an
      -- empty body with nothing to retry observes nothing, so both leave
      -- storage to the end of @activate_c@. Sound only because guard
      -- residuals do not tell (dev-docs/INVARIANTS.md): nothing can mutate
      -- the store or bind variables while the constraint is alive but
      -- unstored. (The store can still be *read* in that window — a guard
      -- reaching @write_store_to_list@ through a host call will not list
      -- the active constraint; see INVARIANTS.md §Scope.)
      --
      -- A goal occurrence may be called by the removal step with a
      -- dead constraint, so its store is liveness-guarded.
      storeStmts
        | activeIsRemoved = []
        | null bodyStmts && null removalStmts = []
        | isGoal =
            [If (BAlive (IdVar activeName)) [Store (IdVar activeName)] []]
        | otherwise = [Store (IdVar activeName)]
      -- The rule frame is pushed at occurrence-procedure entry (see
      -- 'genOccurrenceBody'), so it is already on the call stack here.
      --
      -- The removal step is the first thing the body does, before its
      -- first goal, and runs for any rule that removes a constraint with
      -- goal occurrences.
      --
      -- A @takemin@\/@takemax@ finds its match again before anything is
      -- killed, so it sees the store its procedure saw in the guard.
      coreFireStmts =
        selectStmts
          ++ killStmts
          ++ storeStmts
          ++ removalStmts
          ++ bodyStmts
          ++ earlyDropStmts
          ++ backjumpStmts
  pure CompiledFire {history = ruleHistory occ, stmts = coreFireStmts}

-- | Find the suspensions of the match a @takemin@\/@takemax@ selected,
-- so the firing can kill them.
--
-- The procedure cannot hand a suspension back, so it hands back the
-- match's position in goal order instead, and this walks the same goal
-- again and stops there. Nothing has changed the store since the guard:
-- the guard is read-only, and the history write does not touch the store.
-- The loops are seeded with the shared inputs only, as the procedure's
-- are, so they enumerate the same matches in the same order. Counting is
-- exact where matching on the selected values would not be (a @NaN@ key
-- is not equal to itself).
--
-- One id local per constraint conjunct ('selectionIdName') is filled in.
-- They start as the active constraint only so they are bound. The loops
-- should always reach the position; if they don't (a host call in the
-- goal that is not pure could do that), it is a runtime error, so the
-- placeholder is never killed. A goal without a constraint conjunct
-- selects nothing to remove.
genSelectStmts ::
  SymbolTable ->
  SrcInfo ->
  VarMap ->
  AggregatePlan ->
  Writer [Diagnostic CompileError] [Stmt]
genSelectStmts symTab si varMap plan = case conjuncts of
  [] -> pure []
  first : _ -> do
    loops <-
      wrapGoalConjuncts
        symTab
        si
        (selectionLoopNames k)
        (FoldGoal plan.nested)
        plan.goal
        seed
        ( \_ ->
            pure
              [ AssignVal count (increment count),
                If
                  (BEqual (Var count) (Var (selectionPosCell k)))
                  ( [ AssignId (selectionIdName k j) (IdVar (selectionLoopSuspName k j))
                    | j <- conjuncts
                    ]
                      ++ [Break (selectionLabel k first)]
                  )
                  []
              ]
        )
    pure
      ( LetVal count (Lit (IntLit 0))
          : [LetId (selectionIdName k j) (IdVar activeName) | j <- conjuncts]
          ++ loops
          ++ [ If
                 (BNot (BEqual (Var count) (Var (selectionPosCell k))))
                 [ ExprStmt
                     ( HostCall
                         chrErrorName
                         [ Lit
                             ( AtomLit
                                 ( "takemin/takemax: the selected match is gone"
                                     <> " when the rule fires"
                                 )
                             )
                         ]
                     )
                 ]
                 []
             ]
      )
  where
    k = plan.position
    count = selectionCountLocal k
    conjuncts = selectionConjuncts plan
    -- The guard's call already reported a shared variable it could not
    -- find, so a missing one is skipped here.
    seed =
      varMapFromList
        [(v, e) | v <- plan.shared, Just e <- [lookupVar v varMap]]

-- | The positions of a selection's constraint conjuncts in its goal.
selectionConjuncts :: AggregatePlan -> [Int]
selectionConjuncts plan = [j | (j, D.AggConstraint _ _) <- zip [0 ..] plan.goal]

-- | What compiling one firing contributes: the propagation-history key the
-- rule fires under, if it keeps one, and the statements of the firing
-- itself. 'genGuardedFire' places the history guard, because a rule with an
-- aggregate has to run it before the folds.
data CompiledFire = CompiledFire
  { -- | 'Nothing' when the rule keeps no history: it removes a regular head,
    -- so the same combination of heads cannot match again anyway.
    history :: Maybe (RuleId, HistoryIds),
    stmts :: [Stmt]
  }

-- | The key a rule's firings are recorded under, or 'Nothing' when it keeps
-- none.
--
-- A rule keeps a history when it removes no regular head (a propagation
-- rule, as in ωr) /or/ when it has an aggregate: the spec fires an aggregate
-- rule at most once per combination of its regular heads whatever its kind,
-- so a later change in an aggregate's value must not fire it again.
ruleHistory :: Occurrence -> Maybe (RuleId, HistoryIds)
ruleHistory occ
  | null occ.rule.head.node.removed || not (null occ.aggregates) =
      Just (occ.ruleId, buildHistoryIds occ)
  | otherwise = Nothing

-- | Collect constraint identifiers for the propagation history tuple.
-- Each id is tagged with its head position and handed to
-- 'mkHistoryIds', which orders them, so that the same rule with the
-- same partner combination always produces an identical tuple
-- regardless of which occurrence is active (paper §5.2, Listing 1,
-- line 14).
--
-- A goal occurrence has no active regular head, so its tuple is built
-- from its regular-head partners alone — the same tuple the rule's
-- ordinary occurrences build for that combination.
buildHistoryIds :: Occurrence -> HistoryIds
buildHistoryIds occ =
  mkHistoryIds $
    [(idx, IdVar activeName) | Just idx <- [activeHeadPosition occ]]
      ++ [ (p.idx, IdVar (partIdName k))
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
    { label = label,
      sourceLoc = loc,
      sourceCode = T.pack (prettyPExprSrc pexpr)
    }

-- | Kill the constraint suspensions a firing removes: every removed
-- partner, the active constraint when it is removed, and the match each
-- @takemin@\/@takemax@ selected.
--
-- Two of these may be the same suspension (two take forms, or a take form
-- and a removed head, may pick the same constraint). A second 'Kill' does
-- nothing.
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
      selectionKills =
        [ Kill (IdVar (selectionIdName p.position j))
        | p <- occ.aggregates,
          isTakePlan p,
          j <- selectionConjuncts p
        ]
   in partnerKills ++ activeKill ++ selectionKills

-- | The removal step of a firing: for each removed regular head, in
-- textual order, and then for each constraint a @takemin@\/@takemax@
-- removed, in the order of the selection forms and then in goal order,
-- call every goal occurrence of its type with the removed constraint
-- (spec §3).
--
-- This is emitted for any rule whose firing removes a constraint with
-- goal occurrences, whether or not the rule has an aggregate: it is how
-- a `\+` in another rule notices its last match going away. Nothing is
-- added to the runtime 'Kill'.
--
-- The firing rule's own goal occurrences are included, so a dependency
-- chain is retried ("self-triggering") and a rule that removes a
-- constraint one of its own aggregates observes is tried again before
-- its body runs. The calls nest: a rule firing inside the removal step
-- has its own removal step.
--
-- The removed constraint is passed dead (already killed above), and the
-- goal-occurrence procedure's trailing flag tells it so: it must not be
-- stored, and no fold can count it, since it is no longer in the store.
genRemovalStmts :: OccurrenceMap -> Occurrence -> [Stmt]
genRemovalStmts occMap occ =
  concatMap
    oneHead
    (map dropPos (sortOn textualPos (removedHeads occ)) ++ selectionRemoved)
  where
    headNode = occ.rule.head.node

    dropPos (_, ident, idExpr, args) = (ident, idExpr, args)

    -- The textual position of a removed head, first field of an entry.
    textualPos (pos, _, _, _) = pos

    -- The constraints the take forms removed. Their fields are read off
    -- the (now dead) suspensions, which is allowed.
    selectionRemoved =
      [ ( Identifier (Types.qualifiedToName hc.name) (length hc.args),
          IdVar sel,
          [ FieldArg (IdVar sel) (ArgIndex (fromIntegral i))
          | i <- [0 .. length hc.args - 1]
          ]
        )
      | p <- occ.aggregates,
        isTakePlan p,
        (j, D.AggConstraint hc _) <- zip [0 ..] p.goal,
        let sel = selectionIdName p.position j
      ]

    -- (textual position, constraint identifier, id expression, argument
    -- expressions). Removed partners carry their loop variables; a
    -- removed active head is not in the partner list and is added by
    -- hand.
    removedHeads o =
      [ ( sourcePos p.idx,
          Identifier
            (Types.qualifiedToName p.constraint.name)
            (length p.constraint.args),
          IdVar (partIdName k),
          [Var (partArgName k j) | j <- [0 .. length p.constraint.args - 1]]
        )
      | (k, p) <- zip [PartnerIndex 0 ..] o.partners,
        not p.isKept
      ]
        ++ [ ( sourcePos o.activeIdx,
               Identifier o.conName (occurrenceArity o),
               IdVar activeName,
               [Var (argName j) | j <- [0 .. occurrenceArity o - 1]]
             )
           | not o.isKept
           ]

    -- 'ruleOccurrences' numbers the removed heads right-to-left
    -- ('HeadPosition' counts them in reverse), so a textual position is
    -- the reverse of the head position.
    sourcePos idx = length headNode.removed - 1 - idx.unHeadPosition

    -- A goal occurrence is never passive: 'YCHR.Internal.Compile.Passive.isPassive'
    -- exempts any rule whose head has an aggregate. It is deliberately
    -- not filtered here: should a future pass ever mark one passive, the
    -- call below would name a procedure that does not exist and the
    -- closed-procedure-name check would fail the compile loudly, where a
    -- filter would silently lose firings.
    oneHead (ident, idExpr, argExprs) =
      [ ExprStmt
          ( CallExpr
              (occProcName ident.name ident.arity target.number)
              (AId idExpr : map AVal argExprs ++ [AVal (Lit (BoolLit True))])
          )
      | target <- lookupOccurrences ident occMap,
        isJust target.goalOcc
      ]

-- ---------------------------------------------------------------------------
-- Compile terms
-- ---------------------------------------------------------------------------

-- | Placeholder for the value of an expression that already produced a
-- diagnostic. Compilation deliberately keeps collecting errors from
-- every sub-pass before it aborts, so this is only a well-formed
-- stand-in for a value that no successfully compiled program can
-- contain. (The query path in "YCHR.Run" drops the compile diagnostic
-- channel, so this is not a claim that no code path could ever read it.)
unreachableValue :: ValExpr
unreachableValue = Lit (AtomLit "")

-- | Lower a surface 'Term' to a VM 'ValExpr' in /term position/: no
-- function call is evaluated, so a compound becomes a 'MakeTerm' (or a
-- literal when it has arity 0). See Note [Anonymous variables].
compileTerm :: VarMap -> SrcInfo -> Term -> Writer [Diagnostic CompileError] ValExpr
compileTerm varMap si (VarTerm v) = case lookupVar v varMap of
  Just expr -> pure expr
  Nothing -> do
    tell [Diagnostic si.label (AnnP (UnboundVariable v) si.loc si.parsed) []]
    pure unreachableValue
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
compileTerm _ _ Wildcard = pure NewVar

-- | Lower a typed 'D.Expr' to a VM 'ValExpr'. Each constructor maps to
-- exactly one runtime behavior:
--
--   * 'D.CallExpr' produces a 'CallExpr'; 'D.HostExpr' a 'HostCall';
--     'D.ApplyExpr' an 'ApplyClosure', which resolves the closure
--     through the program's callables table at runtime.
--   * 'D.CtorExpr' produces a 'MakeTerm', with its arguments recursively
--     lowered. The native-bool fast path and the @quote\/1@ quoting form
--     are the only structural special cases.
--   * 'D.FunRefExpr' produces the canonical @'/'(<flatname>, <arity>)@
--     compound that 'buildCallables' keys the function-reference
--     entries on and the runtime reads back at a dynamic-call site.
--   * 'D.LambdaExpr' is removed by lambda lifting before compilation
--     and is therefore unreachable here.
--
-- See Note [Compound expression compilation] and Note [Quoting].
compileExpr ::
  VarMap ->
  SrcInfo ->
  D.Expr ->
  Writer [Diagnostic CompileError] ValExpr
compileExpr varMap si e = case e of
  R.VarExpr v -> case lookupVar v varMap of
    Just expr -> pure expr
    Nothing -> do
      tell [Diagnostic si.label (AnnP (UnboundVariable v) si.loc si.parsed) []]
      pure unreachableValue
  R.IntExpr n -> pure (Lit (IntLit n))
  R.FloatExpr n -> pure (Lit (FloatLit n))
  R.TextExpr s -> pure (Lit (TextLit s))
  -- See Note [Anonymous variables]: @_@ is an anonymous logical
  -- variable, so it lowers to a fresh 'NewVar' rather than to a
  -- non-binding wildcard value.
  R.WildcardExpr -> pure NewVar
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
    f' <- compileExpr varMap si f
    args' <- traverse (compileExpr varMap si) args
    pure (ApplyClosure f' args')
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
    goV (ApplyClosure f es) = Set.union (goV f) (Set.unions (map goV es))
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
  let activeNames = Set.fromList (argNames (occurrenceArity occ))
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
        [ (partArgName k j, (k, ArgIndex (fromIntegral j)))
        | (k, p) <- zip [PartnerIndex 0 ..] occ.partners,
          j <- [0 .. length p.constraint.args - 1]
        ]
asPartnerArg _ _ = Nothing

-- | Try to lift an @Equal a b@ check to an index condition on a partner
-- 'YCHR.Internal.VM.Foreach'. Returns @Just (k, cond)@ when exactly one
-- side is partner @k@'s argument @cond.argIndex@ and the other side's
-- free variables are all in scope at loop @k@'s evaluation point.
-- Returns @Nothing@ if neither side qualifies — in which case the
-- equality stays in the residual check expression.
classifyEqual ::
  Occurrence ->
  ValExpr ->
  ValExpr ->
  Maybe (PartnerIndex, IndexCondition)
classifyEqual occ a b
  | Just (k, j) <- asPartnerArg occ a,
    freeVars b `Set.isSubsetOf` inScopeBeforeLoop occ k =
      Just (k, IndexCondition {argIndex = j, expectedValue = b})
  | Just (k, j) <- asPartnerArg occ b,
    freeVars a `Set.isSubsetOf` inScopeBeforeLoop occ k =
      Just (k, IndexCondition {argIndex = j, expectedValue = a})
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
  checks <- compileCheckGuards mOcc acc.varMap si checkGuards
  pure
    CompiledGuards
      { matchWrapper = acc.wrapper,
        indexConditions = checks.indexConditions,
        residualCheck = checks.residualCheck,
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
-- Outside equation mode this is empty: a rule occurrence just falls
-- through.
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

-- | Compile one match guard into a wrapper that nests the enclosing
-- block inside the structural test it introduces. See 'compileGuards'
-- and 'EqDispatch'.
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
  case lookupVar vname acc.varMap of
    -- The variable is already in scope, so this decomposition is a test,
    -- not a binding: an aggregate goal's shared inputs are supplied by the
    -- caller, and a fresh local here would shadow the input and lose the
    -- agreement check. (HNF only emits a get-arg for a variable it has not
    -- seen, so in a head or an equation the variable is never in scope.)
    Just existing ->
      let check body = [If (BEqual existing (GetArg operandExpr idx)) body []]
       in pure acc {wrapper = acc.wrapper . check}
    Nothing ->
      let binding body = LetVal (Name vname) (GetArg operandExpr idx) : body
       in pure
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
  Writer [Diagnostic CompileError] CheckGuards
compileCheckGuards mOcc varMap si guards = do
  (condMap, residuals) <- foldM step (Map.empty, []) guards
  let residual = case residuals of
        [] -> Nothing
        r : rest -> Just (foldl BAnd r rest)
  pure CheckGuards {indexConditions = condMap, residualCheck = residual}
  where
    classify e1 e2 = case mOcc of
      Just occ -> classifyEqual occ e1 e2
      Nothing -> Nothing
    step (cm, rs) (D.GuardEqual t1 t2) = do
      e1 <- compileExpr varMap si t1
      e2 <- compileExpr varMap si t2
      case classify e1 e2 of
        Just (k, cond) ->
          pure (Map.insertWith (flip (++)) k [cond] cm, rs)
        Nothing ->
          pure (cm, rs ++ [BEqual e1 e2])
    step (cm, rs) (D.GuardExpr expr) = do
      e <- BFromVal . EvalDeep <$> compileExpr varMap si expr
      pure (cm, rs ++ [e])
    step acc _ = pure acc

-- ---------------------------------------------------------------------------
-- Compile body goals
-- ---------------------------------------------------------------------------

-- | Compile a rule-body goal list in order, threading the 'VarMap' so
-- later goals see the variables earlier ones bind.
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
-- 'D.BodyIs'.
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
  pure
    ( [ExprStmt (CallExpr (funcProcName funcName (length args')) (map AVal args'))],
      varMap
    )
compileBodyGoal _ varMap si (D.BodyApply f args) = do
  f' <- compileExpr varMap si f
  args' <- traverse (compileExpr varMap si) args
  pure ([ExprStmt (ApplyClosure f' args')], varMap)
compileBodyGoal _ varMap si (D.BodyTellDynamic sc g extras) = do
  -- The appended arguments are tell arguments, so they introduce
  -- variables the way 'D.BodyTell''s do: a top-level bare 'VarExpr'
  -- (an output argument, @tell(G, R)@) and any variable inside a
  -- @quote/1@. The goal itself is not an argument: a fresh variable
  -- there could only ever be an unbound goal, so it is left to the
  -- usual unbound-variable error; only variables quoted inside it are
  -- introduced (@tell(quote(inc(N, R)))@).
  let freshVars =
        nub
          [ v
          | v <-
              [v' | R.VarExpr v' <- extras]
                ++ concatMap quotedTermVars (g : extras),
            notMemberVar v varMap
          ]
      newStmts = [LetVal (Name v) NewVar | v <- freshVars]
      varMap' = List.foldl' (\m v -> insertVar v (Var (Name v)) m) varMap freshVars
  g' <- compileExpr varMap' si g
  extras' <- traverse (compileExpr varMap' si) extras
  pure (newStmts ++ [TellTerm sc g' extras'], varMap')

-- ---------------------------------------------------------------------------
-- Compile function definitions
-- ---------------------------------------------------------------------------

-- | Compile one user-defined function into a VM procedure: one
-- equation-trying block per equation, in source order, followed by the
-- fall-through error when none matches. Also used by 'YCHR.Run' to
-- compile the query-time lifted lambdas.
compileFunctionDef ::
  D.Function ->
  Writer [Diagnostic CompileError] Procedure
compileFunctionDef func = do
  let funcName = Types.qualifiedToName func.name
      procName' = funcProcName funcName func.arity
      params = [Name ("arg_" <> T.pack (show i)) | i <- [0 .. func.arity - 1]]
      fnLabel = flattenName funcName <> "/" <> T.pack (show func.arity)
      funcLabel = Just ("function " <> fnLabel)
      -- The function-entry frame takes the first equation's annotation:
      -- it is pushed before dispatch, so it cannot name one equation.
      (funcLoc, funcParsed) = case func.equations of
        (eq : _) -> (eq.sourceLoc, eq.parsed)
        [] -> (P.dummyLoc, Atom "function")
      frame = mkFrame ("function " <> fnLabel) funcLoc funcParsed
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
      tracksDispatch = any (hasPatternTest . (.node)) func.equations
      -- Every equation carries its own annotation, so a compile-phase
      -- diagnostic raised while compiling its body — an unbound
      -- variable, say — points at the equation that wrote it, including
      -- an `:- extend_function` equation from another module.
      eqSi (AnnP _ eqLoc eqParsed) = SrcInfo eqLoc eqParsed funcLabel
  eqStmts <-
    traverse
      (\eq -> compileEquation tracksDispatch params (eqSi eq) eq.node)
      func.equations
  let dispatchInit
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

-- | Compile one function-body prelude statement, threading the
-- 'VarMap'. Mirrors 'compileBodyGoal' without the reactivation-on-rebind
-- path: a function has no constraint store to reactivate against.
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
  f' <- compileExpr varMap si f
  args' <- traverse (compileExpr varMap si) args
  pure
    ( [ExprStmt (ApplyClosure f' args')],
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

-- | Check if a function was generated by lambda lifting.
isLambdaFunc :: D.Function -> Bool
isLambdaFunc func = T.isPrefixOf "__lambda_" func.name.baseName

{- Note [Head variable extraction]

'buildVarMap' only inspects 'HeadVar' arguments: occurrence head
arguments are 'HeadArg', so the only two cases are 'HeadVar' (binds a
name) and 'HeadWildcard' (contributes nothing). Non-variable patterns
have been lifted into 'D.GuardMatch' and 'D.GuardGetArg' guards by the
desugarer ('YCHR.Internal.Desugar.normalizeHead') and replaced with
fresh 'HeadVar's in the head — the type-level narrowing makes that
invariant explicit instead of trusted by discipline.
-}

{- Note [Active constraint naming]

The active constraint is called @active@ everywhere: at runtime
"constraint identifier" and "constraint suspension" are the same value
(a pointer to a heap-allocated
'YCHR.Internal.Runtime.Types.Suspension'). The compiler picks the
paper's terminology — "active constraint" — and uses 'activeName' as
the single local-variable name in @tell_c@, @activate_c@, and inside
every @occurrence_c_j@ procedure. The only places that talk about
a "suspension" are @reactivate_dispatch@ ('suspParamName') and
'DrainReactivationQueue' ('pendingName'), where the value really is
"a suspension we received from somewhere else".
-}

{- Note [Anonymous variables]

Source @_@ is the anonymous variable: outside a pattern position it is a
fresh logical variable, one per occurrence. HNF has already removed
every wildcard from a rule head or equation pattern before this pass
('Desugar.normalizeArg' / 'Desugar.decomposeArg' emit no operand for
one), so the only @_@ the compiler sees is in a term or evaluating
position — an @=@ operand, the contents of @quote(...)@, a tell
argument, a guard, or an @is@ right-hand side.

Both lowerings therefore allocate a variable rather than a
non-binding wildcard value: 'compileTerm' and 'compileExpr' emit
'NewVar' for each occurrence. The distinction is not cosmetic. A
constraint told with a real variable is registered as an observer of
it, so binding that variable later reactivates the constraint, whereas
a non-binding wildcard value has no cell to observe and would leave
the constraint asleep for ever.
-}

{- Note [Compound expression compilation]

Each 'D.Expr' constructor maps to one runtime behavior. 'D.CallExpr' /
'D.ApplyExpr' / 'D.HostExpr' lower to 'CallExpr' / 'HostCall' (and their
arguments stay in expression context); 'D.CtorExpr' lowers to
'MakeTerm', with its arguments recursively re-entered through
'compileExpr' so a nested call inside @pair(foo(X), bar(Y))@ is still
evaluated when @foo@ is a declared function. The user opts out of this
with @quote\/1@: @quote(foo(X))@ delegates to 'compileTerm' on the
surface 'Term' shape and keeps the subterm opaque regardless of whether
@foo@ happens to be a declared function. The call-vs-constructor
distinction is structural at the 'D.Expr' level
('YCHR.Internal.Resolve' commits to it once, in
'YCHR.Internal.Resolve.termToExpr').
-}

{- Note [Backjumping skips removed partners]

'genFireStmts' skips the alive check for removed partners during
backjumping: 'genKillStmts' has just emitted an unconditional 'Kill'
for every removed partner, so they are guaranteed dead by the time the
body runs. Emitting an alive check for them would always fail and the
resulting unconditional 'Continue' would make every later check
unreachable (paper §5.3, "all following alive tests thus becomes
redundant"). Backjumping is only useful for kept partners.
-}

{- Note [Quoting]

@quote@ is a reserved keyword that prevents evaluation of its argument
in expression contexts (@is@ RHS, guard expressions, function
arguments). Normally, 'compileExpr' recursively evaluates recognised
function calls and host calls inside an expression; @quote(E)@ instead
compiles @E@ via 'compileTerm', producing an opaque data term
('MakeTerm' \/ 'Lit' \/ 'Var') regardless of whether @E@ contains
function or operator names.

The effect is visible in three places:

  1. /Renamer/ ('YCHR.Internal.Rename.renameTerm'): inside @quote(...)@,
     the argument is renamed in 'NoResolve' mode, so functor names stay
     unqualified.  This means @quote(1 + 1)@ preserves the
     surface-level @+(1, 1)@ rather than producing the internal
     @prelude:+(1, 1)@ representation.  Variables are still tracked
     (they need runtime bindings) but are not resolved against the
     module's declarations.

  2. /Compiler/ ('compileExpr'): the @quote\/1@ clause delegates to
     'compileTerm', which never emits 'CallExpr' or 'HostCall'.

  3. /REPL evaluator/ ('YCHR.Run.evalNestedExpr'): a parallel clause
     delegates to 'termToValue' instead of recursively evaluating.

@quote@ is forbidden as a user-defined constraint or function name
('YCHR.Internal.Resolve.checkReservedNames', error code YCHR-16003).

Example: @R is compound_to_list(quote(1 + 1))@ yields
@R = [\'+\', 1, 1]@ because @1 + 1@ is compiled as the compound term
@+(1, 1)@ instead of being evaluated to @2@.
-}

{- Note [extractSymbolTable placement]

'extractSymbolTable' lives in 'YCHR.Internal.Desugar', not here. The
constraint-type indices come from the desugared program alone (its rule
heads and its 'constraintTypes' map), and they are needed outside this
module too: "YCHR.Internal.Compile.Pipeline" builds the table once,
passes it to 'compile', and keeps it on the compiled program for the
query path.
-}
