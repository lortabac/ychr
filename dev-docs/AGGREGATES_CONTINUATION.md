# Aggregates: continuation notes

Working notes for finishing `docs/reference/aggregates.md`. The core
form, the predefined aggregates, goal occurrences and the removal step
and the selection forms are implemented; what remains is nested
aggregates and the aggregator typing. Keep this file until the spec is fully
implemented; delete it then.

Branch `aggregates`, worktree `.worktrees/aggregates`, rebased onto
`master` (`e19fcd8`); phases 1 and A–G are done. Phase H is on branch
`selection-aggregates` (from `a85f36c`). A program that uses the core
form, a predefined aggregate or a selection form runs on both backends;
a nested aggregate is recognized, reported (`YCHR-40004`) and dropped,
so nothing compiles into a rule that never fires. `forall/2` is not defined
by `library(aggregates)` yet, because it needs a nested aggregate.

## Where the work stands

| Phase | State |
|---|---|
| 1. surface, AST, diagnostics | **done**, `4b3c25b` |
| A. goal HNF, lambda lifting into aggregates | **done**, `1098cf5` |
| B. the fold, gates | **done**, `9c426fb` |
| C. store visibility, history, escapes, passivity | **done**, `e2b6e1c` |
| D. `library(aggregates)` | **done**, `9c426fb` |
| E. goal occurrences | **done** |
| F. removal step | **done** |
| G. typing, docs, bench | **done** (typing documented as not implemented) |
| H. selection aggregates | **done**, branch `selection-aggregates` |
| I. nested aggregates | not started |

## What is implemented, and how it is pinned

- An aggregate folds its goal's matches in goal order into a local
  working value, applies the aggregator's `Final` closure, treats
  `nothing` as "the rule does not apply", and matches `Result`.
- `library(aggregates)` provides the core form and the macros
  `count/2`, `sum/3`, `prod/3`, `min/3`, `max/3`, `avg/3`,
  `collect/3`, `exists/1` and `\+/1`.
- A rule with aggregates fires at most once per combination of its
  regular heads, whatever its kind, and the constraint being activated
  is counted.
- **Goal occurrences.** Every CHR constraint conjunct of an aggregate
  goal is an occurrence of its type. The occurrence's loops are the
  goal's conjuncts, nested *outside* the regular-head partner loops; the
  active conjunct's own HNF guards are evaluated in its goal-order place.
  Every goal argument is a local in this phase (the head values are not
  bound yet), and the fire step recomputes the aggregates from the
  regular heads.
- **Removal step.** A rule that removes a constraint with goal
  occurrences calls one goal-occurrence procedure per removed head, in
  textual order, at the start of its body. The call passes the (dead)
  removed constraint and a trailing `$removal` flag; the procedure skips
  its early-drop test when the flag is set, and every store it performs
  is `BAlive`-guarded.
- A variable that only an aggregate's goal binds is reported as escaping
  (`YCHR-40003`) if the rule's guard or body reads it.
- A macro use inside an aggregate goal is reported as not implemented
  (`YCHR-20043`) instead of failing as an unknown constraint.

Golden cases: `aggregates_count`, `aggregates_sum`,
`aggregates_minmax`, `aggregates_collect`, `aggregates_exists_not`,
`aggregates_multi`, `aggregates_view_stored`,
`aggregates_view_removed`, `aggregates_goal_late`,
`aggregates_goal_self`, `aggregates_goal_distinct`,
`aggregates_goal_shadow`, `aggregates_goal_compound_shared`,
`aggregates_goal_hnf_scope`, `aggregates_goal_hnf_later`,
`aggregates_goal_guard_shared`, `aggregates_goal_guard_soft`,
`aggregates_goal_guard_removal`, `aggregates_goal_guard_bind`,
`aggregates_head_hnf_var`, `aggregates_result_literal`,
`aggregates_result_compound`, `aggregates_result_repeat`,
`aggregates_result_local_scope`,
`aggregates_removal_step`, `aggregates_many`, `aggregates_no_match`,
`hnf_arg_slot_shadow`, `hnf_source_var_named_hnf`, and for phase H
`aggregates_argmin`, `aggregates_argmax_tie`,
`aggregates_select_visible`, `aggregates_select_late`,
`aggregates_select_soft`, `aggregates_takemin_drain`,
`aggregates_takemax_once`, `aggregates_take_removal_step`,
`aggregates_takemin_many`, `aggregates_take_multi`,
`constraint_use_takemin_event` and
`reactivation_indexed_position`, plus the negative
`aggregates_element_unbound`, `aggregates_local_escapes`,
`aggregates_macro_in_goal`, `aggregates_reserved_in_goal`,
`aggregates_select_nested`, `constraint_use_aggregate_goal` and
`constraint_use_takemin_fact`. Each positive case runs on the Haskell
interpreter and the Scheme backend.

Unit cases: `test/YCHR/DesugarTest.hs` (`aggregates` group) and
`test/YCHR/CompileTest.hs` (`aggregate folds`, `aggregate result
patterns`, `aggregate goal occurrences` and `selection aggregates`
groups).
`test/repl/test_repl.py` has the `:trace` case for a goal occurrence.

## What remains

### Phase H — selection aggregates (done)

Two steps, because a procedure cannot hand a suspension back and the
guard must stay read-only:

- The selection procedure (`Compile.genSelectionBody`, same name and call
  site as a fold) keeps the first match with the best key and binds one
  out-cell per visible goal variable (`planBind`), plus the match's
  position for `take*` (`Names.selectionPosCell`).
- For `take*`, the firing walks the goal again before the kills
  (`Compile.genSelectStmts`), counting up to that position, and keeps the
  suspensions in `$selection_id_<k>_<j>`. `genKillStmts` kills them and
  `genRemovalStmts` adds them after the removed heads.
- `wrapGoalConjuncts` takes a `GoalLoopNames`, so the relocation loops
  (`selection_loop_<k>_<j>`) don't clash with a goal occurrence's own
  loops for the same aggregate.
- Fixed on the way: the Scheme store registered no observers for a type
  with an indexed position while it was below the index threshold
  (`scheme/ychr/store.sls`, pinned by `reactivation_indexed_position`).

### Phase I — nested aggregates

An aggregate's goal may itself contain aggregates (spec §Aggregate
goals). `Rename.renameAggregate` already parses them
(`AggNested`), and `Compile/Aggregate.checkSupported` reports and drops
them.

What the implementation has to add:

- `GoalOccurrence` already carries `goalEnclosing`, and
  `genGoalOccurrenceBody`/`wrapGoalConjuncts` concatenate it after the
  current goal, so the location phase's loop order is written. What is
  missing is the enclosing goals' *bindings*: with nesting, a goal
  occurrence belongs to one nested goal whose enclosing goal must be
  matched first to reach it.
- A nested aggregate contributes no loop of its own in the fold. It is
  computed in place for each partial match: the enclosing fold's
  innermost block calls the nested aggregate's procedure with the
  shared inputs bound there, and the nested result is in scope for the
  element (spec §Value of an aggregate, goal order). That needs a
  second `AggregatePlan` shape or a general "evaluate this aggregate
  here" helper `genAggregateProcedure` can call, plus the closure
  scoping the lifter already implements (`Desugar.liftAggregate`).
- `Aggregate.aggregateGoalLocals` already walks `AggNested`
  (`aggregateGoalLocals n.goal`), and `Rename` already recognizes a
  nested aggregate in a goal; the plan-side work is the main piece.
- Once nesting lands, `forall/2` can be defined in `libraries/aggregates.chr`
  as `\+ (G, \+ C)`.

### Aggregator typing

`docs/reference/type-system.md` §Aggregates describes the intended
rules. The two hook points are:

- `YCHR.Internal.TypeCheck.Encode.ruleHead` drops `h.aggregates`; the
  encoded head has to carry them.
- `typechecker/skel.chr`'s `collect_vars_rule` only sees variables that
  reach it through the guard or body, so an aggregate-bound variable
  gets an ordinary flexible slot. The aggregate's own positions
  (`Agg`, `Element`, `Goal`, `Result`) never reach the checker.
- The integer folds (`sum`, `prod`, `min`, `max`, `avg`) are
  integer-typed until overloaded helpers exist; `libraries/aggregates.chr`
  declares them that way.

## Exact hook points (as of the phase G tip; line numbers drift)

| What | Where |
|---|---|
| the goal-occurrence record | `Compile/Types.hs` `GoalOccurrence`, `Occurrence.goalOcc`, `activeHeadPosition` |
| emitting goal occurrences | `Compile/Occurrences.hs` `ruleOccurrences`, `mkGoalOccurrence`, `resolvePartners` |
| the location phase | `Compile.hs` `genOccurrenceBody`, `genGoalOccurrenceBody`, `wrapGoalConjuncts` |
| the fold | `Compile.hs` `genAggregateProcedure`, `wrapGoalConjuncts`, `withGoalNest` is gone |
| distinctness | `Compile.hs` `wrapGoalConjuncts` (`distinctTests`), `wrapInPartnerLoops` |
| the fire step | `Compile.hs` `genGuardedFire`, `genFireStmts` (store/early drop/removal), `buildHistoryIds` |
| the removal step | `Compile.hs` `genRemovalStmts` |
| the removal flag | `Compile/Names.hs` `removalParamName` |
| gates | `Compile/Aggregate.hs` `checkSupported`, `checkLocalEscapes` |
| selection | `Compile.hs` `genSelectionBody`, `genSelectStmts`, `GoalLoopNames`; `Aggregate.hs` `selectionGoalVars` |
| passivity exemption | `Compile/Passive.hs` `isPassive`, `aggregateRule` |
| constraint use | `ConstraintUse.hs` `checkConstraintUse.goalConstraints` |
| the macro-in-goal gate | `Rename.hs` `renameConjunct`, `Display.hs` `renameErrorCode`/`renameErrorMsg` |
| the library | `libraries/aggregates.chr` |

## Facts that cost time to establish

- **No new VM instruction is needed.** `CallExpr` is already a
  `ValExpr`, so `BFromVal (CallExpr aggProc sharedVars)` puts a whole
  `Foreach` fold inside a `BSoftGuard`.
- **`unify'` binds its left operand and returns that operand's
  observers** (`Runtime/Var.hs`), so every out-cell `bunify` puts the
  cell on the left and enqueues no reactivation.
- **Local variables are not trailed**; `Foreach` has no per-iteration
  undo and iterates an immutable store snapshot, so a later tell is
  invisible to a running fold.
- **Generated locals must be unspellable in source.** The runtime
  environment is flat per invocation, so a source variable named
  `X_0` shadows a local of the same name. `argName` therefore emits
  `$X_i`, not `X_i`, and HNF's fresh names are `$hnf_N` for the same
  reason; every other generated local is either `$`-prefixed
  (`$aggregate_susp_`, `$removal`, the out-cells) or starts lowercase
  (`pArg_k_j`, `active`, `dropped`), and a source variable is
  `[A-Z_][A-Za-z0-9_]*`, so none of them collides. A future pass that
  introduces a local must keep that property.
- **The location phase is a strict over-approximation: it drops every
  `?` guard.** It runs outside the regular-head loops, so a shared input
  is not bound yet, and a matched argument may still be unbound; either
  way a guard there can be inconclusive, and skipping the candidate
  would lose a firing that the fold, run later against a different store
  (a removal can make it defined), would have found. The fold evaluates
  every guard, so the fire step is what enforces them.
- **The result pattern's tests must run before its bindings.** The
  aggregate procedure does this in `maybeValueStmts`; a literal,
  compound or repeated variable is a test, and only a not-yet-bound
  variable is bound.
- **An inert type registers no observers**, which is why a type with
  goal occurrences must not be inert.
- **`storeConstraint` on a dead suspension inserts it.** Every store a
  goal occurrence can reach is `BAlive`-guarded for that reason, and a
  dead constraint must not be counted by a fold.
- **HNF sees variables in goal order**, so a conjunct's guards only
  reference variables it binds itself or that an earlier conjunct bound.
  That is why the location phase evaluates the active conjunct's guards
  between the conjuncts before it and the ones after it, not before all
  of them.
- **A library content edit is not always re-spliced**: remove the
  component's build directory and rebuild
  (`rm -rf dist-newstyle/build/*/ghc-*/ychr-*/x/ychr; cabal build exe:ychr`),
  or edit `embed/YCHR/Embedded/StdLib.hs`.
- **`make format` does not enforce the 95-column limit** that
  `test-style` checks; run `test-style` after formatting.
- Guile 3 is `/usr/bin/guile3.0`; `make test-scheme` resolves it by
  name, so `PATH` must include `/usr/bin`.
- **`make mhs-build` is a CI gate too.** The aggregates work broke it
  twice with the constructs `dev-docs/MICROHS_GAPS.md` records: a record
  update on a selector chain (`rule.head {node = …}`, gap 3) and a
  `.head` field access in a module that does not hide `Prelude.head`
  (gap 1). Check `make mhs-build` after touching `src/`.

## Verification recipe

```sh
cd /home/lorenzo/Development/ychr/.worktrees/aggregates
CABAL_DIR=/home/lorenzo/Development/ychr/.cabal-home cabal build all
CABAL_DIR=/home/lorenzo/Development/ychr/.cabal-home cabal test
make format && make test-style
make test            # the python suites, including test-scheme
make mhs-build       # CI's MicroHs job; easy to forget, see below
make bench
```

Baseline at the phase G tip (rebased onto `master`): `cabal test`
2357/2357, `test-style` 134, `test-repl` 86, `test-typecheck` 21,
`test-docs` 44, `test-stlc` 11, `test-scheme` 830 passed / 3 skipped,
`test-scheme-runtime` clean.
`make bench` runs; the aggregate cases measure ~32 µs
(`aggregates_sum`), ~943 µs (`aggregates_many`) and ~14 µs
(`aggregates_no_match`).
