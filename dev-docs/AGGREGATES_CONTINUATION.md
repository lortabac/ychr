# Aggregates: continuation notes

Working notes for finishing `docs/reference/aggregates.md`. Everything
but the aggregator typing is implemented: the core form, the predefined
aggregates (`forall/2` included), the selection forms, nested aggregates,
macros in aggregate goals, goal occurrences and the removal step. Keep
this file until typing lands; delete it then.

Phase I is on branch `nested-aggregates` (from `fb327d9`).

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
| I. nested aggregates, macros in goals, `forall/2` | **done**, branch `nested-aggregates` |

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
- **Nested aggregates.** The enclosing fold calls a nested aggregate's
  procedure in place (`wrapGoalConjuncts`, `FoldGoal`), with no soft
  guard of its own. The location phase skips it (`LocateGoal`). A
  nested goal's conjuncts are goal occurrences whose location phase
  loops the enclosing goals innermost first, one nest per level, each
  with its own distinctness tests. A nested `takemin`/`takemax` is
  `YCHR-40004`; a variable shared only with a later conjunct of the
  enclosing goal is `YCHR-40002`.
- A macro use inside an aggregate goal expands in place
  (`Rename.renameConjunct`). `YCHR-20043` is gone.

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
`reactivation_indexed_position`, for phase I `aggregates_forall`,
`aggregates_nested_not`, `aggregates_nested_select`,
`aggregates_nested_distinct`, `aggregates_nested_soft`,
`aggregates_nested_locate_output`, `aggregates_nested_element_head`,
`aggregates_nested_siblings`, `aggregates_select_nested` and
`aggregates_macro_in_goal`, plus the
negative `aggregates_element_unbound`, `aggregates_local_escapes`,
`aggregates_reserved_in_goal`, `aggregates_nested_take`,
`aggregates_nested_shared_later`, `aggregates_nested_select_escape`,
`constraint_use_aggregate_goal` and
`constraint_use_takemin_fact`. Each positive case runs on the Haskell
interpreter and the Scheme backend.

Unit cases: `test/YCHR/DesugarTest.hs` (`aggregates` group) and
`test/YCHR/CompileTest.hs` (`aggregate folds`, `aggregate result
patterns`, `aggregate goal occurrences`, `selection aggregates` and
`nested aggregates` groups).
`test/repl/test_repl.py` has the `:trace` case for a goal occurrence.

## What remains

### Aggregator typing

The checker side is done (M3 of the typing plan): `Encode.ruleHead`
carries the aggregates, `walk.chr` checks them (`agg_check`), and the
solver has levels on skolems, `link_unify` and `escape_check`. What is
left is the library typing (`libraries/aggregates.chr` is still
int-only, with `collect`, `exists` and `\+` over `any`) and the
goldens, then deleting this file. The notes below are from before that
work.

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
- A nested aggregate's positions need the same rules, with the enclosing
  goal's variables in scope at its goal-order place.

## Exact hook points (as of the phase I tip; line numbers drift)

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
| nested plans | `Compile/Aggregate.hs` `planAggregate`, `planNestedAggregates`; `AggregatePlan.planNested` |
| nested calls / levels | `Compile.hs` `GoalMode`, `levelLoopNames`; `Occurrences.hs` `aggregateGoals` |
| selection | `Compile.hs` `genSelectionBody`, `genSelectStmts`, `GoalLoopNames`; `Desugar/AggregateScope.hs` `selectionGoalVars` |
| shared / locals / binds, result HNF | `Desugar/AggregateScope.hs` `scopeAggregates` fills `D.aggShared`, `aggLocals`, `aggBinds`, `aggResult`; the compiler reads them |
| passivity exemption | `Compile/Passive.hs` `isPassive`, `aggregateRule` |
| constraint use | `ConstraintUse.hs` `checkConstraintUse.goalConstraints` |
| macros in goals | `Rename.hs` `renameConjunct` |
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
cd /home/lorenzo/Development/ychr/.worktrees/<branch>
CABAL_DIR=/home/lorenzo/Development/ychr/.cabal-home cabal build all
CABAL_DIR=/home/lorenzo/Development/ychr/.cabal-home cabal test
make format && make test-style
make test            # the python suites, including test-scheme
make mhs-build       # CI's MicroHs job; easy to forget, see below
make bench
```

Baseline at the phase I tip: `cabal test` 2402/2402, `test-style` 134,
`test-repl` 86, `test-typecheck` 21, `test-docs` 45, `test-stlc` 11,
`test-scheme` 866 passed / 3 skipped, `test-scheme-runtime` clean,
`make mhs-build` clean. `make bench`: ~29 µs (`aggregates_sum`),
~744 µs (`aggregates_many`), ~14 µs (`aggregates_no_match`), ~7.5 ms
(`aggregates_takemin_many`).
