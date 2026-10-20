# Aggregates: continuation notes

Working notes for finishing `docs/reference/aggregates.md`. Everything
is implemented except the last typing step: the core form, the
predefined aggregates (`forall/2` included), the selection forms,
nested aggregates, macros in aggregate goals, goal occurrences, the
removal step, and now the type checker's side of aggregate typing. What
is left is M4 below: type `library(aggregates)` properly, add the
goldens, update PROJECT.md and the roadmap, and delete this file.

The typing work is on branch `aggregate-typing`, in the worktree
`.worktrees/aggregate-typing` (off master `60703e2`). Its plan, with the
decisions taken with the user and the review history, is
`~/.claude-personal/plans/the-implementation-of-aggregates-pure-pizza.md`.
The spec is `docs/reference/type-system.md` §Aggregates plus
`docs/reference/aggregates.md` §Typing. Where the plan and the spec
differ, the spec wins.

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
| T-M1. typing spec | **done**, `cffd5de`, `96e80ad` |
| T-M2. explicit binders on `D.Aggregate` | **done**, `21731b1` |
| T-M3. the checker | **done**, `334ee89` |
| T-M4. library typing, goldens, cleanup | **next** |

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
- **Typing (M3).** The checker types every aggregate position: `Agg`
  as `aggregator(W, E, R)` in the enclosing scope, the goal and
  `Element` one level deeper, the result tests back in the enclosing
  scope. Skolems carry a level, shared names are linked one way, a
  per-match type that reaches the rule is YCHR-60014, a goal type tied
  to two outer ones is YCHR-60015, and a goal that can never match is
  the warning YCHR-20106. Pinned by
  `test/golden/aggregates_typed_aggregator` only, until M4 adds the
  rest.
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

## What remains: M4

Pause for the user's review when M4 is done, as for every milestone.

### 1. `libraries/aggregates.chr`

Today the specs are int-only, and `count`, `collect`, `exists` and `\+`
are typed over `any`. Change them to:

- `count_spec() -> aggregator(int, A, int)`, `count_inc(int, A) -> int`;
- `collect_spec() -> aggregator(list(A), A, list(A))`, with
  `collect_inc`/`collect_final` polymorphic the same way;
- `exists_spec`/`not_spec`: `aggregator(int, A, bool)`;
- `min_spec`/`min_inc` with `requiring '<'(T, T) -> bool`, and `max` the
  same with `'>'`. A `requiring` clause needs its own `:- function`
  declaration, not a member of the grouped list;
- new `fsum`/`fprod`/`favg` macros and specs over floats, with seeds
  `0.0`, `1.0` and `kv(0.0, 0)`. `sum`/`prod`/`avg` stay int (decision 1
  in the plan: a `zero/0` class was rejected).

Export the new macros and functions, and update aggregates.md if any
row of its macro table changes.

Watch for the escape check (YCHR-60014) on existing goldens: once
`collect` is polymorphic, a `collect` over a polymorphic typed
constraint escapes unless the goal fixes the instance. All existing
`aggregates_*` goldens use untyped constraints, so they should not
change, but run `cabal test` early.

### 2. Goldens (black-box, the existing harness)

Use the spec's examples (type-system.md §Aggregates; the plan numbers
them 1 to 12). Expected verdicts, as checked by hand in M3 with a
polymorphic user aggregator:

| Example | Verdict |
|---|---|
| 1 `p(X), collect(Y, q(X, Y), L) ==> out(X, L)` | accepted |
| 2 `count(q(X, wrap(_)), N) ==> seen(X)` | YCHR-60001 at `seen(X)` |
| 3 `p(X), r(Y), count(q(X, Y), N) ==> pair(X, Y)` | YCHR-60015 (and a 60001 in the body) |
| 4 `client(C), count(order(C, _), N)` | warning YCHR-20106 |
| 5 sibling aggregates, same-named local | accepted |
| 6 `collect(Y, item(Y), [A, B]) ==> same(A, B)` | YCHR-60014; with `? integer(Y)` accepted |
| 7 `p(X), count(q(_), X)` | accepted |
| 8 `argmin(K, q(K, V))`, `q(T, U)` | YCHR-60006; with `q(int, U)` accepted, and a rule guard may pin `V` |
| 9 `collect(Y, q(Y), [A, B]) ==> integer(A) \| use_int(B)` | rejected (60001, plus 60014) |
| 10 `p(X), r(Y), collect(X, q(X, Y), L)` | YCHR-60015 |
| 11 `aggregate(aggregator(X, fun(W, Z) -> W + Z end, ...), Z, q(Z), X)` | YCHR-60006; with a preceding `count(r(_), X)` accepted |
| 12 `p(X, box(Z)), count(q(_), X) ==> out(Z)`, `p(A, A)` | use `out(string)`: YCHR-60001 at `out(Z)`. The plan's `out(int)` is a typo: nothing is wrong then |

Also from the plan: the float and string folds (positive); an int `sum`
over floats, a Result misused in the body, a bad user `Inc`, a nested
element error, and a constructor-arity error inside a goal (negative).
Example 4's warning goes in `test/YCHR/TypeCheckTest.hs` (or
`test/typecheck/test_typecheck.py`), since a golden `.error` file only
pins errors. Add any existing golden that starts warning to the
`GoldenTest.hs` allowlist.

`test/golden/aggregates_typed_aggregator/` (M3) already pins that the
`aggregates:aggregator` atom resolves.

For a typed aggregator outside the library, the pattern M3 tested with:

```prolog
:- function gather() -> aggregator(list(A), A, list(A)).
gather -> aggregator([], fun gather_inc/2, fun gather_final/1).
:- function gather_inc(list(A), A) -> list(A).
gather_inc(W, X) -> [X | W].
:- function gather_final(list(A)) -> maybe(list(A)).
gather_final(W) -> just(reverse(W)).
```

A module that writes `aggregator(...)` or `just(...)` itself needs
`library(maybe)`, and `?` needs `library(aggregates)` (it defines the
operator).

### 3. Docs and cleanup

- Delete this file.
- PROJECT.md: an "Already implemented" entry for aggregate typing
  (levels, links, escape check, the new codes), and the roadmap
  (`docs/`) if it lists typing as missing.
- Make sure aggregates.md's status line and Diagnostics table match.
- Run every new doc example and paste the captured output.

### Open questions for the user (raised by the M3 review, not decided)

- Links are gathered after all of a goal's conjuncts (spec §Gathering
  order). So with `p(T) requiring '<'(T, T) -> bool`, the rule
  `p(X), count((q(X, Y), ? Y < X), N)` is rejected (YCHR-60006): the
  `<` check runs before the link that would bring in the bound. Linking
  each name right after the conjunct that binds it would accept it.
- A selection goal's bounds stay inside it; the spec says both "like
  extra heads" and "inside the aggregate only".
- `E` is always escape-checked, so an aggregator that ignores a
  polymorphic element is rejected. The library `count` passes `1`, so
  it is unaffected.

## Typing hook points (M3)

| What | Where |
|---|---|
| encoding the aggregates | `TypeCheck/Encode.hs` `ruleHead`, `aggregate`, `aggConjunct`, `resultTerm`; `typechecker/ast.chr` `rule_head/3`, `agg_e/8`, `agg_conj`, `agg_res` |
| the binder fields | `Desugar/AggregateScope.hs` `scopeAggregates`; `Desugared.hs` `aggShared`, `aggLocals`, `aggBinds`, `aggResult` |
| gathering order | `walk.chr` `walk_rule1`, `hnf_guards`, `user_guards` |
| plain and selection checks | `walk.chr` `agg_check_plain`, `agg_check_select`, `agg_scope`, `goal_conjs_check`, `link_copies`, `agg_result_check`, `key_ctx` |
| levels and modes | `diag.chr` `ctx/5`, `lvl(Level, Mode)`, `report_dead`, `drop_copy_error`; `solver.chr` `rigid/3`, the `ev_unify_*` level guards, `guard_match_rigid_blocked` |
| links, escapes | `solver.chr` `link_unify`, `link_conflicts`, `escape_check` (released by `solving_done` in `main.chr`) |
| skeletons, collection | `skel.chr` `collect_vars_rule/4`, `goal_skel_cons`, `aggs_skel_cons` |
| arity walk | `pure.chr` `aggs_arity` |
| diagnostics | `TypeCheck/Error.hs`, `TypeCheck.hs` `decodeError`/`decodeWarning`, `Display.hs` (60014, 60015, 20106) |

## Runtime hook points (as of the phase I tip; line numbers drift)

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

### Typing (M3)

- **The checker's CHR is compiled on first use**, not at build time, so a
  CHR error in `typechecker/*.chr` only shows when something runs
  `ychr check`. `ychr check --Werror typechecker/*.chr` is the quick
  test (what `make test-typecheck` runs).
- **A fresh variable in a rule body must first appear as a top-level
  argument of a tell.** `check_unify(T, tcon(N, [W, E, R]), C)` with
  fresh `W, E, R` fails to compile (`UnboundVariable`); a helper
  constraint taking them as arguments (`agg_shape`) works.
- **Error ordering depends on the gathering order, by design.** Each
  told check runs to quiescence at once, and residual checks fire later
  when their variables get bound. Evidence placement is order-sensitive
  in the same way it is for guards.
- **`mode_copy` drops every error and warning** of a selection's second
  goal check. Anything typed only there, like the key, must use another
  ctx (`key_ctx`), or its errors vanish.
- **MicroHs gap 1 bit again:** an encoder function named `aggResult`
  clashed with the `aggResult` field. Name helpers so they never equal a
  record field.
- **Rigid ids are global** (`T#n`): a rule with goal occurrences takes
  ids from the same supply, so ids in later diagnostics shift.

### Runtime and compiler

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

Baseline at the M3 tip (`334ee89`): `cabal test` 2410/2410,
`test-style` 137, `test-repl` 86, `test-typecheck` 21, `test-docs` 45,
`test-stlc` 11, `test-scheme` 867 passed / 3 skipped, `make mhs-build`
clean. `make bench` has not been run on the typing work yet: M4 should
run it, interleaving 3 rounds of `typecheck/pairs_library` against
master (that benchmark is noisy, ±10-15%).

Baseline at the phase I tip: `cabal test` 2402/2402, `test-style` 134,
`test-repl` 86, `test-typecheck` 21, `test-docs` 45, `test-stlc` 11,
`test-scheme` 866 passed / 3 skipped, `test-scheme-runtime` clean,
`make mhs-build` clean. `make bench`: ~29 µs (`aggregates_sum`),
~744 µs (`aggregates_many`), ~14 µs (`aggregates_no_match`), ~7.5 ms
(`aggregates_takemin_many`).
