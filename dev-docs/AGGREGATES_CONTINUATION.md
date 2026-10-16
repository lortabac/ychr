# Aggregates: continuation notes

Working notes for finishing `docs/reference/aggregates.md`. This file
exists so the work can move to a fresh session without re-deriving
decisions that are already settled. Delete it when the feature is done.

Branch `aggregates`, worktree `.worktrees/aggregates`. Started from
`569ba4a`; the current tip is `e2b6e1c`. The front end, the fold and
`library(aggregates)` are in; goal occurrences, the removal step and the
documentation sweep are not.

## Read this first

**The feature is usable but incomplete, and must not be merged yet.** An
aggregate evaluates, and a rule that has one fires when one of its
*regular* heads is told or reactivated. What is missing is the other
direction: telling or removing a constraint that appears in an aggregate
*goal* does not retry the rules that observe it (phase E), so a program
whose goal constraints arrive later than the rule's heads silently misses
derivations. That is the "worse than a clean error" state: the workaround
for a test is to tell the goal's constraints first, which is why every
golden case does.

Nothing is silently inert, though. Selection aggregates and nested
aggregates are reported and dropped (`YCHR-40004`), so no rule can compile
into something that never fires.

The spec has a known error at line 142 ("The store here *includes* the
rule's own head constraints"): the decision that replaced it is
implemented, see "Store visibility" below. The spec's Implementation-notes
paragraph on Late Storage is wrong in the same way — the fold is a plain
`Foreach` over the store, and a rule with aggregates stores its live active
constraint *before* the fold. Phase G rewrites both.

## Where the work stands

| Phase | State |
|---|---|
| 1. surface, AST, diagnostics | **done**, `4b3c25b` |
| A. goal HNF, lambda lifting into aggregates | **done**, `1098cf5` |
| B. the fold, gates | **done**, `9c426fb` |
| C. store visibility, history, escapes, passivity | **done**, `e2b6e1c` |
| D. `library(aggregates)` | **done**, `9c426fb` (committed with B: the fold cannot be tested without the library) |
| E. goal occurrences | not started |
| F. removal step | not started |
| G. typing, docs, bench | not started |

## What works, and how it is pinned

- `aggregate(Agg, Element, Goal, Result)` folds the goal's matches in goal
  order into a local working value, applies the aggregator's `Final`
  closure, treats `nothing` as "the rule does not apply", and matches
  `Result`.
- `library(aggregates)` provides `count/2`, `sum/3`, `prod/3`, `min/3`,
  `max/3`, `avg/3`, `collect/3`, `exists/1` and `\+/1` as macros over the
  core form, plus the `aggregator/3` constructor and the `?`/`\+`
  operators.
- A rule with aggregates fires at most once per combination of its regular
  heads, whatever its kind, and the constraint being activated is counted.
- A variable that only an aggregate's goal binds is reported as escaping
  (`YCHR-40003`) if the rule's guard or body reads it.

Golden cases (each runs on the Haskell interpreter and, except the negative
ones, on the Scheme backend):

| Case | Pins |
|---|---|
| `aggregates_count` | the fold, and a result read from the guard/body |
| `aggregates_sum` | the banking example, including a guarded rule |
| `aggregates_minmax` | min and max, ties, and undefined-when-empty |
| `aggregates_collect` | goal order in the folded list |
| `aggregates_exists_not` | `exists` and `\+` in both directions |
| `aggregates_multi` | two aggregates in one head, the second reading the first's result |
| `aggregates_view_stored` / `aggregates_view_removed` | the constraint being activated is counted, kept or removed |
| `aggregates_element_unbound` | `YCHR-40002` for an element variable the match cannot supply |
| `aggregates_local_escapes` | `YCHR-40003` |

Unit cases: `test/YCHR/DesugarTest.hs` (`aggregates` group: a compound goal
argument's guards stay with the conjunct, a repeated goal variable becomes
an equality, the head and the goal share one fresh-name counter, and both
lambda scopes), and `test/YCHR/CompileTest.hs` (`aggregate folds` group:
one fold procedure per aggregate, read-only apart from its out-cell
bindings, the out-cell on the left of `bunify`, a soft-guarded call, a
history for a head-removing rule, no passivity for an aggregate rule, and
no fold procedure at all for a program without aggregates).

## Settled decisions, as implemented

### Store visibility

Late Storage leaves a freshly told constraint out of the store until the
end of `activate_c`, so a fold that only reads the store cannot count the
constraint being activated. The earlier note here said not to force a
`Store`; that was wrong, and the reason is the banking example: with the
client told first and the threshold crossed by the *last* account, the goal
occurrence runs while that account is unstored, the sum is short by one,
the guard fails, the account is stored afterwards, and nothing retries the
client, so `platinum/1` is never derived.

**Implemented:** every occurrence of a rule with aggregates emits
`Store active` before the guard (inside the HNF match-guard wrapper, so a
failed structural match does not store). It is emitted whether the rule
keeps or removes the active constraint: skipping it for a removed active
would make an aggregate's value depend on which head is active, and would
break the idempotence passivity argument, which assumes both occurrences
see the same store. Storing cannot make the active constraint match itself
as a partner, because the partner loops have already taken their snapshot.
The firing's own `Kill` still removes it, and a dead suspension left in the
bucket is skipped by liveness. `Compile.genFireStmts`'s own Late Storage
`Store` becomes a no-op for these rules.

The two spec passages (line 142 and the Late Storage paragraph at 443-458)
still say the old thing; phase G rewrites them.

### The result pattern

Every structural test runs before every binding, so a pattern that cannot
match leaves the out-cells untouched and nothing is half-done when the
guard's soft boundary is abandoned. A variable already in scope (a shared
input or a goal-local) is compared with `BEqual` (ask semantics, total on
unbound operands). A fresh variable — bare or nested inside a compound
pattern — is bound through an out-cell, and the out-cell is the **left**
operand of the `bunify`. That order is load-bearing: `unify'` binds its
left operand and returns that operand's observers
(`Runtime/Var.hs:160-175`), so binding a fresh cell enqueues no
reactivation, whereas the other order would bind the computed result and
enqueue whatever observes it, inside the guard window where the active
constraint is unstored.

This widens the letter of `dev-docs/INVARIANTS.md` §"Rule-guard residuals
do not tell": a guard, through a called procedure, can now bind. The
binding is on a fresh cell created per candidate and unreachable from the
store, so nothing reacts to it and nothing is left behind. `vm.md` states
the old rule normatively twice (the `bequal` section and the `bsoft-guard`
section); phase G amends both, and INVARIANTS.md records the exception.

### History

A rule keeps a firing history when it removes no regular head **or** when
it has an aggregate, whatever its kind: an aggregate's value can change
after the rule fired, and the spec fires such a rule once per combination
of regular heads. The history tuple is built from the regular heads only.
The history guard is emitted **in front of** the folds, not behind them:
both are pure, and a combination that already fired must not refold.

### Passivity

`Compile/Passive.isPassive` returns `False` for every occurrence of a rule
with an aggregate. The two sources there rest on the ωr-earlier occurrence
always firing first, which an aggregate's applicability condition can
falsify. Dropping the optimization for those rules is conservative;
`dev-docs/passive-occurrences.md` still needs a sentence (phase G).

### Diagnostics and gates

| Code | Constructor | Condition |
|---|---|---|
| `YCHR-40003` | `AggregateLocalEscapes` | a variable only an aggregate's goal binds is read by the rule's guard or body |
| `YCHR-40004` | `AggregateNotImplemented` | selection aggregates and nested aggregates, until their phase |
| `YCHR-40005` | `AggregateResultNotMaybe` | the program declares no `maybe:just/1`, so no aggregator can produce the protocol's result type |

`YCHR-40003` is reported per name at the rule head, before the guard and
body are lowered, so a typo gets that message rather than `YCHR-40002`.

### The aggregator protocol

The compiler assumes the two facts in Note [Aggregator representation]
(`Compile/Aggregate.hs`): `Agg` evaluates to a three-argument
`aggregates:aggregator(Init, Inc, Final)` (checked at run time with
`bmatch-term`, so a wrong shape is a runtime error, not a silent misread),
and `Final` returns `library(maybe)`'s `maybe`. The result is decoded with
the `maybe:just` functor; a value that is neither `just/1` nor `nothing` is
a runtime error naming the protocol, and a program with no `maybe:just/1`
is rejected at compile time. No new VM instruction is involved anywhere:
`CallExpr` is already a `ValExpr`, so the fold call rides inside
`BSoftGuard`, and the aggregate procedure is emitted as a `PKFunction` with
the reserved module name `$aggregate` (reusing that kind keeps the
serialization format and its version untouched).

## Exact hook points

Line numbers are as of `e2b6e1c`; they will drift.

### Done

| What | Where |
|---|---|
| recognise the forms | `Rename.hs` `aggregateKindOf` :1365, `renameAggregate` :1385, `renameConjunct` :1435, `checkAggregateOnlyHead` :1298 |
| qualify + type an aggregate | `Resolve.hs` `resolveAggregate` :1319 |
| goal HNF, per conjunct | `Desugar.hs` `desugarAggregates` :307, `desugarAggregate` :333, `desugarConjuncts` :355, `normalizeHeadConstraints` :422, `normalizeGoalConstraint` :440 |
| lambda lifting into aggregates | `Desugar.hs` `liftRule` :1192, `liftAggregate` :1229, `liftConjunct` :1252, `aggregateGoalVars` :1290 |
| plan + gates + escapes | `Compile/Aggregate.hs` `collectAggregatePlans` :96, `checkLocalEscapes` :153, `checkSupported` :249, `aggregateResultTypeDeclared` :296, `aggregateResultMatch` :330 |
| occurrence collection | `Compile/Occurrences.hs` `collectOccurrences` :60, `ruleOccurrences` :130, `mkOccurrence` :168 |
| occurrence wiring | `Compile.hs` `genGuardedFire` :483 (store, out-cells, fold calls, history placement) |
| the fold procedure | `Compile.hs` `genAggregateProcedure` :597, `maybeValueStmts` :670, `bindsStmts` :703, `withGoalNest` :724, `bindGoalArgs` :772, `lookupGoalCType` :792 |
| per-aggregate helpers | `Compile.hs` `aggregateOutCellStmts` :543, `aggregateOutCellVars` :549, `aggregateTest` :564 |
| history | `Compile.hs` `genFireStmts` :930 (returns `CompiledFire`), `ruleHistory` :1007, `buildHistoryIds` :1019, `genKillStmts` :1045 |
| program assembly | `Compile.hs` `compile` :128 (`aggregateWork`), `genConstraintProcs` :314 (`inertType`) |
| passivity exemption | `Compile/Passive.hs` `isPassive` :67, `aggregateRule` :73 |
| codes and messages | `Display.hs` :369-371, :1567-1590 |
| generated names | `Compile/Names.hs` `aggregateProcName` :335 and the block around it |
| library | `libraries/aggregates.chr`, listed in `embed/YCHR/Embedded/StdLib.hs` `librarySources` |

### Phase E — goal occurrences

Every CHR constraint conjunct of an aggregate goal becomes an occurrence of
its type, alongside the rule's ordinary head occurrences. Nothing of this
exists yet; the design that fits the code as it stands:

1. **The record.** Add to `Occurrence` (in `Compile/Types.hs`) a marker for
   goal occurrences carrying: the active conjunct (`HeadConstraint` plus
   its own HNF guards), the remaining conjuncts of the same goal in goal
   order, the enclosing goals' conjuncts (empty until nested aggregates
   land), and the *number of leading partners that are not regular heads*.
   The partner list stays one flat list in the order the loops are nested:
   the goal's own conjuncts first, then the enclosing goals', then the
   regular heads. Everything that must see only heads takes the tail:
   `buildHistoryIds`, `genKillStmts`, the backjump list, and the `VarMap`
   (`buildVarMap`) — pass the boundary count, or add a small accessor
   `headPartners occ = drop occ.goalPartnerCount occ.partners`.

2. **Numbering.** `ruleOccurrences` emits the rule's ordinary occurrences
   first and its goal occurrences after them; `collectOccurrences` already
   reverses and numbers per type, so within one rule a goal occurrence
   follows that rule's ordinary occurrences of the same type, which is what
   the spec asks for. Passivity is already off for these rules (phase C),
   so no change is needed there; `YCHR.Internal.Compile.Passive` needs
   nothing.

3. **The location procedure.** A goal occurrence's procedure takes
   `activeName : argNames arity`, binds the active conjunct's arguments
   from that suspension, evaluates the active conjunct's HNF guards, then
   nests: the remaining goal conjuncts (with the same distinctness tests as
   head partners), the enclosing goals, then the regular heads through the
   existing `wrapInPartnerLoops`. Treat *every* goal argument as a local in
   the location phase, including one that also occurs in a regular head:
   the fire step recomputes the aggregates from the regular heads and
   discards the goal's bindings (spec §2 step 3), so a pairing the goal
   does not really support is only an extra try, never a wrong answer. That
   is also why the location phase needs no equality between a goal argument
   and a head argument.

4. **Distinctness.** Pairwise distinct *within* one goal, like head
   conjuncts, and within the regular heads as today, but **never across the
   two**: a goal partner may be the same suspension as a regular head (the
   `task(T), \+ depends(T, _) \ depends(U, T)` shape of the spec depends on
   it). The fold's own loops need the within-goal tests too, so the two
   agree on what a match is; `withGoalNest` (`Compile.hs:724`) already
   builds the loops and is the place to add them.

5. **The fire step.** For a goal occurrence, `isKept = True` (firing does
   not remove the active constraint), the `VarMap` comes from the regular
   heads only, and the aggregate calls read their shared inputs from that
   map. The store prologue must become `If (BAlive active) [Store it] []`
   for these occurrences, because phase F calls the *same* procedure with a
   removed (dead) constraint; a dead constraint must not be stored and must
   not be counted.

6. **Inertness and constraint use.** A type with goal occurrences must not
   be inert (`genConstraintProcs`'s `inertType`: the test is already
   `null occs` over the filtered list, so it becomes right once goal
   occurrences are in it). `ConstraintUse.checkConstraintUse` counts a
   constraint in an aggregate goal as a kept occurrence.

7. **Tests.** The spec's own examples: a rule whose goal constraints are
   told *after* its heads (this is the one that shows the phase is
   missing), a fold over the active's own type, the re-tell loop idiom, a
   removed head's type retried through the removal step (phase F), and a
   `:trace` case.

### Phase F — the removal step

When a rule fires and removes constraints, the first thing its body does is
the removal step: for each removed regular head, in textual order, call one
procedure per goal occurrence of its type, passing the removed constraint's
id and arguments.

1. **Order.** Iterate the rule head's `removed` list in source order. Note
   that a partner's `idx` numbers `reverse removed` (`Occurrences.hs:153`),
   so textual order within the removed group is *descending* `idx`; a
   removed **active** head is not in the partner list at all and has to be
   included by hand.

2. **The call.** The goal-occurrence procedure needs a trailing `Bool`
   parameter (`$removal`): `genActivate` passes `false`, the removal step
   passes `true`. Without it, the early-drop
   `If (BNot (BAlive active)) [Return True]` sees the dead active and
   returns after the first firing, so the remaining combinations of regular
   heads are never retried. With the flag, that test is skipped for
   removal-step calls and the procedure runs to the end.

3. **The body-statement count.** `storeStmts`' condition in `genFireStmts`
   becomes `not (null bodyStmts) || not (null removalStmts)`, so a removal
   step counts as a non-empty body and the active constraint is stored
   before it.

4. **Self-triggering.** The removal step includes the firing rule's own goal
   occurrences, so a dependency chain works and recursion depth equals the
   chain's length. Nothing is added to the runtime's `Kill`.

### Phase G — typing, docs, bench

- `docs/reference/aggregates.md`: the Status line; the four corrections the
  old notes list (line 142, 199/460, 276-280, 400-402 — the line 142 one is
  now "store visibility" above); the Implementation notes' Late Storage
  paragraph replaced by the actual scheme; and two limitations to record:
  `sum`, `prod`, `min`, `max` and `avg` are integer-typed until the
  aggregator typing lands (a float element needs overloaded helpers), and
  `forall/2` is not defined yet because it needs nested aggregates.
- `macros.md`: the "once implemented" note about `aggregates`.
- `type-system.md`: aggregates are not type-checked yet — the encoder drops
  the aggregate list (`TypeCheck/Encode.ruleHead`), and an aggregate-bound
  variable in a guard gets a flexible `sk_open` slot (`typechecker/skel.chr`
  `collect_vars_rule`), not `ty_any`; plus the full typing rules for later.
- `INVARIANTS.md`: the aggregate exception to "guards do not tell".
- `passive-occurrences.md`: no passivity for a rule with an aggregate.
- `language.md`: the REPL's query operator table merges every library's
  exports, so `?` and `\+` become visible in REPL queries.
- `CHANGELOG.md`; `bench/Main.hs` gets `aggregates_sum` (and a no-match
  case, and a many-match case).
- The gate for a *macro* use inside an aggregate goal: `renameConjunct` does
  not expand macros, so a nested `count(...)` currently fails as an unknown
  constraint. Report it as not-implemented (a rename-phase code, the next
  free in the 2xxxx band) rather than leaving that confusing error.

## Facts that cost time to establish

- **No new VM instruction is needed.** `CallExpr` is already a `ValExpr`, so
  `BFromVal (CallExpr aggProc sharedVars)` puts a whole `Foreach` fold
  inside a `BSoftGuard`.
- **`unify'` binds its left operand and returns that operand's observers**
  (`Runtime/Var.hs:160-175`). This is why every out-cell `bunify` puts the
  cell on the left; a `CompileTest` case pins it.
- **Local variables are not trailed.** `Env` is an `IOArray Int Cell` and
  `AssignVal` writes a slot directly; the trail covers only
  `TrailVar`/`TrailFlag`. A fold accumulator in a local is safe from undo.
- **`Foreach` has no per-iteration undo** and iterates an immutable store
  snapshot, so a later tell is invisible to a fold already running.
- **`BSoftGuard` catches only `InstantiationError`**, restores the call
  stack, and does not roll back locals or bindings.
- **An inert type registers no observers**, which is why a type with goal
  occurrences must not be inert.
- **A library's *content* edit is not always re-spliced.** `embed/`'s splice
  reads the file list it names, and Cabal re-runs it from the files it
  tracked at configure time; after adding a library, `cabal configure all`
  may still leave the old text in the binary. The reliable recipe is to
  remove the component's build directory and rebuild it:

  ```sh
  rm -rf dist-newstyle/build/*/ghc-*/ychr-*/x/ychr
  cabal build exe:ychr
  ```

  The same applies to `t/ychr-tests` when a golden or unit test reads a
  library. Editing `embed/YCHR/Embedded/StdLib.hs` also works, and is what
  that module's own comment recommends.
- **A simpagation head (`\`) needs `<=>`.** `convertPropagationHead` does
  not split a `\` head, so `A \ B ==> C` fails as an unknown name `\/2`.
- **`fun M:name/N` is a pre-existing resolver gap.** Only unqualified
  `fun name/N` canonicalizes; the renamer flattens it to `M:name` at the use
  site. The library therefore writes `fun count_inc/2`, not
  `fun aggregates:count_inc/2`. A *macro body* referring to another
  module's helper has the same problem.
- **A golden goal must be one declared constraint.** `-g` rejects a
  conjunction, so every test tells its constraints from a `setup/N` rule
  (`setup(A) <=> d(1), c(1), ask(A).`).
- `make format` does not enforce the 95-column limit that `test-style`
  checks, so run `test-style` after formatting.

## Verification recipe

```sh
cd /home/lorenzo/Development/ychr/.worktrees/aggregates
CABAL_DIR=/home/lorenzo/Development/ychr/.cabal-home cabal build all
CABAL_DIR=/home/lorenzo/Development/ychr/.cabal-home cabal test
make format && make test-style
make test            # the python suites, including test-scheme (needs Guile 3)
make bench           # not run since phase C; phase G adds cases
```

Baseline at `e2b6e1c`: `cabal test` 2299/2299, `test-style` 134,
`test-repl` 75, `test-typecheck` 21, `test-docs` 44, `test-stlc` 11,
`test-scheme` 800 passed / 3 skipped (the same three the harness skipped
before this work; a negative case carries no `.goal`, so it is not
collected). `test-scheme-runtime` passes in full (`Total failures: 0`).
`make bench` has not been run in this session; phase G adds cases.
