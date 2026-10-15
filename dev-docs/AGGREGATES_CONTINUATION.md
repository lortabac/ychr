# Aggregates: continuation notes

Working notes for finishing `docs/reference/aggregates.md`. This file
exists so the work can move to a fresh session without re-deriving
decisions that are already settled. Delete it when the feature is done.

Branch `aggregates`, worktree `.worktrees/aggregates`, rebased on
`569ba4a` (Implement declaration macros).

## Read this first

**Nothing here may be merged until Phase 2 lands.** An aggregate is
recognized and compiles, but no fold evaluates it, so a rule that uses
one simply never fires:

```prolog
c(X), aggregate(dummy, 1, d(X), 0) ==> fired(X).   % compiles; fired/1 never derived
```

That is worse than a clean error. If the branch has to sit for a while,
gate the feature behind an explicit "not implemented" compile error
rather than leaving it silently inert.

**The spec has a known error.** `docs/reference/aggregates.md` line 142
("The store here *includes* the rule's own head constraints, so
`c(X), count(c(_), N)` counts the `c` in the head too") contradicts its
own Late Storage note at lines 443-446. Do not implement line 142
literally; see "Settled decisions" below. Fixing the four spec points is
Phase 7, but the *semantics* decision is already made and must be
followed from the start.

## Where the work stands

| Phase | State |
|---|---|
| 1. surface, AST, diagnostics | **Done**, commit `4b3c25b` |
| 2. the fold | not started |
| 3. `library(aggregates)` | not started |
| 4. selection forms | not started |
| 5. goal occurrences | not started |
| 6. removal step | not started |
| 7. typing, docs, bench | not started |

What Phase 1 actually delivers: the three ASTs carry the rule's
aggregates, the renamer recognizes the five forms, and four diagnostics
report misuse. Verification after the rebase: `cabal test` 2278/2278,
`test-repl` 75, `test-typecheck` 21, `test-docs` 44, `test-stlc` 11,
`test-style` 133, `test-scheme` 792 passed / 3 skipped.

Not yet run at all: `test-scheme-runtime`, `make bench`.

## Settled decisions

These were decided before implementation started. Follow them; do not
reopen them without saying why.

### Store visibility — the aggregate sees whatever is in the store

The paper's Definition 4 writes the aggregate over the store, which
*does* include the rule's head constraints (`agg_cond(A, S_h ∪ S, B)`),
but it takes `S` as given and never says whether the constraint being
activated is in it. That is operational, and YCHR's Late Storage means
an active constraint is unstored, so a store search does not see it.

**Decision: no special-casing and no forced `Store` before the fold.**
The fold sees exactly what a `Foreach` over the store sees at that
point. A head constraint is counted because it is stored; the active
constraint joins the fold only once it is stored, which Late Storage
postpones to the end of `activate_c`. So a rule that counts its own head
constraint can see its own count change when it is reactivated after a
variable is bound.

This costs nothing in the common cases: when a later `account` tell
arrives, every `client` is already stored, so a goal over `client`
finds it.

The spec fix (Phase 7) is to replace line 142 with a precise statement
of this, keep 443-446 as the reason, and drop the phrase "and it must
not be counted twice" — there is no second counting site if the fold is
one `Foreach`.

Pin it with a golden test in both directions, not just the convenient
one.

### `Result` is matched with `BEqual`, not `BUnify`

The spec says "Match `Result` against `R`", with head-matching
semantics. `BUnify` is the wrong operator: it binds, so a failure part
way through leaves half-done bindings that survive (see
`dev-docs/INVARIANTS.md` §"Rule-guard residuals do not tell" — the soft
guard catch does not roll back).

Use `BEqual` (ask semantics, `==`, total on unbound operands). The
consequence to document: a `Result` containing a fresh variable cannot be
*bound* by an aggregate — it either agrees with the computed value or the
rule does not apply. A use that needs binding must do it in the rule body
with `=`.

### Aggregates are intercepted by name *and* arity

`renameCon` checks the aggregate forms before `classifyGoalName`, so a
user macro or function called `aggregate/4` cannot shadow them, but an
unrelated `aggregate/3` is unaffected. Only an unqualified name matches,
so `M:aggregate` stays an ordinary constraint.

### Fire once, with the history over the regular heads only

Confirmed against the paper: the ω<sub>t</sub> (Apply′) / §4.7 fire-once
semantics, with the history recording the regular heads. This composes
with the paper's algorithms — Sudoku's loop works by *re-telling* `solve`
in the body, which makes a new combination.

One consequence the spec under-explains and the implementation must
honour: **a rule of *any* kind gets `BNotInHistory`/`AddHistory` once it
has an aggregate**, not just propagation rules. Without it,
`c(X) \ count(d(X), N) <=> …` would fire again on every later `d`. So
`genFireStmts`'s `isPropagation` test becomes "`removed` is empty **or**
the head has aggregates".

### `forall/2` does not clash with `library(search)`

Both macro and ordinary visibility are arity-keyed
(`Rename.hs`'s `macroDefTable` is keyed `(module, name, arity)`;
`classifyGoalName` filters by arity), and arity overloading is an
intentional, tested feature (`test/golden/arity_overload`). So
`aggregates:forall/2` and `search:forall/3` are distinct names. No
qualification is needed and no diagnostic. An earlier draft of the plan
claimed otherwise; that was wrong.

## Phase 1 design choices — do not relitigate

- **Recognition lives in the renamer, not the parser.** A predefined
  aggregate is a macro (`sum/3`, `count/2`, …), so expansion has to run
  first, and `renameCon` is where head macros already expand.
  `Parsed.Head`'s aggregates slot is therefore *always empty* out of the
  parser; `renameHead` rebuilds it. `RoundtripTest`'s generator reflects
  this and must keep doing so.
- **`Aggregate` is threaded through all three ASTs** rather than being
  desugared early. `Types.Aggregate` holds raw `Term`s;
  `Resolved.Aggregate` holds typed `Expr`s (resolution is what types
  them); `Desugared.Aggregate` shadows the `Types` one, which is why
  `Desugared.hs` hides `Aggregate`/`AggregateConjunct` on import.
  `AggregateKind` is shared, not duplicated.
- **Aggregates are not in `kept` or `removed`.** They get their own
  list, which is why every existing walker over the two head lists kept
  seeing exactly what it saw before.
- **All `?` guards stay in `goal`**, in source order. An earlier attempt
  hoisted a whole-goal guard into a separate field; that was dropped as
  complexity with no benefit, since a guard before the constraints is
  already the semantics.
- **`AggregateOnlyHead` is checked in `renameRule`**, per rule and after
  expansion, so a macro that expands to aggregates only still reports.
  It is not a parser error.

## Exact hook points

Line numbers are as of `4b3c25b`; they will drift.

### Already done

| What | Where |
|---|---|
| recognize the forms | `Rename.hs` `aggregateKindOf` :1365, `renameAggregate` :1385 |
| classify goal conjuncts | `Rename.hs` `renameConjunct` :1435, `isGuardFunctor` :1474 |
| body/guard interceptions | `Rename.hs` `renameBodyGoal`, `renameTerm` |
| aggregate-only check | `Rename.hs` `checkAggregateOnlyHead` :1298 |
| qualify + type an aggregate | `Resolve.hs` `resolveAggregate`, `collect` |
| desugar aggregates | `Desugar.hs` `desugarAggregate` :306 |
| HNF pass-through | `Desugar.hs` `normalizeHead` :381 |
| diagnostics | `Display.hs` :321-324, and the matching `renameErrorMsg` arms |

### Phase 2 — the fold

| What | Where |
|---|---|
| the fold itself | `Compile.hs`, new; model the loop on `wrapInPartnerLoops` :526 |
| the call site | `Compile.hs` `genGuardedFire` :462 — after the heads match |
| history for every kind | `Compile.hs` `genFireStmts` :594 (`isPropagation`) |
| keep `buildHistoryIds` unchanged | `Compile.hs` :671 — regular heads only |

### Phase 5 — goal occurrences

| What | Where |
|---|---|
| synthesize occurrences | `Compile/Occurrences.hs` `ruleOccurrences` and `mkOccurrence` |
| don't emit kills/stores for them | `Compile.hs` `genKillStmts` :697, `genFireStmts` :594 |
| the inert-type fix | `Compile.hs` `genConstraintProcs` :307, `inertType` :322 |
| constraint-use role | `ConstraintUse.hs` `checkConstraintUse` :60, `occurrences` :68 |
| variable scope | `Desugar.hs` `ruleHeadVars` :1086, `liftRule` :1131 |
| symbol table | `Desugar.hs` `getRuleConstraints` :263 (already walks aggregate goals) |

The inert-type fix is a one-line change with a non-obvious reason: the
test must become `null regularOccs && null goalOccs` rather than
`null occs`. A type with goal occurrences is not inert, because an inert
type registers no observers — so reactivating one would never fire, and
its goal occurrences would never be retried.

Do **not** change `Compile/Passive.hs`. Both passivity sources key off
`(kept, removed)`, and a rule with an aggregate still needs its removed
occurrence tried first — the soundness argument is unchanged.

### Phase 6 — removal step

`genFireStmts` :594, prepending calls before the body statements. The
removal step must count as a non-empty body so `storeStmts` still fires
when the body is `true`.

## Facts that cost time to establish

- **No new VM instruction is needed.** `CallExpr` is already a `ValExpr`,
  so `BFromVal (CallExpr aggProc sharedVars)` puts a whole `Foreach`
  fold inside a `BSoftGuard` — which is what makes an instantiation error
  anywhere in the fold leave the aggregate undefined. Soft guard only
  catches `InstantiationError`; everything else aborts, which is the
  documented behaviour.
- **Local variables are not trailed.** `Env` is an `IOArray Int Cell`
  and `AssignVal` writes a slot directly; the trail covers only
  `TrailVar`/`TrailFlag`. So a fold accumulator in a local is safe from
  undo, and a `Foreach` iteration does **not** roll anything back.
- **Store, index, history and the reactivation queue use whole-structure
  snapshots**, not the trail.
- **`Foreach` has no per-iteration undo**, and `BSoftGuard` deliberately
  does not roll back locals.
- **`catchInstantiation` snapshots and restores the call stack** but
  not locals or bindings.
- **An inert type registers no observers** (`Runtime/Store.hs`, the
  `InertSet` check), which is exactly why a type with goal occurrences
  must not be inert: its reactivations would never fire.
- **`declare-macro` work landed on master in `569ba4a`**, adding
  `MacroKindMismatch` = YCHR-20035 and shifting
  `MalformedMacroPrimitive`/`MacroPrimitiveOutsideMacro`/
  `MacroExpansionTooLarge` to 20036-20038. The aggregate codes
  (20039-20042) were chosen to follow them; keep the range contiguous and
  `test/YCHR/ErrorCodeTest.hs` will keep passing.

## The four spec corrections (Phase 7)

1. **Line 142** — store visibility, rewritten as above.
2. **Lines 400-402** — `exists`/`\+` are said to have result `true` while
   also passing `_` as `Result`. A `_` matches anything, so the value is
   never observed. Drop the `true` claim.
3. **Lines 199 and 460** — extend the fire-once section with the sentence
   that the history is recorded for a rule of *any* kind once it has an
   aggregate.
4. **Lines 276-280** — goal occurrences come after the regular ones in
   the rule's ω<sub>r</sub> order, which is *removed-first, right-to-left*,
   not textual. Reword.

Also: the Status line ("draft, not implemented") and `macros.md`'s
"once implemented" note.

## Diagnostics already implemented

| Code | Constructor | Condition |
|---|---|---|
| YCHR-20039 | `AggregateOnlyHead` | rule head is aggregates only |
| YCHR-20040 | `AggregateOutsideHead` | aggregate in a body, query or guard |
| YCHR-20041 | `MalformedAggregateGoal` | bad arity, or a bad goal conjunct |
| YCHR-20042 | `GuardOutsideAggregateGoal` | `?/1` outside an aggregate goal |

`AggregateLocalEscapes` was planned for the 40xxx compile band
(`YCHR-40003`, after `UnboundVariable` = 40002) and is **not yet
implemented**. It belongs with the variable scoping work in Phase 5.

## Tests already in place

`test/YCHR/DesugarTest.hs`, `ParserTest.hs`, `RenameTest.hs`,
`DSLTest.hs` and `RoundtripTest.hs` were updated for the new head slot
only — they pin that the slot exists and stays empty out of the parser.
No aggregate behaviour is tested yet.

## Verification recipe

```sh
cd /home/lorenzo/Development/ychr/.worktrees/aggregates
CABAL_DIR=/home/lorenzo/Development/ychr/.cabal-home cabal build all
CABAL_DIR=/home/lorenzo/Development/ychr/.cabal-home cabal test
make format && make test
```

`make format` runs ormolu; it does **not** enforce the 95-column limit
that `test-style` checks. A long line left by hand-editing will fail
`make test-style` after `make format` has already passed.
