# YCHR Aggregates Specification

**Status: implemented.**
The core form, the predefined aggregates, the selection forms
(`argmin`/`argmax`/`takemin`/`takemax`), nested aggregates, goal
occurrences and the removal step run on both backends, and the type
checker checks them ([type-system.md](type-system.md#aggregates)).

An *aggregate* is a rule-head conjunct that summarizes an unbounded
part of the constraint store: the sum, count, minimum, … of a value
over every match of a goal. A rule head without aggregates matches a
fixed number of constraints; an aggregate matches all of them at once.

```prolog
:- use_module(library(aggregates)).

client(C), sum(B, account(_, C, _, B), S) ==> S >= 25000 | platinum(C).
```

`platinum(C)` is derived as soon as the balances of `C`'s accounts
add up to 25000, whether the client or the accounts arrive first, and
whatever rules elsewhere in the program add, update or remove
accounts. Without the aggregate, every such rule must maintain an
auxiliary running total by hand.

The design follows Sneyers, Van Weert, Schrijvers and Demoen,
*Aggregates in CHR* (2007): the same core form, the same predefined
aggregates as macros over it, the same fire-once semantics. The
implementation strategy does not follow the paper (see
[Implementation notes](#implementation-notes)).


## The core form

```prolog
aggregate(Agg, Element, Goal, Result)
```

may occur as a conjunct of a rule head, kept or removed.

- `Agg` is an expression evaluating to an *aggregator*,
  `aggregator(Init, Inc, Final)`, a constructor of
  `library(aggregates)`:
  - `Init` — the initial working value;
  - `Inc` — a closure applied to the working value and one element,
    returning the next working value;
  - `Final` — a closure turning the last working value into the
    result, as a `maybe` (`library(maybe)`). `nothing` means the
    aggregate is *undefined* (the maximum of no elements, say) and the
    rule does not apply.
- `Element` is an expression, evaluated once per match of `Goal`.
- `Goal` is an *aggregate goal* (see [Aggregate goals](#aggregate-goals)).
- `Result` is a pattern, matched against the result.

User-defined aggregates are ordinary aggregators:

```prolog
:- use_module(library(aggregates)).
:- use_module(library(maybe)).

:- macro sum_sq(E, G, R) --->
       [ aggregate(aggregates:aggregator(0, fun(W, X) -> W + X * X end,
                                            fun(W) -> just(W) end),
                   E, G, R) ].
```

### Typing

`library(aggregates)` declares the aggregator type, over elements of
type `E`, working values of type `W` and results of type `R`:

```prolog
:- chr_type aggregator(W, E, R) --->
       aggregator(W, fun(W, E) -> W end, fun(W) -> maybe(R) end).
```

`Agg` has type `aggregator(W, E, R)`, `Element` type `E` and `Result`
type `R`. The selection key must be comparable with `<` (or `>` for
`argmax`/`takemax`). The full rules — scopes, how far a goal's facts
reach, and the errors — are in
[type-system.md §Aggregates](type-system.md#aggregates).


## Aggregate goals

An aggregate goal is a conjunction of:

- CHR constraints;
- aggregates (nested aggregates);
- guard conjuncts, written `? Guard`.

```prolog
count((employee(E, C), salary(E, S), ? S > 1000), N)
```

A guard conjunct is checked in place, left to right, so it can test
variables bound by the conjuncts before it and filter matches before
the conjuncts after it are searched. Like a rule guard, it is an
ask-only boolean expression.

`?/1` is recognized structurally inside an aggregate goal, as `,` is;
outside one it has no meaning. `library(aggregates)` exports the
operator `op(900, fy, '?')`. Without the operator, write the functor
quoted: `'?'(Guard)`.

The goal is a goal position for [macros](macros.md), so the
predefined aggregates may be nested:

```prolog
argmax(S, (client(C), sum(B, account(_, C, _, B), S)))
```

`takemin` and `takemax` may not be nested (`YCHR-40004`): they would
have to remove one match per match of the enclosing goal. `argmin` and
`argmax` may.

### Variables

A variable of an aggregate's `Goal` or `Element` is *shared* if it
also occurs outside that aggregate in:

- the regular (non-aggregate) head conjuncts of the rule;
- the enclosing aggregate goals, for a nested aggregate;
- the `Result` of an aggregate to its left, at the same level;
- the `Goal` of a selection form to its left, at the same level
  (see [Selection aggregates](#selection-aggregates)).

Every other variable of `Goal` and `Element` is *local* to the
aggregate: it is renamed apart per match. Shared variables are inputs:
matching the goal never binds them, and a match must agree with their
values (`==`, as for head matching). The selection forms are the
exception: their goal variables are visible to the rest of the rule.

A local variable is not visible to the rule's guard or body. Using its
name there anyway is an error (`AggregateLocalEscapes`), not a
distinct variable, so a typo cannot silently change its meaning. A
variable that occurs both in the goal and in that same aggregate's
`Result` is bound by the result match, not read out of the loop: the
loop's binding is local to the aggregate and after the fold holds only
the last match's value.

`Element` must be computable from the match: a variable of `Element`
that occurs neither in `Goal` nor among the shared variables is an
unbound name (`YCHR-40002`), as in a rule body.

A nested aggregate is computed at its place in the enclosing goal, so a
variable it shares with the enclosing goal must be bound by then, by a
conjunct to its left (or be an input of the enclosing aggregate). One
that only a later conjunct binds is an unbound name (`YCHR-40002`), as
for a `?` guard: write `(c(Y), \+ b(Y))`, not `(\+ b(Y), c(Y))`.
A later *nested aggregate* does not count here: as in a rule head, two
sibling aggregates may each have a local of the same name.


## Semantics

### Value of an aggregate

Given a match of the rule's regular heads, an aggregate is computed as
follows:

1. Evaluate `Agg`, giving `aggregator(Init, Inc, Final)`.
2. Enumerate every match of `Goal` against the current store. The store
   here includes the rule's own head constraints and the constraint
   being activated: a rule with aggregates stores its active constraint
   before computing them (see [Implementation notes](#implementation-notes)),
   so `c(X), count(c(_), N)` counts the `c` in the head too, and a goal
   occurrence counts the constraint it was activated by. Matches are
   enumerated in *goal order*, defined below.
3. Fold: `W0 = Init`, `Wi = Inc(Wi−1, Element_i)` for each match `i`,
   where `Element_i` is `Element` evaluated under that match.
4. `Final(Wn)`: `nothing` makes the aggregate undefined and the rule
   inapplicable; `just(R)` makes `R` its result.
5. Match `Result` against `R`. The pattern is head-matched: a literal,
   a compound shape or a repeated variable is a test, and a variable the
   pattern has not bound yet is bound. A failed match makes the rule
   inapplicable.

**Goal order** is nested-loop order over the goal's constraint
conjuncts, left to right. The first conjunct's matching constraints
are taken in store order (the order they were told). For each of them,
the second conjunct's matches are taken in store order, and so on. A
nested aggregate contributes no loop of its own; it is computed in
place for each partial match. For `collect(X, (a(Y), b(Y, X)), L)`,
the `b` constraints matching the first `a` come first, in store order,
then those matching the second `a`.

A nested aggregate acts as a filter on the partial match it is computed
for: if it is undefined, or its `Result` does not match, that partial
match is not extended. Otherwise its result (or, for `argmin`/`argmax`,
its goal variables) is bound for the conjuncts after it and for the
enclosing `Element`.

Because matches are enumerated in goal order, a non-commutative `Inc`
(as in `collect`) gives a deterministic result.

Several aggregates in one head are computed left to right, after the
regular heads are matched and before the rule's guard is checked; the
guard and body see every result.

### Errors

A runtime error raised by `Agg`, `Element`, `Inc` or `Final`, or by a
goal's guard, aborts as in any other expression position. An
*instantiation* error (an unbound variable reaching a demand point)
makes the whole aggregate undefined, so the rule does not apply, as
for [soft guard failure](language.md#soft-guard-failure). It does not
silently drop the one match that raised it.

### Fire once

A rule with aggregates fires at most once per combination of regular
head constraints, whatever its kind. Every such rule has a propagation
history, and it records the regular heads only, as in the paper's
ωt (Apply′). Keeping that history is what makes the "at most once"
hold: the history is recorded for a rule of *any* kind — a
simplification and a simpagation too, not just a propagation — as soon
as its head carries an aggregate. If an aggregate's value changes after
the rule fired, the rule does not fire again for the same heads:

- In the banking example, a client is made platinum once; a later
  withdrawal does not derive `platinum` again, and nothing retracts
  it.
- `c(X) \ count(d(X), N) <=> N > 3 | alarm(X)` removes nothing, since
  an aggregate keeps its goal's constraints. It raises the alarm once
  per `c(X)`, not on every later `d`.
- A rule that removes a regular head can match that combination only
  once anyway, so for it the history changes nothing.

This differs from the fire-many semantics of negation as absence in
CHR¬, where a rule fires again each time the negated head becomes
absent.

A rule must have at least one regular head conjunct.

### Selection aggregates

`argmin(X, Goal)` and `argmax(X, Goal)` are core forms, not
aggregators. `argmin(X, Goal)` matches `Goal` like ordinary head
conjuncts, restricted to the matches whose `X` is minimal. The
variables of `Goal` are not local; they are visible to the rest of the
rule. The matches it selects are those of

```prolog
Goal, \+ (Goal', ? X' < X)
```

(in notation, not YCHR syntax), where `Goal'` and `X'` are `Goal` and
`X` with `Goal`'s fresh variables renamed apart. `X` is compared with
the prelude's `<`, so it must be an `int`, a `float` or a `string`.
On ties, the rule fires with the first minimal match in goal order.

The equivalence fixes which match is selected and which variables are
visible, nothing else. `Goal` is still an aggregate goal:

- its constraints are kept;
- they are goal occurrences, not head occurrences
  ([Extension of ωr](#extension-of-ωr));
- they are not recorded in the propagation history.

So `p(K), argmin(X, item(K, X)) ==> best(K, X)` fires once per
`p(K)`, as for any other aggregate, not once for each `item` that is
the minimum at some point.

`takemin(X, Goal)` and `takemax(X, Goal)` are the same, but the
constraints of the selected match are removed when the rule fires.

Every other aggregate keeps its goal's constraints, whatever side of
`\` or `<=>` the aggregate is written on.


## Extension of ωr

YCHR executes rules under the refined operational semantics ωr
(Duck et al., 2004). Aggregates extend ωr in three places and leave
the rest unchanged.

### 1. Applicability

Under ωr a rule applies to a match of its heads whose guard succeeds.
A rule with aggregates also requires every aggregate to be defined and
its `Result` to match (see [Value of an aggregate](#value-of-an-aggregate)).
This is the paper's `matchings'` (Defs. 3–4). It is the only condition
that reads the store beyond a rule's own heads.

### 2. Goal occurrences

Every CHR constraint conjunct of an aggregate goal is a *goal
occurrence* of its constraint type, alongside the type's ordinary
head occurrences. When a constraint is active, because it was told or
reactivated, its goal occurrences are tried like any other occurrence.
Trying a goal occurrence means:

1. Match the active constraint against the conjunct.
2. Find matches for the remaining conjuncts and guards of the same
   aggregate goal, then for those of every enclosing aggregate goal,
   then for the rule's regular heads. (The compiler's location phase may
   skip the guards — the next step recomputes the aggregate and enforces
   them — so this step may over-approximate.)
3. Keep only the regular head constraints of each match found, and
   discard every binding of an aggregate goal's variables. For each
   *distinct* combination of regular heads, in the order first found,
   try the rule as usual: compute every aggregate from scratch
   (re-selecting, for a selection form), check the guard and the
   propagation history, and fire.

A goal occurrence only *locates* the combinations of regular heads
the active constraint may affect. The active constraint is not a head
of the rule, so firing does not remove it as a goal constraint. It can
still disappear: a match may also match it as one of the rule's
removed regular heads, and that head's removal takes it, just as a
`takemin`/`takemax` re-selection does. It never enters the propagation
history.

**Order.** Goal occurrences are numbered with the ordinary ones. A
rule's ordinary occurrences are numbered first, in ωr order — its
removed heads before its kept ones, right-to-left within each group —
and the rule's goal occurrences follow them. Within one rule, a goal
occurrence therefore comes after all of the rule's regular occurrences
of the same type, and the rule's ωr occurrence order is unchanged.
Among themselves the goal occurrences are numbered with the source
order of the goals, an aggregate's own goal before the goals of the
aggregates nested in it.

### 3. The removal step

When a rule fires and removes constraints, the first thing its body
does, before its first goal, is the *removal step*. This happens even
if the body is `true`. For each removed constraint whose type has goal
occurrences, the removal step tries each of those goal occurrences, in
occurrence order, as in §2. The removed constraints are taken in the
textual order of the removed heads, followed by the constraints a
`takemin`/`takemax` removed, in the textual order of the selection
forms and then in goal order. A removed constraint is matched against
the conjunct as if it were active, only to locate regular heads; it is
no longer in the store, so no fold counts it.

A rule firing inside the removal step is an ordinary firing, so its
own removals have their own removal steps. When the removal step ends,
the body runs from its first goal in ωr order.

**Self-triggering.** The removal step includes the firing rule's own
goal occurrences, as the paper's transformation does. A rule that
removes a constraint its own aggregates observe, through
`takemin`/`takemax` or an ordinary removed head, is therefore tried
again before its own body runs. Without this, firings would be lost.
This rule walks a dependency chain `a ← b ← c` only because of it:

```prolog
step @ task(T), \+ depends(T, _) \ depends(U, T) <=> released(U, T).
```

Firing for `a` removes `depends(b, a)`, which makes the rule
applicable for `task(b)`. Only the removal step retries `task(b)`.

The consequence is nesting. The firing for `b` happens inside the
removal step of the firing for `a`, before that firing's body, so
`released(c, b)` is told before `released(b, a)`, at a recursion depth
equal to the length of the chain.

**Loops over a selection form.** Because of [fire once](#fire-once),
a rule with kept regular heads takes one selection per combination:

```prolog
machine(M) \ takemin(D, job(M, D, J)) <=> run(M, J).
```

runs one job per `machine(M)`, not all of them. To drain the jobs,
remove a driver constraint in the same rule and tell it again at the
end of the body:

```prolog
next(M), machine(M) \ takemin(D, job(M, D, J)) <=> run(M, J), next(M).
```

Each `next(M)` is a new constraint, so each iteration is a new
combination of regular heads. With `next(M)` removed, the removal step
finds no regular head to match and does nothing, and the body's
`next(M)` starts the next iteration after `run/2` is told, so jobs run
shortest first. The paper's Sudoku solver uses the same idiom with its
`solve` constraint.

Without the removal step, `\+`, `forall` and `min` would never
notice a constraint going away:

```prolog
task(T), \+ depends(T, _) ==> ready(T).
done(D) \ depends(_, D) <=> true.
```

`ready(T)` is derived when the last dependency of `T` is removed, by
the removal step of the second rule.

Because the removal step runs before the body, an update written as
remove-then-tell shows aggregates an intermediate state. In

```prolog
withdraw(A, X), account(A, C, T, B) <=> account(A, C, T, B - X).
```

rules aggregating over `account` are tried once with the account
missing, before the new one is told. A rule whose guard bounds an
aggregate from above (`S < 1000`) can fire on that intermediate state.
This is the paper's semantics. To avoid it, keep the head and update
it in place, or make the guard robust to the intermediate value.

### What does not change

The extension is *conservative*.

- **Without aggregates.** A program without aggregates has no goal
  occurrences and no removal steps, and §1 reduces to the ωr
  condition, so it runs exactly under ωr. The compiler generates the
  same code it generates today.
- **With aggregates.** The changes are bounded by two static facts.
  Only a constraint type that appears in some aggregate goal gains
  occurrences. Only a rule that may remove such a constraint gains a
  removal step. Every other constraint type is activated exactly as
  under ωr, and every other rule's own firing is unchanged, though
  the firings a removal step adds can change when it is reached.
  Adding an aggregate affects the rest of a program the way adding an
  ordinary rule does.


## Predefined aggregates

`library(aggregates)` defines the aggregator constructor and the macros
below, over `aggregate/4`. (The four selection forms are core forms and
need no library.)

| Macro | Result |
|---|---|
| `count(G, N)` | the number of matches of `G` (`int`) |
| `sum(X, G, S)` | the sum of `X` over the matches (`int`) |
| `prod(X, G, P)` | the product of `X` over the matches (`int`) |
| `avg(X, G, A)` | the mean of `X` (`int` elements, `float` result); undefined if there are no matches |
| `fsum(X, G, S)` | `sum` over `float` |
| `fprod(X, G, P)` | `prod` over `float` |
| `favg(X, G, A)` | `avg` over `float` |
| `min(X, G, M)` | the minimum of `X` (`int`, `float` or `string`); undefined if there are no matches |
| `max(X, G, M)` | the maximum of `X` (`int`, `float` or `string`); undefined if there are no matches |
| `collect(X, G, L)` | the list of `X` over the matches, in goal order (`list(T)` for `X : T`) |
| `exists(G)` | holds if `G` has at least one match |
| `\+ G` | holds if `G` has no match (negation as absence) |
| `forall(G, C)` | holds if every match of `G` extends to a match of `C`; defined as `\+ (G, \+ C)` |

The integer and float folds are separate macros because an empty fold
returns its seed (`0`, `1`), and one aggregator cannot return `0` for
`int` and `0.0` for `float`: YCHR has no dispatch on types.

`exists` and `\+` are aggregates whose `Final` returns `nothing`
when the condition fails, so they need no guard. The macro passes `_`
as `Result`, so the value the aggregate computes is never observed;
only whether it is defined matters.

Each macro refers to its aggregator by qualified name, as
[macros.md](macros.md#names-and-modules) requires of a library macro.

The library also exports two prefix operators, `op(900, fy, '\\+')`
and `op(900, fy, '?')`. At 900 they bind tighter than `,` (1000), so
`\+ p(X), q(X)` is `(\+ p(X)), q(X)`, and looser than comparisons, so
`? X > 1` is `?(X > 1)`. A module that imports the library with an
import list must list them to use the operator syntax. Outside
operator syntax the functors are written quoted, `'\\+'(G)` and
`'?'(G)`, which works with or without the operators. A REPL query is
parsed with the union of every loaded module's operator exports, so
both operators are visible in a query whether or not the query's module
imports them individually (see [language.md](language.md)).


## Interaction with other features

- **Constraint use.** A constraint in an aggregate goal is a kept
  occurrence for [`:- constraint_use`](type-system.md#constraint-use-checking),
  or a removed one inside `takemin`/`takemax`, and YCHR-45001 applies
  as usual. So a `tell_only` constraint cannot occur in an aggregate
  goal, and an `event` constraint only inside `takemin`/`takemax`.
- **`library(search)`.** Nothing to add: an on-demand aggregate keeps
  no state between attempts, so undo has nothing to restore.
- **Scheme backend.** Supported. Aggregates compile to existing VM
  constructs; see below.


## Implementation notes

The paper compiles an aggregate into a guard that tells auxiliary CHR
constraints. That depends on Prolog guard backtracking and on CHR
constraints in guards, and YCHR has neither. Instead, the compiler
lowers an aggregate in the occurrence procedure itself:

- An aggregate is a compiler-generated procedure (named
  `$aggregate:aggregate_<rule>_<index>`, so no user function collides
  with it): a nested `Foreach` over the goal's constraints, with the
  shared variables as index conditions and the variables an earlier
  conjunct bound, folding into a local with `AssignVal`. It returns the
  result or `nothing`. The occurrence calls it inside a `BSoftGuard`,
  so an instantiation error anywhere in the fold makes the aggregate
  undefined; `BSoftGuard` wraps a `BoolExpr`, so it cannot enclose the
  loop directly. No new VM instruction is needed.
- Two conjuncts of the same type inside one goal must match different
  suspensions, like two head conjuncts of the same type, and the fold's
  loops test that. A goal conjunct and a regular head are deliberately
  *not* compared: a goal partner may be the same suspension as a
  regular head. Nor are two conjuncts of different goals, an enclosing
  one and a nested one: in `count((c(X), exists(c(X))), N)` a single
  `c(1)` matches both.
- A nested aggregate is a procedure of its own (its name adds its goal
  position to the enclosing one's). The enclosing fold calls it in place,
  in its innermost block so far, with the variables bound there as
  inputs. The call has no `BSoftGuard` of its own: an instantiation error
  inside it reaches the one around the top-level aggregate, so the whole
  aggregate is undefined, as [Errors](#errors) requires.
- The result pattern is checked in the aggregate procedure's tail: every
  test runs before any out-cell is bound, so a pattern that cannot match
  leaves nothing half-done. A repeated variable is tested against its
  first occurrence, and a fresh one is bound through an out-cell.
- A `?` guard in a goal is evaluated in place in the fold; an
  instantiation error inside it propagates to the `BSoftGuard` around the
  aggregate call, so the aggregate is undefined, as
  [Errors](#errors) requires. The location phase evaluates no `?` guard
  at all. A guard there can be inconclusive — a shared input is not
  bound yet, or a matched argument is still unbound — and skipping the
  combination would lose a firing that the fold, run later against a
  different store, would have found (a removal can make the fold
  defined). Dropping every guard is a true over-approximation: it can
  only try more combinations, since the fold still enforces the guard.
- A [goal occurrence](#2-goal-occurrences) is an ordinary occurrence
  procedure with two differences. First, its loops are the goal's
  conjuncts, nested outside the partner loops that search the regular
  heads. A regular head's value is therefore not bound yet when a goal
  loop evaluates, so every goal argument — including one shared with a
  regular head — is treated as a local. The fire step recomputes the
  aggregates from the regular heads and discards the goal's bindings,
  so a pairing the goal does not really support is only an extra try,
  never a wrong answer. Second, it takes a trailing `$removal` flag,
  explained below.
- For a conjunct of a nested goal, the location phase loops the rest of
  that goal, then each enclosing goal from the innermost outward, then
  the regular heads. It skips every nested aggregate it meets, as it
  skips a `?` guard: an aggregate only filters, and the fire step
  recomputes it. A variable that aggregate would bind is then bound by
  the next conjunct that mentions it. Going out from a nested goal to
  the goal around it, only the nested aggregate's shared inputs stay
  bound. Its other variables are its locals or its outputs (a result
  that also occurs in its goal, a selection's goal variables), whose
  value the fold takes from the whole nested goal, not from the
  constraint being tried. So again the phase can only try more
  combinations.
- **Late Storage.** An active constraint is unstored until Late
  Storage, so a fold that only read the store would miss the very
  constraint being activated. Every occurrence of a rule with
  aggregates therefore emits `Store active` before the fold. For a goal
  occurrence the store is guarded by `BAlive`, because the removal step
  calls the same procedure with a constraint that is already dead; a
  dead constraint must not be stored, and the fold cannot count it
  because it is not in the store. The store is idempotent, and the
  partner loops have taken their snapshot before it, so storing the
  active cannot change the combinations they enumerate. A goal
  occurrence whose active constraint was already stored — a reactivated
  one — can therefore match it as a regular head, and vice versa: the
  goal distinctness rule compares two goal conjuncts, never a goal
  conjunct with a head. That is only an extra try, since the fire step
  recomputes the aggregates from the regular heads.
- The [removal step](#3-the-removal-step) is a call sequence at the
  start of the body of a rule that removes a constraint with goal
  occurrences: one call per goal occurrence of each removed head's
  type, in the textual order of the removed heads. It is emitted
  whether or not the firing rule has an aggregate of its own, and it
  includes the rule's own goal occurrences. The call passes the removed
  constraint, already dead, plus the trailing `$removal` flag; the
  procedure then skips its early-drop liveness test, which a dead
  active would otherwise trip after the first combination of regular
  heads. A removal step counts as a non-empty body, so the rule's kept
  active constraint is still stored before it. Nothing is added to the
  runtime's `Kill`.
- A rule with aggregates gets `BNotInHistory`/`AddHistory` over its
  regular heads whatever its kind, where a rule without aggregates has
  it only when it is a propagation rule. The history guard is emitted
  in front of the folds, since a combination that already fired must
  not refold.
- The history records one entry per combination of regular heads, as in
  ωr. A combination that several goal matches locate is tried for each
  of them, and the later tries are rejected by the history; the
  implementation does not deduplicate them before trying.
- Analyses that assume a rule observes only its own heads take goal
  occurrences into account. A type that appears in some aggregate goal
  gains occurrences, so it is not inert (it registers observers) and
  reactivating it retries those occurrences; an aggregate-goal
  constraint counts as a kept occurrence for
  [`:- constraint_use`](type-system.md#constraint-use-checking); and
  passive-occurrence detection is turned off for a rule with an
  aggregate, because both of its sources assume the ωr-earlier
  occurrence always fires first, which an aggregate's applicability
  condition can falsify. For a program without aggregates all of this
  is vacuous.
- A selection form is computed in two steps, because a procedure
  cannot hand a suspension back and the guard must stay read-only. Its
  procedure walks the goal's matches in goal order and keeps the first
  one with the smallest (largest) key, comparing with the host `<`
  (`>`); the first match is compared with itself, so an unbound key is
  an instantiation error even when there is only one match. It binds
  one out-cell per visible goal variable. For `takemin`/`takemax` it
  also binds the match's 1-based position in goal order. When the rule
  fires, before any `Kill`, the firing walks the same goal again with
  the same shared inputs, counts matches up to that position, and keeps
  the suspensions it lands on (loops labelled `selection_loop_<k>_<j>`,
  left with a `Break`). The store is the one the guard saw: the guard
  reads only, and the history write does not touch the store. Counting
  is exact, where matching the selected values again would not be (a
  NaN key is not equal to itself). The kills and the removal step then
  use those suspensions. Two take forms, or a take form and a removed
  head, may pick the same constraint; the second kill does nothing, and
  the removal step tries its goal occurrences twice, which the history
  makes harmless.
- A macro use inside an aggregate goal expands in place, like one in a
  head; each goal of the expansion is a conjunct again.

## Diagnostics

| Code | Name | Condition |
|---|---|---|
| YCHR-20039 | `AggregateOnlyHead` | A rule head consists of aggregates only. |
| YCHR-20040 | `AggregateOutsideHead` | `aggregate/4` or a selection form outside a rule head. |
| YCHR-20041 | `MalformedAggregateGoal` | A goal conjunct that is neither a constraint, an aggregate nor a `?` guard. |
| YCHR-20042 | `GuardOutsideAggregateGoal` | A `?` guard outside an aggregate goal. |
| YCHR-40002 | `UnboundVariable` | An `Element` variable the match cannot supply. |
| YCHR-40003 | `AggregateLocalEscapes` | A local variable of an aggregate used in the rule's guard or body. |
| YCHR-40004 | `AggregateNestedTake` | A `takemin`/`takemax` inside an aggregate goal. |
| YCHR-40005 | `AggregateResultNotMaybe` | The program declares no `maybe:just/1`, so no aggregator can produce the protocol's result type. |
| YCHR-60014 | `AggregateTypeEscapes` | A per-match type reaches the rule's scope ([type-system.md](type-system.md#escaping-types)). |
| YCHR-60015 | `AggregateLinkConflict` | A goal links one rigid type variable to two outer ones ([type-system.md](type-system.md#shared-variables-in-a-goal)). |
| YCHR-20106 | `AggregateGoalInaccessible` | Warning: an aggregate goal can never match ([type-system.md](type-system.md#goals-that-can-never-match)). |


## Not in this version

- **Incremental maintenance** (the paper's `#maintain` and `Dec`
  predicate). Every attempt recomputes the aggregate. Maintenance would
  add a fourth aggregator field and needs to work with search undo.
- **Early failure and early success**, sharing a maintained result
  between occurrences, and user pragmas in general.
- **Fire-many semantics**, for any aggregate.
- **Aggregates in guards, bodies or function equations.**
- **Nested `takemin`/`takemax`** (`YCHR-40004`). This one is not
  planned: see [Aggregate goals](#aggregate-goals).
- **`stddev`, `variance`.** They are easy to define as user
  aggregators.

