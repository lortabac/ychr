# YCHR Aggregates Specification

**Status: draft, not implemented.** None of the examples below run
yet.

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

`Element` has type `E` and `Result` type `R`. The full typing rules,
including goal-local variables, go in
[type-system.md](type-system.md) when this is implemented.


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
distinct variable, so a typo cannot silently change its meaning.

`Element` must be computable from the match: a variable of `Element`
that occurs neither in `Goal` nor among the shared variables is an
unbound name (`YCHR-40002`), as in a rule body.


## Semantics

### Value of an aggregate

Given a match of the rule's regular heads, an aggregate is computed as
follows:

1. Evaluate `Agg`, giving `aggregator(Init, Inc, Final)`.
2. Enumerate every match of `Goal` against the current store. The
   store here *includes* the rule's own head constraints, so
   `c(X), count(c(_), N)` counts the `c` in the head too. Matches are
   enumerated in *goal order*, defined below.
3. Fold: `W0 = Init`, `Wi = Inc(Wi−1, Element_i)` for each match `i`,
   where `Element_i` is `Element` evaluated under that match.
4. `Final(Wn)`: `nothing` makes the aggregate undefined and the rule
   inapplicable; `just(R)` makes `R` its result.
5. Match `Result` against `R`. A failed match makes the rule
   inapplicable.

**Goal order** is nested-loop order over the goal's constraint
conjuncts, left to right. The first conjunct's matching constraints
are taken in store order (the order they were told). For each of them,
the second conjunct's matches are taken in store order, and so on. A
nested aggregate contributes no loop of its own; it is computed in
place for each partial match. For `collect(X, (a(Y), b(Y, X)), L)`,
the `b` constraints matching the first `a` come first, in store order,
then those matching the second `a`.

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
ωt (Apply′). If an aggregate's value changes after the rule fired,
the rule does not fire again for the same heads:

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
the prelude's `<`, so it must be a number. On ties, the rule fires
with the first minimal match in goal order.

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
   then for the rule's regular heads.
3. Keep only the regular head constraints of each match found, and
   discard every binding of an aggregate goal's variables. For each
   *distinct* combination of regular heads, in the order first found,
   try the rule as usual: compute every aggregate from scratch
   (re-selecting, for a selection form), check the guard and the
   propagation history, and fire.

A goal occurrence only *locates* the combinations of regular heads
the active constraint may affect. The active constraint is not a head
of the rule. Firing does not remove it, except when a
`takemin`/`takemax` re-selects it, and it does not enter the
propagation history.

**Order.** Goal occurrences are numbered with the ordinary ones, top
to bottom by rule. Within one rule, they come after all of the rule's
regular occurrences of the same type, so the rule's ωr occurrence order
is unchanged. Among themselves they are numbered left to right, with
an aggregate's goal before the goals of the aggregates nested in it.

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

`library(aggregates)` defines the aggregator constructor, the four
selection forms, and these macros over `aggregate/4`:

| Macro | Result |
|---|---|
| `count(G, N)` | the number of matches of `G` |
| `sum(X, G, S)` | the sum of `X` over the matches |
| `prod(X, G, P)` | the product of `X` over the matches |
| `min(X, G, M)` | the minimum of `X`; undefined if there are no matches |
| `max(X, G, M)` | the maximum of `X`; undefined if there are no matches |
| `avg(X, G, A)` | the arithmetic mean of `X`; undefined if there are no matches |
| `collect(X, G, L)` | the list of `X` over the matches, in goal order |
| `exists(G)` | holds if `G` has at least one match |
| `\+ G` | holds if `G` has no match (negation as absence) |
| `forall(G, C)` | holds if every match of `G` extends to a match of `C`; defined as `\+ (G, \+ C)` |

`exists` and `\+` are aggregates whose `Final` returns `nothing`
when the condition fails, so they need no guard. Their result is
`true`, and the macro passes `_` as `Result`.

Each macro refers to its aggregator by qualified name, as
[macros.md](macros.md#names-and-modules) requires of a library macro.

The library also exports two prefix operators, `op(900, fy, '\\+')`
and `op(900, fy, '?')`. At 900 they bind tighter than `,` (1000), so
`\+ p(X), q(X)` is `(\+ p(X)), q(X)`, and looser than comparisons, so
`? X > 1` is `?(X > 1)`. A module that imports the library with an
import list must list them to use the operator syntax. Outside
operator syntax the functors are written quoted, `'\\+'(G)` and
`'?'(G)`, which works with or without the operators.


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

- An aggregate is a compiler-generated procedure: a nested `Foreach`
  over the goal's constraints, with the shared variables as index
  conditions, folding into a local with `AssignVal`. It returns the
  result or `nothing`. The occurrence calls it inside a `BSoftGuard`,
  so an instantiation error anywhere in the fold makes the aggregate
  undefined; `BSoftGuard` wraps a `BoolExpr`, so it cannot enclose the
  loop directly. No new VM instruction is needed.
- A [goal occurrence](#2-goal-occurrences) is an ordinary occurrence
  procedure. It searches for the rest of its goal and for the regular
  heads as partners, and it does not count the active constraint as a
  head.
- The [removal step](#3-the-removal-step) is a call, at the start of
  the body of every rule that may remove a constraint with goal
  occurrences, to one procedure per goal occurrence. The procedure
  takes the removed constraint as its argument. Nothing is added to
  the runtime's `Kill`.
- Late Storage: an active constraint that is not yet stored must
  still be counted, so the fold includes it explicitly while it is
  unstored. Once it is stored (a reactivated constraint is), the
  `Foreach` finds it and it must not be counted twice. Any firing that
  can run a body, including one from a goal occurrence, stores a kept
  active constraint before the body, and a removal step counts as a
  non-empty body.
- A rule with aggregates gets `BNotInHistory`/`AddHistory` over its
  regular heads whatever its kind, where today only propagation rules
  do. History elimination may still drop it for a rule that always
  removes a regular head.
- Analyses that assume a rule observes only its own heads have to take
  goal occurrences into account: passive-occurrence detection, inert
  types (a type with goal occurrences is not inert) and
  constraint-use checking. For a program without aggregates they see
  nothing new.

## Diagnostics

Codes are assigned at implementation.

| Name | Condition |
|---|---|
| `AggregateOutsideHead` | `aggregate/4` or a selection form outside a rule head. |
| `AggregateOnlyHead` | A rule head consists of aggregates only. |
| `MalformedAggregateGoal` | A goal conjunct that is neither a constraint, an aggregate nor a `?` guard. |
| `GuardOutsideAggregateGoal` | A `?` guard outside an aggregate goal. |
| `AggregateLocalEscapes` | A local variable of an aggregate used in the rule's guard or body. |


## Not in this version

- **Incremental maintenance** (the paper's `#maintain` and `Dec`
  predicate). Every attempt recomputes the aggregate. Maintenance would
  add a fourth aggregator field and needs to work with search undo.
- **Early failure and early success**, sharing a maintained result
  between occurrences, and user pragmas in general.
- **Fire-many semantics**, for any aggregate.
- **Aggregates in guards, bodies or function equations.**
- **`stddev`, `variance`.** They are easy to define as user
  aggregators.

