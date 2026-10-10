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
  - `Inc` — a closure `(W, E) -> W`, applied to the working value and
    one element;
  - `Final` — a closure `W -> maybe(R)`, turning the last working value
    into the result. `nothing` means the aggregate is *undefined* (the
    maximum of no elements, say) and the rule does not apply.
- `Element` is an expression, evaluated once per match of `Goal`.
- `Goal` is an *aggregate goal* (see [Aggregate goals](#aggregate-goals)).
- `Result` is a pattern, matched against the result.

User-defined aggregates are ordinary aggregators:

```prolog
:- function avg_inc/2, avg_final/1.
avg_inc(t(N, S), X) -> t(N + 1, S + X).
avg_final(t(0, _)) -> nothing.
avg_final(t(N, S)) | N > 0 -> just(S / N).

:- macro avg(E, G, R) --->
       aggregate(aggregates:aggregator(t(0, 0), fun avg_inc/2,
                                        fun avg_final/1), E, G, R).
```

### Typing

For an aggregator over elements of type `E` with working value `W`
and result `R`:

```
aggregator(W, (W, E) -> W, W -> maybe(R))
```

`Element` has type `E` and `Result` type `R`. The full typing rules,
including goal-local variables, go in
[type-system.md](type-system.md) when this is implemented.


## Aggregate goals

An aggregate goal is a conjunction of:

- CHR constraints;
- aggregates (nested aggregates);
- one optional trailing guard, written `Goal | Guard` as in a rule.

```prolog
count((employee(E, C), salary(E, S) | S > 1000), N)
```

The goal is a goal position for [macros](macros.md), so the
predefined aggregates may be nested:

```prolog
argmax(S, (client(C), sum(B, account(_, C, _, B), S)))
```

### Variables

A variable of an aggregate goal is *shared* if it also occurs in:

- the regular (non-aggregate) head conjuncts of the rule;
- an enclosing aggregate goal;
- the `Result` of an aggregate to its left in the same conjunction.

Every other variable is *local* to the goal: it is renamed apart per
match and is not visible to the rule's guard or body, nor to other
aggregates. Shared variables are inputs: matching the goal never binds
them, and a match must agree with their values (`==`, as for head
matching). `argmin` and `takemin` are the exception (see below).


## Semantics

### Value of an aggregate

Given a match of the rule's regular heads, an aggregate is computed as
follows:

1. Evaluate `Agg`, giving `aggregator(Init, Inc, Final)`.
2. Enumerate every match of `Goal` against the current store. The
   store here *includes* the rule's own head constraints, so
   `c(X), count(c(_), N)` counts the `c` in the head too. Matches are
   enumerated in store order.
3. Fold: `W0 = Init`, `Wi = Inc(Wi−1, Element_i)` for each match `i`,
   where `Element_i` is `Element` evaluated under that match.
4. `Final(Wn)`: `nothing` makes the aggregate undefined and the rule
   inapplicable; `just(R)` makes `R` its result.
5. Match `Result` against `R`. A failed match makes the rule
   inapplicable.

Because matches are enumerated in store order, a non-commutative
`Inc` (as in `collect`) gives a deterministic result.

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

### When a rule with an aggregate is tried

Under ωr a rule is tried when one of its head constraints is active.
A rule with aggregates is tried in three further situations:

1. **A regular head is active.** The aggregates are computed while
   matching, as above.
2. **A goal constraint is active.** A constraint that matches a
   constraint of an aggregate goal is active because it was told, or
   reactivated by a variable binding. The rule is tried with the
   regular heads as partners.
3. **A goal constraint is removed.** When a rule firing removes a
   constraint that matches a constraint of an aggregate goal, the
   rules containing that aggregate are tried, again with the regular
   heads as partners. Removals are processed at the start of the
   removing rule's body, before its first goal, in the order the
   constraints were removed.

Case 3 is what makes "no", "for all" and "minimum" behave as expected
when constraints go away:

```prolog
task(T), none(depends(T, _)) ==> ready(T).
done(D) \ depends(_, D) <=> true.
```

`ready(T)` is derived when the last dependency of `T` is removed.

A constraint that matches an aggregate goal is observed only through
the aggregate. It is not a head of the rule, it is never removed by it
(except for `takemin`), and it does not enter the propagation history.

### Fire once

A propagation rule fires at most once per combination of regular head
constraints, as without aggregates. Its propagation history records
the regular heads only. If an aggregate's value changes after the rule
fired, the rule does not fire again for the same heads. In the banking
example, a client is made platinum once; a later withdrawal does not
derive `platinum` again, and nothing retracts it.

This is the paper's choice. It differs from the fire-many semantics of
negation as absence in CHR¬, where a rule fires again each time the
negated head becomes absent.

A rule must have at least one regular head conjunct.

### Selection aggregates

`argmin(X, Goal)` and `argmax(X, Goal)` are core forms, not
aggregators. `argmin(X, Goal)` matches `Goal` like ordinary head
conjuncts, restricted to the matches whose `X` is minimal. The
variables of `Goal` are not local; they are visible to the rest of the
rule. It is equivalent to

```prolog
Goal, none((Goal', X' < X))
```

where `Goal'` and `X'` are `Goal` and `X` with `Goal`'s fresh variables
renamed apart. The constraints of `Goal` are kept. On ties, the rule
fires with whichever minimal match the join reaches first, in store
order.

`takemin(X, Goal)` and `takemax(X, Goal)` are the same, but the
constraints of the selected match are removed when the rule fires.

Every other aggregate keeps its goal's constraints, whatever side of
`\` or `<=>` the aggregate is written on.


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
| `collect(X, G, L)` | the list of `X` over the matches, in store order |
| `exists(G)` | holds if `G` has at least one match |
| `none(G)` | holds if `G` has no match |
| `forall(G, C)` | holds if every match of `G` extends to a match of `C`; defined as `none((G, none(C)))` |

`exists` and `none` are aggregates whose `Final` returns `nothing`
when the condition fails, so they need no guard. Their result is
`true`, and a use ignores it.

Each macro refers to its aggregator by qualified name, as
[macros.md](macros.md#names-and-modules) requires of a library macro.


## Interaction with other features

- **Constraint use.** A constraint in an aggregate goal is a kept
  occurrence for [`:- constraint_use`](type-system.md#constraint-use-checking),
  or a removed one inside `takemin`/`takemax`. A `tell_only`
  constraint cannot occur in an aggregate goal.
- **`library(search)`.** Nothing to add: an on-demand aggregate keeps
  no state between attempts, so undo has nothing to restore.
- **Scheme backend.** Supported. Aggregates compile to existing VM
  constructs; see below.


## Implementation notes

The paper compiles an aggregate into a guard that tells auxiliary CHR
constraints. That depends on Prolog guard backtracking and on CHR
constraints in guards, and YCHR has neither. Instead, the compiler
lowers an aggregate in the occurrence procedure itself:

- An aggregate is a nested `Foreach` over the goal's constraints, with
  the shared variables as index conditions. It folds into a local with
  `AssignVal`. No new VM instruction is needed.
- Case 2 of [when a rule is tried](#when-a-rule-with-an-aggregate-is-tried)
  is an extra occurrence procedure per goal constraint. It searches for
  the regular heads as partners and does not count the goal constraint
  as a head.
- Case 3 is a *removal occurrence*: a procedure the compiler calls from
  the start of the body of every rule that may remove a goal
  constraint. Nothing is added to the runtime's `Kill`.
- Late Storage: the active constraint is not yet stored when its
  occurrence runs, so the fold has to include it explicitly; a
  `Foreach` alone would miss it.


## Diagnostics

Codes are assigned at implementation.

| Name | Condition |
|---|---|
| `AggregateOutsideHead` | `aggregate/4` or a selection form outside a rule head. |
| `AggregateOnlyHead` | A rule head consists of aggregates only. |
| `MalformedAggregateGoal` | A goal conjunct that is neither a constraint nor an aggregate, or a guard that is not last. |
| `TellOnlyInAggregate` | A `tell_only` constraint in an aggregate goal. |


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


## Open questions

1. **Guard syntax in a goal.** This draft uses `Goal | Guard`, which
   mirrors a rule. The paper writes the guard as a conjunct,
   `?(Guard)`, which allows guards between constraints.
2. **When removals are processed.** Processing them at the start of the
   body follows the paper's implementation. It means an update written
   as remove-then-tell (`withdraw(A, X), account(A, C, T, B) <=>
   account(A, C, T, B - X)`) shows the aggregate an intermediate state
   in which the account is missing. Processing removals at the end of
   the body avoids that, but delays `none`-style rules past the body's
   own tells.
3. **Self-removal.** Should a rule that removes a constraint of its own
   aggregate's goal (with `takemin`, say) trigger its own removal
   occurrence?
4. **Spelling of `none`.** The paper's `\+` is not an operator in
   YCHR's default table. `none/1` avoids adding one.
