# YCHR Search Specification (`library(search)`)

> **Audience:** readers writing a labeling, generate-and-test or
> enumeration program in YCHR, and anyone working on the search driver
> itself.
> **You will:** find the choice-at-quiescence execution model, the
> commit and undo rules, how failure differs from error, how goal
> disjunction (`;`) lowers, and the exact edge-case behaviour of every
> primitive.
> **Skip if:** you only need deterministic CHR — nothing here applies
> to a program that never imports `library(search)`.

This document specifies *search*: an opt-in, explicitly driven
exploration of alternative branches, provided by the standard library
module `search` and implemented in the Haskell runtime. Search is
**not** pervasive backtracking. A program that does not run a search
executes exactly as it does today, under the refined operational
semantics (ωr), with no VM changes and no per-step bookkeeping.

Search generalizes a pattern YCHR already relies on: try a candidate,
keep it if the computation survives, otherwise discard everything it
did and try the next one. The type checker's resolution of overloaded
signatures does exactly that today, one throwaway sub-session
(`run_chr_session/1`) per candidate signature, with no way to undo a
binding it made. One possible further use is a finite-domain solver:
propagate to quiescence, label one variable, propagate again,
backtrack on failure.

**Availability.** Haskell interpreter only. The Scheme backend does
not implement the search host calls; a program that uses them fails to
run there. This mirrors `run_chr_session/1` (see
[`dev-docs/SCHEME_BACKEND_GAPS.md`](../../dev-docs/SCHEME_BACKEND_GAPS.md)).


## Overview

Search is built from these pieces:

| Piece | Kind | Role |
|---|---|---|
| `alt/1` | CHR constraint, **no rules** | The primitive choice point: a list of alternative goals. Sits inert in the store. |
| `;` | body operator | Surface syntax for a choice between two rule-body conjunctions. Lowers to `alt/1`. |
| `choose/2` | CHR constraint, **derived** | Labeling: bind one variable to one of a list of values. One rule over `alt` and `try_unify`. |
| `fail/0` | function | Fails the current branch. |
| `try_unify/2` | CHR constraint | Prolog's `=`: unify, or fail the branch. |
| `solve/1` | function | Runs a goal; commits to its first solution. |
| `find_all/2` | function | Runs a goal; collects a copy of a template per solution, then undoes everything. |
| `fold_solutions/4` | function | Folds a function over the solutions, in search order, with early exit. |
| `forall/3` | function | Derived from `fold_solutions`: does every solution satisfy a predicate? |
| `find_n/3` | function | Derived from `fold_solutions`: the first *N* solutions. Terminates on an infinite space. |

The execution model is *choice at quiescence* (labeling), not
continuation capture:

1. A search entry point forks a sub-session and tells the goal,
   running it to quiescence under the ordinary ωr semantics.
2. At quiescence the driver looks in the store for an alive
   `search:alt/1` constraint. If there is none, the current state is a
   **solution**.
3. Otherwise it takes the *oldest* such constraint, `alt(Goals)`, and
   tries each element of `Goals` in list order: kill the `alt`, tell
   the goal, and recurse from step 2.
4. If a branch fails, everything the branch did is undone and the next
   alternative is tried. When the alternatives run out, the failure
   propagates to the enclosing choice point (or out of the driver).

There is no continuation to capture because the continuation after a
choice is always "tell this goal and propagate to quiescence", which
the driver invokes itself. This is how labeling works in CHR
generally: propagate to fixpoint, label, repeat.


## The `search` module

```prolog
:- use_module(library(search)).
```

exports

```prolog
:- chr_constraint alt(list(any)), choose(any, list(any)), try_unify(any, any).

:- chr_type step(A) ---> continue(A) ; stop(A) ; commit(A).

:- function
    (fail() -> any),
    (solve(any) -> bool),
    (find_all(T, any) -> list(T)),
    (fold_solutions(T, any, fun(T, A) -> step(A) end, A) -> A),
    (forall(T, any, fun(T) -> bool end) -> bool),
    (find_n(int, T, any) -> list(T)).
```

`alt/1` has **no rules**. Telling it simply stores it. The runtime
recognizes it by its qualified name `search:alt` at arity 1 — one
wired-in name, like `'$call'`. This is *provisional*: a general
mechanism for a library to nominate a constraint to the runtime would
replace it without changing the surface language.

Everything else in the module is ordinary CHR and ordinary functions,
defined in the library itself.


## Scope: search runs in a sub-session

`solve(quote(Goal))`, `find_all(Template, quote(Goal))` and
`fold_solutions(Template, quote(Goal), F, Acc0)` run `Goal` in a
**fresh session of the current program** — its own constraint store,
propagation history, reactivation queue, and call stack, with the same
rules, functions, host calls, and exports. This is exactly
`run_chr_session/1`'s fork, and it inherits that model verbatim:

- **The caller's store is not searched.** Constraints already stored
  in the calling session are invisible to the goal, and constraints
  the goal stores are invisible to the caller. Search explores the
  goal, not the ambient program state.
- **Goal shape.** `Goal` is a single constraint term, a list of them
  told in order, or a disjunction (see
  [Dynamic disjunction](#dynamic-disjunction)), wrapped in `quote/1`
  to keep it symbolic.
- **Goal resolution is a caller error.** Goal constraint names are
  resolved through the program's exports *in the calling session*
  before the search starts, so an unknown, unexported, or
  wrong-arity goal constraint is a loud runtime error — never a
  `false` result and never a failed branch.
- **Variable sharing is the result channel.** Logical variables are
  mutable cells, so a variable reachable from the goal is the same
  variable inside the search. Bindings that survive (see
  [Commit](#commit-and-undo)) are readable afterwards.
- **Reactivation does not cross the boundary.** A *live* stored
  constraint of the calling session that observes a variable the
  search binds is not reactivated. Pass ground terms and fresh
  variables in; read results out.


## Choice points

### Selection order

At quiescence the driver scans the store for suspensions of type
`search:alt/1` that are still alive, and takes the **oldest** — first
by store insertion order. Alternatives are tried in **list order**,
left to right. Search is therefore depth-first and fully
deterministic: for a given program and goal, the sequence of solutions
is fixed.

Nothing prevents a rule from removing or rewriting an `alt` constraint
before the driver sees it — `alt` is an ordinary constraint, and a
rule with `alt([G]) <=> ...` is a legitimate (if pointless) way to
make a unary choice deterministic. The driver only ever considers what
is alive and stored at quiescence.

### Firing a choice

For alternative `G` of `alt(Goals)` the driver, in order:

1. takes a trail mark and snapshots the store refs (see
   [Undo](#commit-and-undo));
2. kills the `alt` constraint, so an alternative cannot rediscover its
   own choice point and recurse forever;
3. **tells** `G` — one constraint, or each element of a list in order,
   or a nested `alt` when `G` is a `;` compound;
4. recurses into step 2 of the overview.

Telling a goal runs the ordinary VM activation path, which drains the
reactivation queue itself, so the driver adds nothing on top.

Each alternative is a *goal*, not a value: the choice is between
computations, not between bindings. Binding a variable is one
computation among others, which is why `choose/2` is derived rather
than primitive.

### Goal names inside a choice point

Alternatives are resolved when the choice is fired, not when the `alt`
was told, and a *qualified* name is taken at its word — no export
check. Disjuncts lifted out of a `;` are module-internal constraints
that no module exports, and they have to be reachable.

An *unqualified* name still goes through the export list, because
nothing at the choice point says which module wrote it. So an
alternative naming a constraint the module keeps to itself has to be
spelled `mod:name`:

```prolog
pick(X) <=> alt([quote(mine:hidden(X, 1)), quote(mine:hidden(X, 2))]).
```

Either way, a name that resolves to no tell procedure is a runtime
error, never a failure.

### `choose/2`, derived

`choose(X, Alts)` binds `X` to one of the values in `Alts`. It is one
library rule:

```prolog
choose(X, Alts) <=> alt(maplist(fun(A) -> quote(try_unify(X, A)) end, Alts)).
```

Three consequences worth stating, because they are visible:

- `choose` does **not** sit in the store. The rule fires at tell time
  and what is stored is the `alt`. A rule of yours can intercept
  `alt`, not `choose`.
- A non-member alternative fails through `try_unify/2`, so the
  backtrack reason is `fail`.
- A non-list `Alts` is a runtime error inside `maplist` at *tell*
  time, not at the choice point.

The driver may later recognize `choose` directly as a fast path — it
is the labeling primitive, and the extra constraint tell plus closure
call per alternative is a measurable constant. That is an
optimization, not a semantic change, and it is not done today.

### ωr interaction

Each branch inherits the store, the propagation history, and the
reactivation queue as they stood at the choice point, and all three are
restored when the branch is undone. Two consequences worth stating:

- A rule that fired in a failed branch is **not** recorded as fired in
  the next alternative: the history snapshot is rolled back with
  everything else, so the same propagation rule fires again if the
  next alternative reaches the same match.
- A rule that fired *before* the choice point stays recorded in every
  branch, which is what keeps a propagation rule from re-firing per
  alternative.

Within a branch, ωr is unchanged: the branch is an ordinary CHR
computation run to quiescence.


## Disjunction (`;`)

`;` is an infix body operator (`xfy`, priority 1100, so it binds
looser than `,`). Each side is an ordinary body conjunction:

```prolog
h(X) <=> p(X), (b(X) ; c(Y), d(X, Y)), q(X).
```

A module that writes `;` in a rule body must import `library(search)`;
otherwise the disjunction is rejected as `YCHR-20021`
(`DisjunctionWithoutSearch`). The `search:alt` reference is generated
rather than written, so qualifying is not an escape here.

`;` belongs to a rule body and nowhere else. In a guard, an `is`
right-hand side, or a function body there are no goals to choose
between, and a `;` there is rejected as `YCHR-20022`
(`DisjunctionNotInRuleBody`). Inside `quote/1` it stays ordinary data,
which is what makes the dynamic form below work.

### Choice is still at quiescence

**`;` does not branch where it is written.** It tells an `alt`
constraint, which sits in the store until the goal reaches quiescence.
In `p(X), (b(X) ; c(X)), q(X)` the goal `q(X)` is told — and runs to
completion — *before* either branch is picked. Same ωr fixpoint,
different order than Prolog's left-to-right resolution.

This is the single most important thing to know about `;` in YCHR. It
is not a control-flow construct that suspends the rest of the body; it
is a constraint that records what is left to decide.

### Variables

A disjunct may mention any variable of the enclosing rule — head,
guard, or body — and may introduce fresh ones. Variables shared with
the rest of the rule are shared in the ordinary way: a binding a
branch makes is visible to constraints told before or after the
disjunction, and is undone with the branch.

A variable that occurs only inside one disjunct is still allocated
once, before the choice, so it is the same variable in every
alternative that mentions it and it survives into code after the
disjunction:

```prolog
h(X) <=> (a(Y) ; b(Y)), c(Y).
```

`c(Y)` is told with `Y` unbound, before the branch is picked, and is
reactivated if the branch binds `Y`.

### `=` stays strict

A failing `X = Y` inside a disjunct is a **runtime error**, exactly as
it is anywhere else in a rule body (see
[Failing unification](#failing-unification)). Disjunction does not
turn a bug into a dead end. Write `try_unify(X, Y)` when a mismatch is
a dead end, or `choose(X, [...])` when the disjunction is over values
rather than goals. The error message names both.

### Lowering

Every disjunct is lifted into its own constraint, exactly the way
lambdas are lifted into their own functions. This is *explanatory* —
the lifted names are internal and not part of the language — but it
pins the semantics precisely:

```prolog
h(X) <=> p(X), (b(X) ; c(Y), d(X, Y)), q(X).
% ==>
h(X) <=> p(X), alt([quote('__disj_1'(X)), quote('__disj_2'(X, Y))]), q(X).
'__disj_1'(X)    <=> b(X).
'__disj_2'(X, Y) <=> c(Y), d(X, Y).
```

A disjunct's parameters are the variables it shares with the enclosing
rule's scope, sorted ascending — the same rule lambda lifting uses for
captured variables. The lifted constraints are declared arity-only
(every argument `any`); the type checker has already checked each
disjunct in place, against the enclosing rule's typing, before this
runs.

Nesting needs no special treatment: an inner `;` lowers to an inner
`alt`, which is told inside the chosen branch and therefore picked at
*that* branch's next quiescence.

### Dynamic disjunction

Inside `quote/1` a `;` compound stays symbolic data, and the driver
interprets it when it reads the goal:

```prolog
Ok is solve(quote((p(X) ; q(X)))).
```

Each side is a goal in the dynamic sense — a constraint term, a list
of them, or a further `;` — so a conjunction has to be written as a
list, `quote((p(X) ; [q(X), r(X)]))`. This is the only form of `;`
available at the top level of a query: a query is not a rule body and
has no place to lift a disjunct to, so a bare `;` in a query is
rejected as `YCHR-30006` (`DisjunctionInQuery`).


## Failure and error

Search distinguishes **failure** — an ordinary control-flow outcome,
scoped to the current branch — from **error**, which is not.

### `fail/0`

`fail` fails the innermost enclosing branch. It never returns, so its
declared result type (`any`) is never inhabited; write it in body
position (`... <=> fail.`) or as the right-hand side of a conditional
expression.

Calling `fail` when **no search is active** is a runtime error
(`YCHR-60001`, message `fail/0 outside a search`) — loud, not silent
success and not a stuck query.

### Runtime errors propagate

A runtime error raised inside a branch — arithmetic on a non-number, a
failing body unification, no matching equation — is **not** a branch
failure. It unwinds out of the search entirely and reaches the caller
unchanged. This is deliberately *unlike* `run_chr_session/1`, which
maps every error to `false`: conflating a bug with a dead end is
exactly what makes generate-and-test programs undebuggable.

Bindings are still rolled back to the search's base mark before the
error propagates (ISO `catch/3`-style rollback), so a caller that
catches the error — for instance an enclosing `run_chr_session/1`,
which turns it into `false` — resumes with the variables it had.

### What can fail a branch

Exactly two things:

1. An explicit `fail/0` — including via `try_unify/2` and therefore
   via `choose/2`, both of which are defined in terms of it.
2. Exhaustion: an `alt` whose alternatives have all been tried, which
   includes `alt([])` and `choose(X, [])`.

In particular, a **failing unification in a rule body remains a runtime
error**, not a branch failure — see below.

### Failing unification

`X = Y` in a rule body is a hard runtime error when the two sides
cannot be unified (`YCHR-60001`, `unification failure: cannot
unify …`). Search does not change that. A body `=` that can never
succeed is a bug in the rule, and turning it into a silent dead end
would trade a diagnostic for a wrong answer with no way to get the
diagnostic back.

Prolog's `=`, which fails rather than erroring, is available as a
separate constraint:

```prolog
:- chr_constraint try_unify(any, any).

try_unify(X, Y) <=> unifiable(X, Y) | X = Y.
try_unify(_, _) <=> fail.
```

That is the whole definition — ordinary CHR over the prelude's
`unifiable/2`, with no runtime support of its own. Write
`try_unify(X, Y)` in a rule body wherever a mismatch should be a dead
end rather than a bug:

```prolog
place(X, Y) <=> choose(X, [1, 2, 3]), try_unify(Y, X).
```

`unifiable/2` binds nothing, so the guard never leaves a half-done
binding behind, and it never raises an instantiation error — an
unbound operand simply means "yes, these can unify".

Because `try_unify/2` fails via `fail/0`, calling it **outside a
search** is the same error as calling `fail/0` outside a search. The
message names `fail/0` rather than `try_unify/2`; the call stack on
the error identifies the rule.

### Interaction with `run_chr_session/1`

A branch failure is **contained** by a `run_chr_session/1` boundary:
the sub-session returns `false`, and the enclosing search branch
carries on. Failure does not escape a sub-session any more than a
runtime error does.

This makes `run_chr_session`'s contract total, and simpler than it was
before search existed: it returns **`true` if and only if the goal ran
to quiescence**, and `false` otherwise — runtime error or branch
failure alike. For a program that never uses search the behaviour is
unchanged, since a branch failure cannot arise without one.

The cost is that `false` no longer distinguishes "the goal hit a bug"
from "the goal deliberately failed". That is the conflation
`run_chr_session` already made for errors, and it is bounded here in a
way it is not for search itself: the caller gets a boolean it must
test, rather than a computation that silently continues.

Bindings the sub-session made before failing are **not** rolled back,
exactly as they are not when it errors. `run_chr_session` has no
choice point and takes no mark; a caller that needs the bindings
undone should run the sub-session inside a search branch, where the
enclosing driver's marks cover it.


## Commit and undo

### Undo mechanism

Everything a branch does is undone by two mechanisms:

- **Snapshot** for the store refs — the type-indexed store, the
  suspension map, the propagation history, and the reactivation queue.
  All four hold *persistent* structures behind an `IORef`, so a
  snapshot is a pointer read and a restore is a pointer write.
- **A trail** for the mutable cells a snapshot cannot reach: logical
  variable cells (bindings *and* observer-list updates) and the
  `alive` / `stored` flags on suspensions. Every write to those cells
  records its previous contents; unwinding replays them in reverse.

The variable counter and the suspension-id counter are **not** rolled
back. They stay monotonic across backtracking, so an id allocated in
an abandoned branch is never reused — which is what keeps a stale
observer id in some other session from silently reactivating an
unrelated constraint.

### One shared trail, marks per choice point

There is **one trail per outermost search**, shared down through every
fork inside it, with a mark taken per choice point (WAM-style) — not
one trail per fork.

This is load-bearing. Store refs are per-fork and vanish with the
fork, but *variable cells are shared across forks*. An inner `solve`
that commits inside an outer search branch must leave its trail
entries visible to the outer driver; with independent trails the outer
branch's unwind would miss the inner-committed bindings, and the next
alternative would run against contaminated state.

The rules:

- **Fork inheritance.** A search fork installs a fresh trail only when
  there is no trail already; otherwise it shares the enclosing one.
  A plain `run_chr_session/1` fork inherits the field as it is — so a
  sub-session's writes to shared variables, made inside a search
  branch, are undone when that branch is undone. At the top level
  there is no trail and nothing is recorded.
- **Marks delimit undo, not forks.** The driver takes a *base mark* on
  entry and a mark per alternative. A failed branch unwinds to that
  alternative's mark. Exhaustion, and any ending that does not commit,
  unwind to the base mark. An escaping runtime error unwinds to the
  base mark.
- **Commit means "do not unwind".** The entries stay on the shared
  trail, so an enclosing driver can still undo them.


## Entry points

### `solve/1`

`Ok is solve(quote(Goal))`

Runs `Goal` and stops at the **first solution**, returning `true`.
That solution is **committed**: nothing is unwound, so bindings made
to variables shared with the goal are visible to the caller. If the
whole search space is exhausted without a solution, everything is
unwound to the base mark and `solve` returns `false`.

"Committed" is relative to the enclosing computation, not absolute: if
`solve` is itself running inside a search branch, its trail entries
remain on the shared trail and are undone if *that* branch is later
abandoned.

### `find_all/2`

`Solutions is find_all(Template, quote(Goal))`

Explores the **whole** search space and returns the list of solutions,
in search order. At each solution `Template` is copied with
`copy_term/1` semantics — a fresh, structure-sharing-free snapshot
with distinct fresh variables for each unbound variable it still
contains — and appended to the result.

When the search finishes, **everything is unwound to the base mark**.
The list of copies is the only thing that survives; no binding made
during the search is visible afterwards. An empty search space gives
`[]`, which is `find_all`'s way of saying "no solutions" — it never
fails and never returns `false`.

`find_all` explores the whole space, so it does not terminate on an
infinite one. Use `find_n/3`.

`Template` is an ordinary expression argument, evaluated once before
the search starts, so it is normally just a variable (or a term over
variables) that the goal binds. It is an *evaluated* position, so
every variable in it must already be in scope — in a rule body, that
means the rule's head has to bind it (`YCHR-40002`):

```prolog
% Rejected: X and Y appear in an evaluated position without being bound.
all_pairs(Ss) <=> Ss is find_all([X, Y], quote(pair(X, Y, 5))).

% Accepted: the head binds them. They are left unbound afterwards,
% since find_all unwinds everything.
all_pairs(X, Y, Ss) <=> Ss is find_all([X, Y], quote(pair(X, Y, 5))).
```

This is unlike Prolog's `findall/3`, where the goal's variables are
local to the call.


## Iterating over solutions

`solve` and `find_all` are the two extremes: stop at the first
solution, or collect them all. `fold_solutions/4` is the general form
— a fold over the solution sequence, in search order, with early exit
and with the driver in control of the iteration.

```prolog
Acc is fold_solutions(Template, quote(Goal), F, Acc0)
```

At each solution, in search order, the driver evaluates

```prolog
'$call'(F, copy_term(Template), Acc)
```

with the solution's bindings still live and nothing yet undone. `F`
returns a `step`:

| Result | Effect |
|---|---|
| `continue(A)` | The accumulator becomes `A`. Backtrack and look for the next solution. |
| `stop(A)` | Stop now. Unwind everything to the base mark. `fold_solutions` returns `A`. |
| `commit(A)` | Stop now. Unwind **nothing**: this solution's bindings survive, as they do for `solve`. `fold_solutions` returns `A`. |

Exhausting the search space unwinds everything to the base mark and
returns the accumulator as it stands.

`stop` and `commit` differ only in what happens to the bindings, and
`stop` is the one you want unless you specifically need the witness.
Making the shorter name the undoing one is deliberate: committing
inside a fold is the surprising outcome, so it is the one you have to
name.

Three properties keep the fold sound across backtracking:

- **`F` is an expression function.** It cannot tell constraints and
  cannot bind logical variables, so the accumulator it returns cannot
  hold a binding that a later backtrack would undo underneath it.
- **The witness is a copy.** `copy_term` gives the accumulator a
  snapshot with fresh variables, structurally independent of the
  branch it came from.
- **The accumulator is host state.** It lives in the driver, not in
  the store or on the trail, so backtracking does not touch it.

Two error cases: `fail/0` inside `F` fails the current branch, which
behaves exactly like `continue` with the accumulator unchanged, and a
return value that is not a `step` is a runtime error. Runtime errors
raised by `F` propagate out of the search, after unwinding to the base
mark, like any other error in a branch.

`solve` and `find_all` are expressible over `fold_solutions` —
`commit(true)` at the first solution, and `continue` accumulating
copies to exhaustion — and are kept as host calls only because they
are already there and pay no `'$call'` per solution.

### `forall/3`

```prolog
Ok is forall(Template, quote(Goal), P)
```

`true` when `'$call'(P, Copy)` holds at every solution. Stops at the
first counterexample and returns `false`. Everything is unwound
either way; a search that finds no solutions at all is vacuously
`true`.

### `find_n/3`

```prolog
Xs is find_n(N, Template, quote(Goal))
```

The first `N` solutions, as copies of `Template` in search order —
`find_all` with a bound. Fewer than `N` if the space is smaller;
`[]` when `N` is zero or negative, without running the goal at all.

`find_n` stops with `stop`, so **everything is unwound**: like
`find_all`, the copies are all that survives. That is what makes it
usable on an infinite generator, where `find_all` would not terminate.


## Nesting

Search nests. A search entry point may appear in a rule body, in a
function, in a guard-called function, and inside a goal that is itself
under search. Each nested call forks again and takes its own marks on
the one shared trail:

- an inner **commit** leaves its entries on the trail for the enclosing
  driver, which may still undo them;
- an inner **failure** unwinds only to the inner driver's own marks,
  leaving the outer branch's state alone;
- an inner **error** unwinds to the inner base mark and then keeps
  propagating outward, unwinding each enclosing driver to *its* base
  mark in turn.

`alt/1` constraints belong to the store of the session that told them,
so an inner search never sees an outer search's pending choices.


## Edge cases

| Situation | Behaviour |
|---|---|
| `alt([])`, `choose(X, [])` | The branch fails: zero alternatives is immediate exhaustion. |
| `alt(G)` where `G` is not a proper list (an atom, an integer, a partial list ending in an unbound variable) | Runtime error at the choice point. Not a failure. |
| An alternative that is not a goal (an integer, an unbound variable) | Runtime error at the choice point, when that alternative is reached. Earlier alternatives may already have produced solutions. |
| An alternative naming a constraint that does not exist | Runtime error at the choice point. Not a failure. |
| `choose(X, Alts)` where `X` is already bound | `try_unify` makes it a membership test: alternatives that do not unify with `X`'s value fail individually, and the branch continues with the next one. |
| `choose(X, Alts)` where `X` is bound by propagation *after* the `choose` was told | Same as above — `X` is dereferenced when the alternative is tried, not when the `choose` was told. |
| `choose(X, Alts)` where `Alts` is not a proper list | Runtime error at *tell* time, inside `maplist`, before anything is stored. |
| Several `alt` constraints alive at quiescence | The oldest is taken; the others stay stored and are reached at a later quiescence, in insertion order. |
| An `alt` killed by a user rule | Never seen by the driver. |
| An `alt` told inside a branch — including the inner `alt` of a nested `;` | Picked up at that branch's next quiescence, so it is nested *under* the current choice. |
| The goal quiesces with no `alt` at all | One solution, immediately. |
| An empty goal list | Quiesces immediately with no `alt`: one solution. |
| Non-terminating propagation inside a branch | Does not terminate. Search adds no fairness or depth limit. |
| `;` in a module that does not import `library(search)` | Compile-time error, `YCHR-20021`. |
| `;` in a guard, an `is` right-hand side, or a function body | Compile-time error, `YCHR-20022`. |
| `;` at the top level of a query | Compile-time error, `YCHR-30006`. Wrap it: `solve(quote((A ; B)))`. |


## Tracing

The REPL's `:trace` covers search. Six events are emitted: entering
and leaving a search, selecting a choice point, trying an alternative,
reaching a solution, and backtracking.

Abridged from `:trace bound_pick(X, Ss).` over
`test/golden/search_basic`, where `X` is bound to 2 before a
`choose(X, [1, 2, 3])`, so labeling is a membership test. The elisions
are `choose`'s `maplist` building its three goals, and the ordinary
activation of each `try_unify`.

```
      call search:find_all(2, pick3(2))
        search find_all
        tell search_basic:pick3(2)
          activate c#1: search_basic:pick3(2)
            try occurrence search_basic:pick3 #1 (rule __rule_10)
              kill c#1
              tell search:choose(2, [1, 2, 3])
                activate c#2: search:choose(2, [1, 2, 3])
                  try occurrence search:choose #1 (rule __rule_0)
                    kill c#2
                    ...
                    tell search:alt([try_unify(2, 1), try_unify(2, 2), try_unify(2, 3)])
                      activate c#3: search:alt([...])
                        store c#3: search:alt([...])
        choice c#3: [try_unify(2, 1), try_unify(2, 2), try_unify(2, 3)]
        try alt 1/3: try_unify(2, 1)
        tell search:try_unify(2, 1)
          ...
              call search:fail
        backtrack (fail)
        try alt 2/3: try_unify(2, 2)
        tell search:try_unify(2, 2)
          ...
              unify 2 = 2
        solution
        backtrack (more solutions wanted)
        try alt 3/3: try_unify(2, 3)
        tell search:try_unify(2, 3)
          ...
              call search:fail
        backtrack (fail)
        end search find_all (exhausted)
        host call find_all(2, pick3(2)) = [2]
```

The `choose` layer is what a trace of the derived form costs: a rule
firing, a `maplist` over the values, and a `try_unify` tell per
alternative. A hand-written `alt` shows only the last three levels.

`backtrack` is emitted **after** the undo, so by the time it appears
the bindings, store, history and reactivation queue are back to what
they were at the choice point. Its reason distinguishes the two ways a
branch can fail from the one way it can succeed and still be
backtracked out of:

| Reason | Meaning |
|---|---|
| `fail` | `fail/0` was called. |
| `alternatives exhausted` | Every alternative of the choice point has been tried. |
| `more solutions wanted` | A solution was reached and the caller asked to keep going. This is `find_all`'s normal mode, and is *not* a failure. |

`end search` reports `(committed)`, `(stopped)` or `(exhausted)`.


## Worked example

Labeling is the smallest example that exercises every part of the
model — propagate, choose, prune, backtrack — so it is the one used
here; it is not what search exists for.

```prolog
:- module(search_example, [pair/3]).
:- use_module(library(search)).

:- chr_constraint pair(any, any, any), sum_is(any, any, any).

% Post both choices and the check in one go.
pair(X, Y, S) <=> choose(X, [1, 2, 3]), choose(Y, [1, 2, 3]), sum_is(X, Y, S).

% The guard demands both values, so while X or Y is unbound it delays
% (soft-guard failure) and `sum_is` stays stored. Labeling binds them;
% reactivation retries the guard; a wrong sum fails the branch.
sum_is(X, Y, S) <=> not(X + Y == S) | fail.
```

`Ok is solve(quote(pair(X, Y, 5)))` binds `X = 2`, `Y = 3` — the first
pair in search order that survives the check — and
`Ss is find_all([X, Y], quote(pair(X, Y, 5)))` yields
`Ss = [[2, 3], [3, 2]]` with `X` and `Y` left unbound.

The same program written with `;` chooses between goals rather than
values, which is what you want when the branches do different work:

```prolog
% A tiny generator. `nat(N)` binds N to 0, 1, 2, ... in order.
:- chr_constraint nat(any), succ_of(any, any).

nat(N) <=> (try_unify(N, 0) ; nat(M), succ_of(M, N)).
succ_of(M, N) <=> integer(M) | N is M + 1.
```

The guard on `succ_of` is not decoration. The second branch tells
`nat(M)` and `succ_of(M, N)` together, and the inner choice that binds
`M` is not made until the next quiescence — so without a guard,
`M + 1` would be reached with `M` unbound and abort. Delaying on an
unbound argument is the ordinary way to write a rule that has to wait
for a choice.

`Ns is find_n(5, N, quote(nat(N)))` yields `Ns = [0, 1, 2, 3, 4]`.
`find_all` on the same goal would not terminate.

Complete, runnable programs live in `test/golden/search_*/`.


## Non-goals

- **No pervasive backtracking.** Nothing outside a search entry point
  is undoable.
- **No continuation capture.** The `Chr` monad is untouched; there is
  no `logict`-style non-determinism monad, and CHR code cannot suspend
  and resume a computation.
- **No cursor over solutions.** Iteration is *internal* — the driver
  runs the loop and calls back into the program. There is no handle a
  caller can hold and pull from, because the state a solution depends
  on lives on a shared trail that the caller could unwind out from
  under it. An external iterator would need the driver rewritten
  around an explicit stack; that is worth doing for a REPL that
  offers Prolog's `;` prompt, and it is not in scope here.
- **No search strategies.** Depth-first, left-to-right, in list order.
  No breadth-first, no iterative deepening, no branch-and-bound, no
  labeling heuristics. A heuristic is expressible in the program: build
  the alternatives list in the order you want, and choose *when* to
  tell the choice point.
- **No constraint-directed backjumping.** A failure discards the whole
  branch; there is no analysis of which choice caused it.
- **No finite-domain solver.** `library(search)` provides the choice
  and undo mechanism only. An FD library is one thing that could be
  built on top of it, separately.
