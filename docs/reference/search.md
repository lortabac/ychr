# YCHR Search Specification (`library(search)`)

> **Audience:** readers writing a labeling or generate-and-test program
> in YCHR, and anyone working on the search driver itself.
> **You will:** find the choice-at-quiescence execution model, the
> commit and undo rules, how failure differs from error, and the exact
> edge-case behaviour of every primitive.
> **Skip if:** you only need deterministic CHR — nothing here applies
> to a program that never imports `library(search)`.

This document specifies *search*: an opt-in, explicitly driven
exploration of alternative bindings, provided by the standard library
module `search` and implemented in the Haskell runtime. Search is
**not** pervasive backtracking. A program that does not call
`solve/1` or `find_all/2` executes exactly as it does today, under the
refined operational semantics (ωr), with no VM changes and no
per-step bookkeeping.

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
| `choose/2` | CHR constraint, **no rules** | Marks a pending choice. Sits inert in the store. |
| `fail/0` | function | Fails the current branch. |
| `try_unify/2` | CHR constraint | Prolog's `=`: unify, or fail the branch. |
| `solve/1` | function | Runs a goal; commits to its first solution. |
| `find_all/2` | function | Runs a goal; collects a copy of a template per solution, then undoes everything. |

The execution model is *choice at quiescence* (labeling), not
continuation capture:

1. `solve` / `find_all` fork a sub-session and tell the goal, running
   it to quiescence under the ordinary ωr semantics.
2. At quiescence the driver looks in the store for an alive
   `search:choose/2` constraint. If there is none, the current state
   is a **solution**.
3. Otherwise it takes the *oldest* such constraint, `choose(X, Alts)`,
   and tries each element of `Alts` in list order: kill the `choose`,
   unify `X` with the alternative, run reactivation to quiescence, and
   recurse from step 2.
4. If a branch fails, everything the branch did is undone and the next
   alternative is tried. When the alternatives run out, the failure
   propagates to the enclosing choice point (or out of the driver).

There is no continuation to capture because the continuation after a
choice is always "run reactivation to quiescence", which the driver
invokes itself. This is how labeling works in CHR generally: propagate
to fixpoint, label, repeat.


## The `search` module

```prolog
:- use_module(library(search)).
```

exports

```prolog
:- chr_constraint choose(any, list(any)), try_unify(any, any).

:- function
    (fail() -> any),
    (solve(any) -> bool),
    (find_all(any, any) -> list(any)).
```

`choose/2` has **no rules**. Telling it simply stores it. The runtime
recognizes it by its qualified name `search:choose` at arity 2 — one
wired-in name, like `'$call'`. This is *provisional*: a general
mechanism for a library to nominate a constraint to the runtime would
replace it without changing the surface language.

`try_unify/2` is ordinary CHR, defined in the library itself (see
[Failing unification](#failing-unification)).


## Scope: search runs in a sub-session

`solve(quote(Goal))` and `find_all(Template, quote(Goal))` run `Goal`
in a **fresh session of the current program** — its own constraint
store, propagation history, reactivation queue, and call stack, with
the same rules, functions, host calls, and exports. This is exactly
`run_chr_session/1`'s fork, and it inherits that model verbatim:

- **The caller's store is not searched.** Constraints already stored
  in the calling session are invisible to the goal, and constraints
  the goal stores are invisible to the caller. Search explores the
  goal, not the ambient program state.
- **Goal shape.** `Goal` is a single constraint term, or a list of
  them told in order, wrapped in `quote/1` to keep it symbolic.
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
`search:choose/2` that are still alive, and takes the **oldest** —
first by store insertion order. Alternatives are tried in **list
order**, left to right. Search is therefore depth-first and fully
deterministic: for a given program and goal, the sequence of solutions
is fixed.

Nothing prevents a rule from removing or rewriting a `choose`
constraint before the driver sees it — `choose` is an ordinary
constraint, and a rule with `choose(X, [A]) <=> X = A` is a legitimate
(if pointless) way to make a unary choice deterministic. The driver
only ever considers what is alive and stored at quiescence.

### Firing a choice

For alternative `A` of `choose(X, Alts)` the driver, in order:

1. takes a trail mark and snapshots the store refs (see
   [Undo](#commit-and-undo));
2. kills the `choose` constraint (it is not retried inside the branch);
3. unifies `X` with `A`;
4. enqueues the observers that unification collected and drains the
   reactivation queue — the same work the VM's
   `DrainReactivationQueue` does after a tell-side `BUnify`;
5. recurses into step 2 of the overview.

If step 3 fails, this alternative fails and the driver moves to the
next one (see [Edge cases](#edge-cases)). A unification that fails
part-way through a compound leaves the bindings it already made; those
are on the trail like any others and are undone by the same unwind.

This is the one place where a failing unification is a failure rather
than an error. It is the driver's own choice mechanism, not a
user-written `=`: erroring here would make `choose/2` unusable on a
variable that propagation has already narrowed, which is the normal
case rather than a bug.

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

Exactly three things:

1. An explicit `fail/0` — including via `try_unify/2`, which is
   defined in terms of it.
2. The driver's own `X = A` unification failing at a choice point (see
   [Edge cases](#edge-cases)).
3. Exhaustion: a `choose` whose alternatives are all exhausted, which
   includes `choose(X, [])`.

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
  alternative's mark. `solve` exhaustion and `find_all` completion
  unwind to the base mark. An escaping runtime error unwinds to the
  base mark.
- **Commit means "do not unwind".** The entries stay on the shared
  trail, so an enclosing driver can still undo them.

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

`Template` is an ordinary expression argument, evaluated once before
the search starts, so it is normally just a variable (or a term over
variables) that the goal binds.

Unlike Prolog's `findall/3`, the goal's variables are **not local to
the call**. A rule body may only mention variables its head binds
(`YCHR-40002`), so a template variable has to be threaded through the
enclosing head:

```prolog
% Rejected: X and Y appear only in the body.
all_pairs(Ss) <=> Ss is find_all([X, Y], quote(pair(X, Y, 5))).

% Accepted: the head binds them. They are left unbound afterwards,
% since find_all unwinds everything.
all_pairs(X, Y, Ss) <=> Ss is find_all([X, Y], quote(pair(X, Y, 5))).
```


## Nesting

Search nests. `solve` and `find_all` may appear in a rule body, in a
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

`choose/2` constraints belong to the store of the session that told
them, so an inner search never sees an outer search's pending choices.


## Edge cases

| Situation | Behaviour |
|---|---|
| `choose(X, [])` | The branch fails: zero alternatives is immediate exhaustion. |
| `choose(X, Alts)` where `Alts` is not a list (an atom, an integer, a partial list ending in an unbound variable) | Runtime error at the choice point. Not a failure. |
| `choose(X, Alts)` where `X` is already bound | The driver's `X = A` is a membership check: alternatives that do not unify with `X`'s value fail individually, and the branch continues with the next one. This is not an error, despite body-position unification failure being one. |
| `choose(X, Alts)` where `X` is bound by propagation *after* the `choose` was told | Same as above — `X` is dereferenced at the choice point, not when the `choose` was told. |
| Several `choose` constraints alive at quiescence | The oldest is taken; the others stay stored and are reached at a later quiescence, in insertion order. |
| A `choose` killed by a user rule | Never seen by the driver. |
| A `choose` told inside a branch | Picked up at that branch's next quiescence, so it is nested *under* the current choice. |
| The goal quiesces with no `choose` at all | One solution, immediately. `solve` returns `true`; `find_all` returns a one-element list. |
| An empty goal list | Quiesces immediately with no `choose`: one solution. |
| Non-terminating propagation inside a branch | Does not terminate. Search adds no fairness or depth limit. |


## Tracing

The REPL's `:trace` covers search. Six events are emitted: entering and
leaving a search, selecting a choice point, trying an alternative,
reaching a solution, and backtracking.

```
      call search:find_all(2, pick3(2))
        search find_all
        tell search_basic:pick3(2)
          activate c#1: search_basic:pick3(2)
            try occurrence search_basic:pick3 #1 (rule __rule_9)
              kill c#1
              tell search:choose(2, [1, 2, 3])
                activate c#2: search:choose(2, [1, 2, 3])
                  store c#2: search:choose(2, [1, 2, 3])
        choice c#2: 2 in [1, 2, 3]
        try alt 1/3 = 1
        backtrack (no match)
        try alt 2/3 = 2
        solution
        backtrack (more solutions wanted)
        try alt 3/3 = 3
        backtrack (no match)
        end search find_all (exhausted)
        host call find_all(2, pick3(2)) = [2]
```

`backtrack` is emitted **after** the undo, so by the time it appears
the bindings, store, history and reactivation queue are back to what
they were at the choice point. Its reason distinguishes the three ways
a branch can fail from the one way it can succeed and still be
backtracked out of:

| Reason | Meaning |
|---|---|
| `fail` | `fail/0` was called. |
| `no match` | The driver's `X = Alt` did not unify — the membership case. |
| `alternatives exhausted` | Every alternative of the choice point has been tried. |
| `more solutions wanted` | A solution was reached and the caller asked to keep going. This is `find_all`'s normal mode, and is *not* a failure. |

`end search` reports `(committed)` or `(exhausted)`, which is exactly
`solve`'s `true` / `false`.


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

The pattern generalizes: rules propagate and prune, `choose` marks
what is left to decide, and the driver alternates between the two.

Complete, runnable programs live in `test/golden/search_*/`.


## Non-goals

- **No pervasive backtracking.** Nothing outside a `solve` / `find_all`
  call is undoable.
- **No continuation capture.** The `Chr` monad is untouched; there is
  no `logict`-style non-determinism monad, and CHR code cannot suspend
  and resume a computation.
- **No search strategies.** Depth-first, left-to-right, in list order.
  No breadth-first, no iterative deepening, no branch-and-bound, no
  labeling heuristics. A heuristic is expressible in the program: build
  the alternatives list in the order you want, and choose *when* to
  tell `choose`.
- **No constraint-directed backjumping.** A failure discards the whole
  branch; there is no analysis of which choice caused it.
- **No solution limit on `find_all`.** Use `solve` for one solution.
- **No finite-domain solver.** `library(search)` provides the choice
  and undo mechanism only. An FD library is one thing that could be
  built on top of it, separately.
