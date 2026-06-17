# Known Bugs

This document tracks known correctness bugs in the YCHR implementation
that have not yet been fixed. Entries are concrete (file:line, code
snippet, repro) so they can be picked up as standalone tasks.

Remove entries from this file when the underlying bug is fixed.

## Bare expression goals: `42` and `"hello"` produce `YCHR-15003`, not the documented `YCHR-20013`

**Documented claim.** `docs/reference/errors.md` §`YCHR-20013`:
"`ychr run -g GOAL` was given a goal that is not a single declared
constraint — a bare expression (`true`, `1 + 1`), an `is`/`=` form,
a conjunction (`a, b`), a function call (`factorial(5)`), or an
unknown name."

**Test.**

    ychr run -g '42'      empty_module.chr   →  YCHR-15003
    ychr run -g '"hello"' empty_module.chr   →  YCHR-15003
    ychr run -g '1 + 1'   empty_module.chr   →  YCHR-20013  (matches doc)
    ychr run -g 'true'    empty_module.chr   →  YCHR-20013  (matches doc)
    ychr run -g 'a, b'    empty_module.chr   →  YCHR-20013  (matches doc)

**Expected.** `YCHR-20013` for all "not a declared constraint" goals,
as the doc says.

**Actual.** `YCHR-15003` (`MalformedConstraint` — "expected an atom or
compound term") fires for goals that are bare literals (numbers,
strings). Other expression forms get `YCHR-20013` as documented.

**Notes.** Either errors.md should note that literal-shaped goals
route through `YCHR-15003`, or the `run -g` validator should fold
literals into the same `YCHR-20013` path as the other bare
expressions.

## `'$call'(5, 1)` reports "no matching equation" instead of a type-of-target diagnostic

**Documented claim.** `docs/reference/errors.md` defines `YCHR-60001`
as covering "runtime errors raised by the Haskell interpreter (e.g.
arithmetic on non-numbers, calling a non-function)."

**Test.**

    ychr> R is '$call'(5, 1).

**Expected.** A `YCHR-60001` whose message names the actual problem:
"calling a non-function" or similar.

**Actual.**

    YCHR-60001: CHR runtime error: no matching equation

The message technically explains the dispatch failure (no
`'$call'(int, int)` equation), but it leaks an implementation detail
("equation") and tells the user nothing useful: they did not write any
equations, they wrote `'$call'(5, 1)`. The typed `call(5, 1)` path
catches this at the type checker with a much better message:
`Type mismatch: 'int' does not match 'fun(_) -> _'`.

**Notes.** The doc explicitly carves out "calling a non-function" as a
`YCHR-60001` case, but the message for the `'$call'` form is
unintelligible compared to the `call` wrapper.

## `term(pair(1,2))` example in type-system.md is wrong on both the typecheck and the runtime half

**Documented claim.** `docs/reference/type-system.md:332-338`: "the
inferred LHS type can still be unreachable at runtime — `R is term(pair(1,
2))` type-checks with `R : pair(int, int)` because `term(...)` is a
quoting form, but the runtime evaluator sees `pair/2` as a non-evaluable
functor and raises `YCHR-60001`."

**Test.** Probe both halves separately, with `pair` a real constructor.

    % Typecheck half — tie R to a string via a propagating type var.
    :- chr_type pair(A, B) ---> pair(A, B).
    :- chr_constraint go(C).
    go(R) <=> R is term(pair(1, 2)), R = "hello".

    % Runtime half.
    :- chr_constraint go(any).
    go(R) <=> R is term(pair(1, 2)).
    Goal: go(R)

**Expected (per the doc).** Typecheck: `R : pair(int, int)`, so
`R = "hello"` clashes (`pair ~ string`). Runtime: `YCHR-60001`.

**Actual.** Typecheck is clean (`term(pair(1,2))` types `R` as `any`,
not `pair(int,int)`, so no clash). The run yields `R = m:pair(1, 2)`
with no error.

**Notes.** The implementation is self-consistent and matches `PROJECT.md`
("`term(...)` keeps the inner tree opaque"). It is the *bare* form that
infers the constructor type — `R is pair(1, 2), R = "hello"` → `YCHR-60001
'm:pair(_, _)' vs 'string'`; the bare form still does *not* error at
runtime (`R is pair(1, 2)` → `R = m:pair(1, 2)`), because data
constructors are evaluable (they build terms). The genuine non-evaluable
`YCHR-60001` runtime case is a *function* with no matching equation, which
`term(...)` correctly suppresses (`R is f(5)` errors; `R is term(f(5))` →
`R = f(5)`). The note should illustrate its point with a bounded/undefined
function call *without* `term(...)`, not `term(pair(1, 2))`. This is a
documentation bug, not an implementation bug.

## Function-type syntax in type-system.md omits the mandatory `end`; the worked declaration at line 636 does not parse

**Documented claim.** `docs/reference/type-system.md:36` (the `τ`
grammar) gives `fun(τ₁, ..., τₙ) -> τᵣ`, and line 636 a concrete
declaration: `:- function call(fun(A) -> B, A) -> B.`. Every function
type in the spec (lines 144, 145, 580, 603, 636, 1389) omits `end`.

**Test.** Compile the line-636 declaration verbatim.

    :- function myid(A) -> A.   myid(X) -> X.
    :- function callit(fun(A) -> B, A) -> B.
    callit(F, X) -> '$call'(F, X).

**Expected.** Parses and type-checks (verbatim spec example).

**Actual.**

    YCHR-50001
    unexpected "-"
    expecting space, "%", "," or ")"

Adding `end` inside the function type fixes it:
`:- function callit(fun(A) -> B end, A) -> B.` compiles.

**Notes.** The parser requires `end` even in *type-expression* position.
`libraries/prelude.chr:99` and `docs/reference/prelude.md:156` both
correctly write `call(fun(A) -> B end, A) -> B`, and golden tests use
`fun(int) -> maybe(int) end` inside signatures. So `type-system.md` (the
formal `τ` grammar at line 36 and the declaration at line 636) is the
out-of-sync document. Fix the grammar to show the `end` terminator, or
accept the un-terminated form in type position.

## Function-type arity is ignored in consistency checking (refs and lambdas)

**Documented claim.** `docs/reference/type-system.md:203-219`, rule
`[C-Fun]`: `fun(τ₁,...,τₙ) -> τᵣ ~ fun(σ₁,...,σₙ) -> σᵣ` requires the same
number of parameters; line 219 lists `int ~ fun(int) -> int` as an error.

**Test.** Unify function values against a function type of a different
arity.

    :- function dbl(int) -> int.   dbl(X) -> X.
    :- chr_constraint c(fun(int, int) -> int end).
    c(F) <=> F = fun dbl/1.                       % ref, 1 vs 2

    :- chr_constraint c(fun(int) -> int end).
    c(F) <=> F = fun(X, Y) -> X end.              % lambda, 2 vs 1

**Expected.** Type error (`fun(int)->int` inconsistent with
`fun(int,int)->int`).

**Actual.** Both compile clean. An arg-/return-*type* mismatch at equal
arity *is* caught (`F : fun(string)->string end = fun dbl/1` →
`YCHR-60001`), so consistency checks the field types of a function type
but not its arity.

**Notes.** Direct counterexample to `[C-Fun]`/`[Inconsistency]` as
written; lower severity since it is a missing check rather than a wrong
result.
