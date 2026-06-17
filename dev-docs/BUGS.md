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
