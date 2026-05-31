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
