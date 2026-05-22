# Known Bugs

This document tracks known correctness bugs in the YCHR implementation
that have not yet been fixed. Entries are concrete (file:line, code
snippet, repro) so they can be picked up as standalone tasks.

Remove entries from this file when the underlying bug is fixed.

## `docs/reference/prelude.md` lists `rem/2` as `_/2` but the implementation rejects floats

`docs/reference/prelude.md` §Arithmetic shows `rem` with signature
`_/2` ("Remainder; signatures default to `any`."). The row above
(`mod`) is `(int, int) -> int`. `libraries/prelude.chr:87` declares
`rem` identically to `mod`. Pure doc drift.

Repro:

```chr
:- module(z).
:- chr_constraint r/1.
r(R) <=> R is 7.5 rem 3.0.
```

Actual: `YCHR-60001 Type mismatch: 'typechecker:float' does not match
'typechecker:int'`. Expected: change the `rem` row in `prelude.md` to
`(int, int) -> int`, matching `mod`.

## Integer division by zero produces a raw Haskell error with no `YCHR-NNNNN` code

`docs/reference/errors.md`: "YCHR diagnostics carry a numeric code of
the form `YCHR-NNNNN`." `PROJECT.md` documents `YCHR-60001` as the
runtime-error code for arithmetic failures. Integer `div`/`mod` by
zero bypasses the YCHR diagnostic infrastructure entirely.

Repro:

```chr
:- module(z).
:- chr_constraint r/1.
r(R) <=> R is 10 div 0.
```

Actual: `Error: divide by zero` — no code, no rule context, no source
location, none of the `=== runtime error ===` framing. Expected: a
formatted `YCHR-NNNNN` diagnostic. Same category as the `ychr run
-g 'true'` failure above — a class of runtime errors that bypasses
YCHR diagnostics.

Cross-check: `1.0 / 0.0` returns `Infinity.0` without error.

## Integer arithmetic silently overflows at the 64-bit boundary (spec ambiguous)

`docs/reference/type-system.md` describes `int` as "integer values"
without specifying width. The prelude declares `+` as
`(int, int) -> int` with no overflow caveat. The doc's Prolog-flavored
framing implies arbitrary precision; the implementation uses the
host's fixed-width `Int` and wraps silently.

Repro:

```chr
:- module(z).
:- chr_constraint r/1.
r(R) <=> R is 9223372036854775807 + 1.
```

Actual: `R = (-9223372036854775808)`. Expected: either bignum
semantics, or commit to fixed-width in `type-system.md`/`prelude.md`
and (ideally) trap overflow at runtime.

## `host:foo(...)` is accepted as a rule-head pattern (spec silent)

`docs/reference/language.md` §"Host calls" describes `host:` as a
wired-in qualifier intercepted by the resolver. The doc does not say
what `host:foo(...)` means in a non-evaluating position like a head
pattern. The implementation intercepts `host:` only at value-evaluation
sites; in head patterns and inside `term(...)` it is treated as a plain
structural qualified atom.

Repro:

```chr
:- module(z).
:- chr_constraint c/1, r/1, go/1.
c(host:foo(X)), r(R) <=> R = X.
go(R) <=> c(term(host:foo(42))), r(R).
```

Actual: goal `z:go(R)` yields `R = 42`. Behavior is consistent with
"heads don't evaluate" and `term(...)` opacity, but unspecified.
Expected: a sentence in §"Host calls" clarifying that `host:` is a
value-evaluation concern only.
