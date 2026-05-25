# Known Bugs

This document tracks known correctness bugs in the YCHR implementation
that have not yet been fixed. Entries are concrete (file:line, code
snippet, repro) so they can be picked up as standalone tasks.

Remove entries from this file when the underlying bug is fixed.

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
