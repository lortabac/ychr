# Known Bugs

This document tracks known correctness bugs in the YCHR implementation
that have not yet been fixed. Entries are concrete (file:line, code
snippet, repro) so they can be picked up as standalone tasks.

Remove entries from this file when the underlying bug is fixed.

## `prelude.md` says arithmetic operators are `:- class`, but `/`, `div`, `mod`, `rem` are single-signature `:- function`

**Documented claim.** `docs/reference/prelude.md` §"How the prelude is
structured": "Operator overloading by signature. Arithmetic and
comparison operators are declared as `:- class` with one signature per
concrete combination of types." The Arithmetic table lists `/`, `div`,
`mod`, `rem`.

**Test.** Source inspection of `libraries/prelude.chr` plus a type
mismatch on `/`:

    :- chr_constraint t/1.
    t(R) <=> R is 5 / 2.

    ychr check

**Expected.** Per the prose, `/` is a class, so a non-matching call
should report `YCHR-60006` (`NoMatchingOverload`), as the genuinely
multi-signature `+` does for `"a" + "b"`.

**Actual.** `libraries/prelude.chr:78` declares
`:- function ('/'(float, float) -> float), ...` — a `:- function`, not a
`:- class`. The mismatch therefore reports the function-style
`YCHR-60001` ("Type mismatch: 'int' does not match 'float'"), whereas
the multi-sig `+` gives the class-style `YCHR-60006` ("No matching type
declaration for 'prelude:+'").

**Notes.** The behavior is internally correct (single-sig → function →
`YCHR-60001`); only `prelude.md`'s blanket "declared as `:- class`" is
inaccurate for the single-signature arithmetic operators. The signature
*table* is accurate. This is a documentation fix, not a code fix.

## REPL one-shot query warnings show an empty `''` source snippet

**Documented claim.** Implicit consistency: file-based diagnostics echo
the offending source line (e.g. `R = mystery(1)`).

**Test.**

    ychr> B is atom(foo).      % foo is an undeclared data constructor

**Expected.** The warning's source-context line shows the query text
(`B is atom(foo)` or similar), as it does for file inputs.

**Actual.**

    <generated>:1:1: YCHR-20101
    Undeclared data constructor 'foo'
      Hint: declare it with :- chr_type, or check the spelling
    ''

The italic source-context line is empty quotes (`''`) rather than the
typed query. (The query itself still succeeds: `B = true`.)

## Constructor arity mismatch double-reports `YCHR-20102` (warning) and `YCHR-60008` (error)

**Documented claim.** `docs/reference/errors.md` lists `YCHR-20102`
(`DataConstructorArityMismatch`, *warning*, rename phase) and
`YCHR-60008` (`ConstructorArityMismatch`, *error*, type-check phase) as
separate codes.

**Test.**

    :- chr_type pr ---> p(int, int).
    :- chr_constraint go/1.
    go(R) <=> R = p(1).

    ychr check

**Expected.** Unclear from the spec whether both should fire for one
mistake.

**Actual.** Both fire for the single `p(1)`:

    ctor_arity.chr:3:11: YCHR-20102  (warning)
    Data constructor 'p' used with 1 argument(s) but declared with a different arity
    ctor_arity.chr:3:11: YCHR-60008  (error)
    Data constructor '<ctor_arity>:p' is used with 1 argument(s) but declared with 2

**Notes.** Possibly by design: the codebase deliberately co-fires
diagnostics elsewhere (the type-system spec calls out `YCHR-16013` +
`YCHR-16007` co-firing as intentional). Flagged because the two messages
restate the same defect at differing severities, and the warning's
"a different arity" is vaguer than the error's exact "declared with 2".
