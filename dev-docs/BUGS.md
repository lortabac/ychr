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

## `YCHR-20009` claims a module "does not export" a name it *does* export when the module simply isn't imported

**Documented claim.** `docs/reference/errors.md` §`YCHR-20009`
(`NotExportedByModule`): "A qualified reference targets a module that
does not export the named item. Check the spelling and the exporter's
export list."

**Test.** Three files compiled together. `moda` exports `aa/1`; `modc`
imports only `modb` and writes the qualified reference `moda:aa`.

    % moda.chr
    :- module(moda, [aa/1]).
    :- chr_constraint aa/1, marker/0.
    aa(X) <=> marker.

    % modb.chr
    :- module(modb, [bb/1]).
    :- use_module(moda).
    :- chr_constraint bb/1.
    bb(X) <=> aa(X).

    % modc.chr
    :- module(modc).
    :- use_module(modb).
    :- chr_constraint cc/1.
    cc(X) <=> moda:aa(X).

    ychr run -g 'cc(1)' moda.chr modb.chr modc.chr

**Expected.** A diagnostic whose message reflects the real cause — that
`modc` does not *import* `moda`. (`moda` plainly exports `aa/1`.)

**Actual.**

    modc.chr:4:11: YCHR-20009
    Module 'moda' does not export 'aa/1'
      Hint: ensure 'moda' is imported and exports 'aa/1'

The message asserts something false: `moda`'s export list literally
contains `aa/1`. The same wording also appears when the qualified module
does not exist in the program at all (`zzz:aa` → `Module 'zzz' does not
export 'aa/1'`).

**Notes.** Controlled variants pin the cause to the missing import:
adding `:- use_module(moda).` to `modc` makes `moda:aa` resolve and the
program runs. A genuine "imported module lacks the export" case produces
the *same* `YCHR-20009` text, which *is* accurate there — so one code +
one message covers three distinct situations (imported-but-not-exported
/ exported-but-not-imported / module-does-not-exist) and the wording is
only correct for the first. The hint partially mitigates the
exported-but-not-imported case. The spec is also silent on whether
qualifying a name requires importing its module; that underlying rule
could be documented in `language.md`.

## Guard that evaluates to a non-boolean errors with a leaked internal name and no source location

**Documented claim.** `docs/reference/errors.md` §`YCHR-60001`: "Also
used for runtime errors raised by the Haskell interpreter (e.g.
arithmetic on non-numbers, calling a non-function)." Other runtime
`YCHR-60001`s print a `file:line`, the offending source, and a stack
trace.

**Test.** A guard whose expression returns an `int` rather than a
`bool`:

    :- chr_constraint p/1, q/0.
    :- function add1/1.
    add1(X) -> X + 1.
    p(X) <=> add1(X) | q.

    ychr run -g 'p(1)'

**Expected.** A `YCHR-60001` pointing at the guard (e.g. line 4), in
user-facing terms (e.g. "guard did not evaluate to a boolean"), ideally
with the same stack-trace treatment other runtime errors get.

**Actual.**

    <generated>:1:1: YCHR-60001
    BFromVal: expected boolean

No source file/line for the guard, no stack trace, and the message leaks
the internal VM construct `BFromVal`.

**Notes.** Same family as the `'$call'(5, 1)` message-quality bug above.
Contrast a sibling `YCHR-60001` that carries full context (file:line,
offending source, and a `=== stack trace ===` section) for a
"no matching equation" runtime failure.

## Data-constructor values from an *unnamed* module print with the diagnostic `<basename>` qualifier

**Documented claim.** `docs/reference/language.md` §Modules:
"Diagnostics refer to such a module by its file basename in angle
brackets (`<a>` for `a.chr`)." The angle-bracket form is specified as a
*diagnostics* convention.

**Test.** Under `=` (non-evaluating), a compound whose functor names a
function is kept as a data term and qualified by its defining module. In
a header-less file that module is unnamed:

    % eq_funcompound.chr  (no :- module header)
    :- chr_constraint t/2.
    :- function double/1.
    double(X) -> X * 2.
    t(R1, R2) <=> R1 = double(YY), R2 = YY.

    ychr run -g 't(A, B)' --show-bindings eq_funcompound.chr

**Expected.** A value rendering that does not embed a diagnostic-only
name. (A `:- module(named).` header renders the same program cleanly as
`A = named:double(_)`.)

**Actual.**

    A = '<eq_funcompound>':double(_)
    B = _

The `<...>` diagnostic name leaks from diagnostic space into ordinary
`run --show-bindings` value output, yielding a non-re-parseable
qualifier.

**Notes.** Surfaces in the main user-facing output path
(`run --show-bindings`), not just in diagnostics.

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
