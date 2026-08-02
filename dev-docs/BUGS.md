# Known Bugs

This document tracks known correctness bugs in the YCHR implementation
that have not yet been fixed. Entries are concrete (file:line, code
snippet, repro) so they can be picked up as standalone tasks.

Remove entries from this file when the underlying bug is fixed.

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

## `push-frame` serializes as bare atoms, breaking VM-dump round-trips

**Documented claim.** `src/YCHR/Internal/VM/SExpr.hs:3-8` says the
s-expression format "is designed for consumption by external backends
… and as a compilation cache artifact", and `deserialize` is the
inverse of `serialize`. `docs/reference/vm.md` §push-frame currently
documents the fields as display-only *because of this bug*; update it
when fixing.

**Test.**

    ychr compile -t vm mymodule.chr        # any program with ≥1 rule
    # then feed program.vm to YCHR.Internal.VM.SExpr.deserialize

**Expected.** `deserialize` returns the same `VMProgram` that
`serialize` produced.

**Actual.**

    deserialize failed: "<sexpr>" (line 1, column 2469):
    unexpected ","
    expecting "(", "\"" or ")"

**Cause.** `stmtToSExpr` (`src/YCHR/Internal/VM/SExpr.hs:183-191`)
emits all five `push-frame` fields as `SAtom` — label, line, col,
file, and pretty-printed source — so a frame like

    (push-frame rule reflexivity 4 15 mymodule.chr leq(X, X))

contains atoms with spaces, commas, and parentheses (`rule
reflexivity`, `leq(X, X)`), which the s-expression grammar cannot
re-read. Every program containing a rule or a user-defined function
(including anything importing the prelude) is affected, so in practice
no `-t vm` dump round-trips. The `push-frame` deserializer at
`SExpr.hs:413-426` expects exactly five atoms and is unreachable on
real output.

**Fix sketch.** Emit the label, file, and source fields as `SString`
and line/col as `SInt`, and match those constructors in the
deserializer (the current `SAtom` patterns for line/col could never
match re-parsed output anyway, since bare digits lex as `SInt`).
Pre-0.1 there are no dump-compatibility constraints. Then drop the
"display-only" caveat from `docs/reference/vm.md` §push-frame.

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
