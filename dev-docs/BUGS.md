# Known Bugs

This document tracks known correctness bugs in the YCHR implementation
that have not yet been fixed. Entries are concrete (file:line, code
snippet, repro) so they can be picked up as standalone tasks.

Remove entries from this file when the underlying bug is fixed.

## Qualified data constructors with non-ASCII names display in an unparseable form

**Documented claim.** `docs/reference/syntax.md` §Identifiers and atoms
describes quoted atoms (`'...'`) and notes that `__` is reserved as
the qualified-name separator. The REPL doc and `docs/reference/prelude.md`
imply that displayed values can be fed back through
`read_term_from_string` and that pretty-printing is the inverse of
parsing.

**Test.** Save to `/tmp/m.chr`:

    :- module(m, [t/1]).
    :- use_module(prelude).
    :- chr_type colours ---> 'naïve' ; ordinary.
    :- chr_constraint t/1.
    t(R) <=> R = 'naïve'.

Then in the REPL:

    ychr --quiet /tmp/m.chr
    ychr> m:t(R).

**Expected.** `R = m:'naïve'.` — qualifier preserved, just like for
the ASCII sibling `ordinary` (which prints as `R = m:ordinary.`).

**Actual.** `R = 'm__na__uef__ve'.` — qualifier lost, mangled
`__uXXXX__` unicode escapes leak into the displayed atom.

**Cause.** `Compile.Names.vmName` encodes non-ASCII chars as
`__uHEX__` and joins module/base with `__`, producing
`m__na__uef__ve` at the VM level. `Meta.valueToTerm` recovers the
qualifier by splitting on the first `__`, but its suffix guard
(introduced to keep user-quoted unicode atoms like `'café'` from being
mis-split) refuses the split when the suffix itself contains `__` —
which it does, because of the unicode escapes. See the comment block
at `src/YCHR/Meta.hs` on the `VAtom` arm.

**Impact.** Worse than cosmetic:
- The displayed form `'m__na__uef__ve'` is rejected by the lexer
  (YCHR-50001 — `__` not allowed in atoms), so
  `read_term_from_string(write_term_to_string(R))` errors instead of
  round-tripping.
- The display gives users no path back to the source spelling
  (`m:'naïve'`); they'd have to recognise the encoding by hand.
- Runtime semantics are unaffected — the mangled form is the canonical
  runtime identity, so `==`, unification, pattern matching, and
  storage all behave correctly. The bug surfaces only at the
  value↔string boundary.

**Notes.** Proper fix needs `vmName` to use a separator the lexer
reserves *and* that cannot appear inside an atom's encoded form
(unlike `__`, which collides with `__uXXXX__` unicode escapes). The
ASCII-only case introduced this asymmetric runtime collapse cleanly;
non-ASCII names need a richer encoding scheme.

## `:- list_operators` reports `op(400, yfx, '/')` twice

**Documented claim.** `docs/reference/prelude.md` lists `'/'` once at
priority 400, type `yfx`. `libraries/prelude.chr` declares it once.

**Test.**

    ychr> :list_operators

**Expected.** Each `op(prio, type, name)` listed once.

**Actual.** Two adjacent lines:

    op(400, yfx, '/')
    op(400, yfx, '/')

No duplicate appears for `+`, `*`, etc. The duplication is specific to
`/`.

**Notes.** Cosmetic. Probably an operator-table merge that
double-includes the `:- function ('/'(float, float) -> float).`
declaration's implicit op-entry alongside the explicit
`op(400, yfx, '/')` from the export list.

## Variables starting with `_` are silently suppressed from REPL output

**Documented claim.** `docs/reference/syntax.md` §Identifiers and
atoms: "Variables start with an uppercase letter or underscore, then
letters, digits, or underscores. The bare `_` is the wildcard:
distinct occurrences are independent." This identifies `_X` as a
named variable, not a wildcard. The REPL doc says "Resulting bindings
(if any) are printed."

**Test.**

    ychr> X = 5.
    X = 5.
    ychr> _X = 5.
    ychr>
    ychr> X = 5, _Y = 10.
    X = 5.

**Expected.** Either `_X = 5.` is printed (consistent with the doc's
"named variable" classification) or the doc explicitly notes the
Prolog convention that `_`-prefixed variable names are suppressed.

**Actual.** `_X` and `_Y` bindings are silently omitted from the REPL
output even though they are bound. The doc neither describes nor
justifies this suppression.

**Notes.** Doc-shaped. Either the docs should mention the suppression
or the suppression should be removed.

## Multiple `:- module(...)` directives in the same file are silently accepted; only the first takes effect

**Documented claim.** `docs/reference/language.md` and
`docs/reference/syntax.md` describe `:- module(...)` as optional and
as "the module header". The implicit assumption is that there is at
most one per file. No spec section addresses what happens with
multiple.

**Test.**

    :- module(mm1).
    :- module(mm2).
    :- chr_constraint c/0.
    c <=> true.

**Expected.** Either a clear diagnostic (e.g. `MalformedTopLevel`,
YCHR-15014, or a dedicated "duplicate module header" code), or a
specified behavior.

**Actual.** `ychr check` exits 0 silently. Probing further:
- `ychr run -g 'mm1:c'` succeeds (first module wins).
- `ychr run -g 'mm2:c'` fails with `YCHR-20013 Goal 'mm2:c/0' is not
  exported by its module`.

The second `:- module(...)` is silently dropped without diagnosing it.

**Notes.** Behavior is undocumented; the impl silently drops the
second header. A user mid-refactor could be surprised.

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
`Type mismatch: 'typechecker:int' does not match 'fun(_) -> _'`.

**Notes.** The doc explicitly carves out "calling a non-function" as a
`YCHR-60001` case, but the message for the `'$call'` form is
unintelligible compared to the `call` wrapper.

## Error codes for type names display the internal `typechecker:` qualifier

**Documented claim.** `docs/reference/type-system.md` describes the
built-in types as `int`, `float`, `string`, `any` — no module
qualifier. The catalog of error codes (`docs/reference/errors.md`
§`YCHR-60001`) likewise refers to "types" abstractly.

**Test.**

    :- module(tm).
    :- chr_constraint go(int).
    go(X) <=> X = "hello".

**Expected.** `Type mismatch: 'int' does not match 'string'` (or
similar without an internal qualifier).

**Actual.**

    YCHR-60001
    Type mismatch: 'typechecker:int' does not match 'typechecker:string'

The internal `typechecker:` qualifier on the built-in type names is
exposed in the user-facing diagnostic.

**Notes.** Cosmetic. Either the message should strip the internal
qualifier, or the spec should document that built-in types appear
qualified by `typechecker:` in diagnostics.
