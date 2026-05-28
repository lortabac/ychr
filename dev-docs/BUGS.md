# Known Bugs

This document tracks known correctness bugs in the YCHR implementation
that have not yet been fixed. Entries are concrete (file:line, code
snippet, repro) so they can be picked up as standalone tasks.

Remove entries from this file when the underlying bug is fixed.

## Internal post-condition leak on unqualified bad `fun name/arity`

**Documented claim.** Diagnostics carry stable `YCHR-NNNNN` codes
(`docs/reference/errors.md` §Catalog).

**Test.** Typed at the REPL with no `nonexistent` declared anywhere:

    R is call(fun nonexistent/2, 1, 2).

**Expected.** A user-facing diagnostic with a `YCHR-NNNNN` code —
naturally `YCHR-20002` (`UnknownName`).

**Actual.**

    Error: YCHR.Resolve.parseFlatName: missing ':' separator in
    nonexistent — renamer post-condition violated

An internal post-condition assertion leaks to the user as a plain
`Error:` line, with no error code and a reference to a Haskell
function name. The qualified form `fun foobar:nonexistent/2` is
handled cleanly with `YCHR-20009` (`NotExportedByModule`), so the leak
is specifically on the unqualified-and-unknown path through
`Resolve.parseFlatName`.

**Notes.** The renamer's invariant that all names reaching
`parseFlatName` are already qualified is being violated by the
function-reference path before the regular `UnknownName` diagnostic
gets a chance to fire.

## Spurious "Undeclared data constructor" warnings for `fun` and `->` when a lambda appears directly as a constraint argument

**Documented claim.** `YCHR-20101` (`docs/reference/errors.md`):
"A symbol used in constructor position is not declared with
`:- chr_type`." Lambdas are first-class values
(`docs/reference/language.md` §Lambdas and function references), not
data constructors; `fun`/`->` are lambda syntax.

**Test.**

    :- module(la).
    :- chr_constraint c/1.
    :- chr_constraint go/1.
    go(R) <=> c(fun(X) -> X + 1 end), R = ok.

**Expected.** At most one `YCHR-20101` for `ok`.

**Actual.** Three warnings:

    YCHR-20101: Undeclared data constructor 'fun'
    YCHR-20101: Undeclared data constructor '->'
    YCHR-20101: Undeclared data constructor 'ok'

If the lambda is first bound to a variable and then passed
(`F = fun(X) -> X + 1 end, c(F)`), the spurious `fun` and `->`
warnings disappear; only the legitimate `ok` warning fires.

**Notes.** Warning-only. The constructor-validation pass appears to
descend into lambda subterms in argument position and treat the
surface lambda compound `'->'(fun(X), X + 1)` as data, surfacing its
synthetic functors `fun` and `->` as "undeclared constructors".

## Zero-arity constructors print as `name()` with empty parens

**Documented claim.** `docs/reference/syntax.md` lists `foo`, `'a-b'`
as atom literal forms. Existing golden tests use `red` / `green` /
etc. as bare atoms in expected output. Pretty-printing of 0-arity user
constructors is not explicitly specified.

**Test.**

    :- module(mod_a).
    :- chr_type myord ---> mlt ; meq ; mgt.
    :- chr_constraint go/2.
    go(N, R) <=> R is cmp(N, 5).   %% returns mlt | meq | mgt

**Expected.** `R = mod_a:mlt` (or `R = mlt` after disambiguation).

**Actual.** `R = mod_a:mlt()` — with empty parens. Same for
`leaf` from a recursive type: `nt:node(1, nt:leaf(), nt:leaf())`. Same
for `prelude:true()` / `prelude:false()` from a literal `true` (see
the boolean-printing bug above).

**Notes.** Ambiguous — could be defensible (disambiguates atom from
0-arity ctor visually), but it diverges from the convention used in
doc snippets that show bare names like `B = true.` and `mod_a:meq`.
Worth a spec line either way.

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
