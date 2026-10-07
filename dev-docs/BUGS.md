# Known Bugs

This document tracks known correctness bugs in the YCHR implementation
that have not yet been fixed. Entries are concrete (file:line, code
snippet, repro) so they can be picked up as standalone tasks.

Remove entries from this file when the underlying bug is fixed.

## Constructor arity mismatch double-reports `YCHR-20102` (warning) and `YCHR-60008` (error)

**Documented claim.** `docs/reference/errors.md` (since removed) lists `YCHR-20102`
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

## A single-signature `:- class` is type-checked as if declared `:- function`

**Documented claim.** `docs/reference/type-system.md` §Signature
Overloading describes the class equation-checking discipline for
`:- class` without a signature-count carve-out: each equation is
checked per candidate signature, a guard's evidence fact that
contradicts the candidate "counts as failure to check under that
signature" (no warning), and an equation that checks under *no*
signature is the `YCHR-60006` `NoMatchingOverload` error. The same
section permits a single-signature `:- class` ("verbose but legal")
without saying it checks differently.

**Test.**

    :- class (sz(int) -> int).
    sz(N) | boolean(N) -> 0.

    ychr check

**Expected.** Per the class discipline: the `boolean(N)` evidence
contradicts the only candidate signature, so the equation checks under
no signature — error `YCHR-60006`.

**Actual.** Warning `YCHR-20104` (inaccessible branch) and the program
compiles — the single-signature-function disposition, where a
contradicting evidence fact marks the equation dead instead of failing
a candidate:

    cls1.chr:2:1: YCHR-20104
    <<function m:sz>>
    This can never fire: a guard requires 'prelude:bool' where the type is 'int'

With two signatures, `:- class (sz(int) -> int), (sz(string) -> int).`
and an equation contradicting both, the same shape is the documented
`YCHR-60006` error.

**Cause.** `walk_funs` (`typechecker/walk.chr`) partitions on
`fun_sig_count(F) > 1`, so a 1-signature class goes down the plain-
function path (`check_equation`) instead of the per-signature attempt
branches of `walk_class_fun`. Use sites are affected the same way:
`build_function_facts` emits `function_sigs` (residual overload
resolution) only for 2+ signatures, so a 1-sig class's calls go through
the unify path — in rigid corner cases that reports `YCHR-60001`
inconsistencies where the resolution path reports `YCHR-60006`. The
declaration kind (`:- class` vs `:- function`) is not consulted; only
the signature count is.
`D.Function` currently does not record the kind, so the partition has
nothing else to look at.

**Impact.** Corner-case only: programs where a 1-sig class's equation
(or use) is rejected/warned differently than the same program with a
second signature, or than the spec's class discipline prescribes.
`test/golden/class_single_sig/` pins only the accept path.

**Fix sketch.** Decide which side gives: either thread the declaration
kind into `D.Function` and partition class functions by kind rather
than signature count (making 1-sig classes take the per-signature
path), or amend `docs/reference/type-system.md` §Signature Overloading
to state that a single-signature class checks exactly like the
equivalent `:- function`. Whichever way, pin the chosen behavior with
a test (`YCHR-60006` golden, or a `TypeCheckTest` case asserting the
warning).

## A user module named `prelude` trips `YCHR-20019` with a hint that is wrong for it

**Documented claim.** `docs/reference/errors.md` (since removed) describes `YCHR-20019`
(`PreludeImportList`) as firing when a `use_module` targeting *the
prelude* carries an import list, on the grounds that "the prelude is
imported implicitly and in full by every module". `prelude` is not a
reserved module name — `reservedModuleNames`
(`src/YCHR/Internal/Resolve.hs:843`) is exactly `["host"]` — so nothing
stops a user file from declaring `:- module(prelude, ...)`, and for
such a module the stated grounds are false.

**Test.**

    % prelude.chr
    :- module(prelude, [foo/1]).
    :- chr_constraint foo/1.
    foo(X) <=> X = 1.

    % main.chr
    :- module(main, [go/1]).
    :- use_module(prelude, [foo/1]).
    :- chr_constraint go/1.
    go(X) <=> foo(X).

    ychr check prelude.chr main.chr

**Expected.** Either the import list narrows normally (it names a
user module, not the stdlib prelude), or the program is rejected for
declaring a module named `prelude` — but not a diagnostic whose
explanation does not apply.

**Actual.**

    main.chr:2:1: YCHR-20019
    use_module(prelude) cannot carry an import list
      Hint: the prelude is imported implicitly and in full by every module; remove the import list
    use_module(prelude, [foo / 1])

Replacing line 2 with the unrestricted `:- use_module(prelude).`
compiles clean (exit 0), so modules named `prelude` are legal today —
this is not an already-rejected corner.

**Cause.** The check in `validateImportLists`
(`src/YCHR/Internal/Rename.hs:582`) keys on
`imp.importModule == "prelude"`. By the rename phase,
`CollectedImport` has deliberately erased the library-vs-module
distinction (`src/YCHR/Internal/Collected.hs:7-17`), so the check
structurally cannot tell the stdlib prelude from a same-named user
module.

Two contributing defects noted here originally have since been fixed in
`Compile/Pipeline.hs`, and neither turned out to be what produces the
misleading message: `addPreludeImport` no longer gives a user module
named `prelude` a synthetic self-import (it now guards on the name, like
its counterpart `Collect.addLibraryPrelude`), and `finalizeCompilation`
now drops a bundled library whose name a user module already carries, so
name-keyed lookups no longer see two providers for one module name.

**Impact.** Narrow: only programs that declare their own module named
`prelude`. Nothing that previously worked is broken — the two import
entries both name `prelude`, so the narrowing was silently widened
before `YCHR-20019` existed. The defect is a misleading diagnostic,
not lost functionality.

**Fix sketch.** Add `"prelude"` to `reservedModuleNames` under a new
`16xxx` code, making the check's premise true by construction rather
than by assumption. This rejects programs that compile today, so it is
a deliberate call, not a silent tightening. Filtering before the
library/module collapse is the alternative, but fights the erasure
that `Collected.hs` documents as intentional. Whichever way, pin it
with a negative golden. Related: the same reasoning would cover the
other stdlib library names (`lists`, `strings`, `meta`). Shadowing them
is no longer silent: the bundled library is dropped in favour of the
user module (pinned by `test/golden/library_shadowing/`), and a module
that imports a library carrying its own name is rejected outright as
`YCHR-10003` (`test/golden/library_self_import/`).

## An unknown bare `use_module(M)` is silently ignored

**Documented claim.** `docs/reference/language.md` §Modules (lines
93–97): a qualified name "is valid only if the current module imports `m`
and `m` exports `name`. Unimported module: `YCHR-20014` … Unknown
module: `YCHR-20015`." The import surface is elsewhere documented as
validated (`YCHR-20005`, `YCHR-20007`, `YCHR-20019`, `YCHR-10001`), and
the DSL separates `importing` (user modules) from `library` (bundled)
(`docs/reference/dsl.md:40-41`).

**Test.**

    :- module(bare, [go/2]).
    :- use_module(nosuchmodule).
    :- chr_constraint go/2.
    go(X, R) <=> R is length(X).

    ychr check bare.chr
    ychr run -g 'bare:go([1,2],R)' --show-bindings bare.chr

**Expected.** A diagnostic naming `nosuchmodule`, or at least a warning
that the import brought nothing into scope.
`use_module(library(nosuchmodule))` correctly gives
`YCHR-10001 Unknown library 'nosuchmodule'`, so the `library(...)` form
*is* validated.

**Actual.**

    === warning ===
    bare.chr:4:14: YCHR-20101
    Undeclared data constructor 'length'
      Hint: declare it with :- chr_type, or check the spelling
    R is length(X)
    R = length([1, 2])
    check exit=0, run exit=0

Nothing mentions `nosuchmodule`. `length` degrades to an opaque
constructor, `is` returns the unevaluated compound, and the query
"succeeds" with the wrong value. A control declaring a local `len/1`
gives `R = 2`, so only the import is bogus. The same silent path swallows
`use_module(lists)`, `use_module(prelude)`, and any other bare name that
is not one of the supplied user modules.

**Notes.** `compileModules` takes its user modules from the command line,
so "the module does not exist" is partly a property of the invocation and
a host embedding may supply the module separately — that is the argument
for treating this as a design question rather than a plain defect. The
counter-argument is the failure mode: a typo yields a wrong *value*, and
the `library(...)` form gets exactly the validation the bare form lacks.

**Fix sketch.** After Collect, reject a bare import whose name is neither
a supplied module nor a bundled library name; reuse `YCHR-20015`
(`UnknownModule`) if that is the intended code, or add one. Add the bare
counterpart of `test/golden/unknown_library`.

## `ychr run --show-bindings` does not filter `_`-prefixed variables

**Documented claim.** `docs/reference/repl.md` §One-shot queries
(lines 174–184): "Bindings are printed, except for variables whose name
starts with `_` (`_X`) — Prolog convention; they are still bound, only
the output is filtered." The same section describes `--show-bindings` as
printing "the bindings one per line, sorted" without restating the
filter.

**Test.**

    :- module(filt, [go/1]).
    :- chr_constraint go/1.
    go(_X) <=> _X = 1.

    ychr run -g 'filt:go(_X)' --show-bindings filt.chr
    printf 'filt:go(_X).\n:quit\n' | ychr repl --quiet filt.chr

**Expected.** Either no `_X` line (the filter is a property of binding
printing) or a line (the filter is REPL-only). The documentation does not
settle it, which is the point of the entry.

**Actual.** `run` prints `_X = 1`; the REPL prints nothing. Two variables
behave the same way: `run` prints `_A = 1` and `_B = 2`, the REPL prints
neither.

**Notes.** The filtering sentence sits in the REPL section, so the doc
does not clearly bind `--show-bindings`. Either way the two surfaces
should not disagree on the same convention. Non-underscore variables
print in both, and sorting is correct.

**Fix sketch.** Decide which surface the convention belongs to and pin it
in the spec; if the filter is meant for both, route `--show-bindings`
through the same printer as the REPL.

## A module-qualified name in a `requiring` bound is parsed as `:/2`

**Documented claim.** `docs/reference/type-system.md` §Declaration syntax
(1497–1512) defines a bound as `name(τ₁, …, τₙ) -> τᵣ`.
`docs/reference/language.md` §Modules (lines 93–97) defines what `m:name`
means in every other position. Nothing says whether a bound name may be
qualified.

**Test.**

    :- module(useq, [foo/2]).
    :- use_module(lib).                       % lib declares gt/2
    :- chr_constraint foo(T, T) requiring lib:gt(T, T) -> bool.
    foo(X, Y) <=> gt(X, Y).

    ychr check lib.chr useq.chr

**Expected.** A qualified bound resolves, or is rejected with a message
that names the qualifier problem.

**Actual.**

    === error ===
    useq.chr:3:39: YCHR-16009
    'useq:foo' requires ':/2' but no such function is declared
      Hint: declare ':- function :/2.' (or import a module that does)

The qualifier is dropped and the bound name becomes the operator `:`. The
same happens for `prelude:'>'(T, T) -> bool` and for a library function
(`strings:string_length(T) -> int`). Unqualified bounds, including
imported ones, work.

**Notes.** The error and the hint are both unusable: `:- function :/2.`
does not parse. If qualification is not meant to be supported, the
diagnostic should say that instead of naming `:/2`.

**Fix sketch.** Either parse the qualified name as a qualified bound
target, or reject it with a diagnostic that quotes the qualifier. Pin
whichever with a golden.

## The global `--quiet` before a subcommand is treated as a file name

**Documented claim.** `ychr --help` shows
`ychr [COMMAND | [--quiet] [--Werror] [--no-check] [FILES...]]`, which
reads as though the global flags may precede a subcommand;
`docs/reference/repl.md` documents `--quiet` for the REPL.

**Test.**

    ychr --quiet repl w.chr
    ychr --quiet check w.chr

**Actual.**

    ychr: Uncaught exception ghc-internal:GHC.Internal.IO.Exception.IOException:
    repl: openFile: does not exist (No such file or directory)

`--quiet` is swallowed, `repl`/`check` is parsed as an input file, and
the command fails on a missing file; `ychr --quiet repl` exits 0.
`ychr repl --quiet` (flag after the subcommand) works as documented.

**Notes.** Per-subcommand `--help` correctly omits `--quiet`
(`ychr check --help`), so `ychr check --quiet` being rejected is
consistent; only the global placement misbehaves.

**Fix sketch.** Either accept the global flags before a subcommand and
apply them to it, or reword the usage line so the flags are shown only
where they are honoured.
