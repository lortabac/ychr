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

## Two input files may declare the same module name, silently merging

**Documented claim.** Implicit: a module is declared in one place.
`YCHR-15015` (`DuplicateModuleHeader`) rejects a second `:- module`
directive *within one file*, but nothing rejects the same module name
across two input files.

**Test.**

    % a.chr
    :- module(m, []).
    :- function f/1.
    f(1) -> 1.

    % b.chr
    :- module(m, []).
    :- function f/1.
    f(2) -> 2.

    ychr check a.chr b.chr

**Expected.** An error naming the duplicate module declaration.

**Actual.** Exit 0. The two files' declarations and equations are
silently merged into one module (`resolveFunctions` groups by
qualified name, so both files' `f/1` decls land in one group and both
equations are gathered — one `CollectedModule` per file, same name).

**Impact.** Confusing merge semantics nobody specified; and every
grouping step keyed by qualified name silently assumes module names
are unique. `resolveFunctions` deliberately gathers equations once per
*distinct declaring module* (`src/YCHR/Internal/Resolve.hs`, `build`)
so this input keeps both files' equations rather than dropping one —
remove that accommodation when fixing this.

**Fix sketch.** Reject the whole category: after Collect, group the
collected modules by name and report a duplicate-module-name error
(new code) naming both files. Decide whether the same *file* listed
twice on the command line should dedup or also error.

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

## Diagnostics for an `:- extend_function` equation blame the owner's first equation

**Documented claim.** Implicit: a diagnostic points at the code that
caused it.

**Test.**

    ychr check test/golden/typecheck_open_function_dead_equation/*.chr

The dead equation is `classify("oops") -> 1`, written in
`b_extender.chr` as an `:- extend_function` directive.

**Expected.** The warning is anchored in `b_extender.chr`, at the
extension directive, echoing its source line.

**Actual.**

    a_owner.chr:4:1: YCHR-20104
    <<function owner:classify>>
    This can never fire: a guard requires 'int' where the type is 'string'
    classify(0) -> 100

Wrong file, wrong line, and a source snippet showing an unrelated
equation that is perfectly well-typed.

**Cause.** `D.Function.equations` is an `AnnP [Equation]`
(`src/YCHR/Internal/Desugared.hs:126`) — one location for the whole
list, taken from the owning declaration. Individual `Equation`s carry
no source of their own (`:130-139`), so `check_equation`
(`typechecker/walk.chr`), which carries the function's `ann` block
into every equation's `ctx`, has nothing better to attribute to.
Extension equations gathered from other modules are appended to that
list and inherit the owner's `AnnP`. Per-equation `unit_id`s keep such
equations' diagnostics *apart*, but cannot place them.

**Impact.** Any diagnostic from an extension equation — the warning
above, and equally an error — sends the reader to the wrong file. It
gets worse the more modules extend one open function. Was invisible
before extension equations were genuinely type-checked.

**Fix sketch.** Give equations their own source: change
`equations :: AnnP [Equation]` to `[AnnP Equation]` (or add
`loc`/`origin` fields to `Equation`) and thread the per-equation
annotation through Resolve's `gatherEquations`, Desugar, Compile, and
TypeCheck. `Exhaustiveness.hs` already reads `fd.equations` per
equation and would gain the same benefit. Pin it with a negative
golden whose `.error` file names the extending module's file.

## `docs/reference/language.md:99` documents a `use_module` equivalence that the rest of the docs and the implementation both contradict

**Documented claim.** `docs/reference/language.md` §Modules (line 99):
"`:- use_module(M)` and `:- use_module(library(M))` are equivalent; there
is no library search path."

**Test.**

    :- module(i1, [go/2]).          % and i2 with the other spelling
    :- use_module(lists).
    :- chr_constraint go/2.
    go(X, R) <=> R is length(X).

    ychr run -g 'i1:go([1,2],R)' --show-bindings i1.chr      # bare
    ychr run -g 'i2:go([1,2],R)' --show-bindings i2.chr      # library(lists)

**Expected.** Per line 99, identical results.

**Actual.**

    use_module(lists)           -> YCHR-20101 'length' undeclared; R = length([1, 2])
    use_module(library(lists))  -> R = 2

**Notes.** This entry is a *documentation* defect, filed here because the
line's consequence is severe: a reader who follows it gets a silently
wrong value rather than an error. Line 99 is the only text promising the
equivalence. Everywhere else says the opposite — `docs/README.md:29`
("the others need `:- use_module(library(name))`"),
`docs/reference/dsl.md:41` (bare `use_module(other)` maps to the DSL's
`importing`, `library(lists)` to `library`),
`docs/reference/language.md:64` and `:587`, and all of `search.md`. The
implementation draws the same distinction:
`use_module(M)` names a *user module* supplied to the compile,
`library(M)` names a *bundled library*;
`resolveLibraryClosure` looks bare `library(...)` names up in the stdlib
map and reports `YCHR-10001` for an unknown one
(`src/YCHR/Internal/Collect.hs:105-112`), and `compileModules` documents
the split (`src/YCHR/Internal/Compile/Pipeline.hs:242-246`).

**Fix sketch.** Amend line 99 to say that bundled libraries are reached
only through `library(name)`, and drop the "equivalent" claim.

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

## The REPL does not accept `%` comments

**Documented claim.** `docs/reference/language.md` §Lexical syntax (line
11): "Comments: `%` to end of line. No block comments."
`docs/reference/repl.md` §One-shot queries: "Outside a live session each
input is a goal run against a fresh store." Nothing scopes comments to
files.

**Test.**

    printf 'X = 1. %% trailing comment\n:quit\n' | ychr repl --quiet
    printf '%% only a comment\nX = 1.\n:quit\n' | ychr repl --quiet

**Expected.** The comment is stripped to end of line; the goal runs and a
comment-only line is a no-op.

**Actual.**

    === error ===
    <query>:1:6: YCHR-50001
    unexpected '.'
    expecting digit, space, "%", lowercase letter or end of input

    === error ===
    <query>:1:17: YCHR-50001
    unexpected end of input
    expecting space, "%", uppercase letter, "_", "-", digit, "\"", "[", "fun", "(", lowercase letter or "'"

The reader strips a period only when the line ends with one and never
strips a comment, so the goal text reaches the parser intact. The parse
error even lists `%` among the expected tokens, so the grammar accepts
comments and the REPL reader does not. Comments work in files (control: a
file containing only `% c` checks with exit 0). A goal split over two
lines fails the same way, because only the first line is sent.

**Notes.** Affects every REPL input, including live sessions. The related
reader bug is that a period is stripped only when it is last: for
`X = 1. % c` the period is fed to the parser too.

**Fix sketch.** Strip the comment (and any trailing whitespace) from each
REPL line before reading it as a goal, as the file path already does.
Cover a trailing comment, a comment-only line, and a comment inside a
string literal (which must stay literal).

## A CRLF line ending corrupts the following REPL input

**Documented claim.** `docs/reference/repl.md` §Starting the REPL and
§One-shot queries: the REPL reads "each input" as a goal; no line-ending
restriction is documented, and `%` to end of line
(`docs/reference/language.md` line 11) implies the terminator is
consumed.

**Test.**

    printf 'X = 1.\r\n:quit\r\n' | ychr repl --quiet

**Expected.** `X = 1.` runs, then `:quit` exits.

**Actual.**

    X = 1.
    === error ===
    <query>:1:2: YCHR-50001
    unexpected "q"
    expecting digit, space, "%", lowercase letter or end of input

The reader splits on `\n` and leaves the `\r`, so the *next* input becomes
`:quit\r` and is read as a goal starting with `:`. The `\r` on the first
line is tolerated, which makes the error look like it belongs to the
following line.

**Notes.** CRLF files are normal on Windows. If the REPL is deliberately
LF-only, the reference should say so; as written, the behaviour is
undefined and the failure lands on the wrong line.

**Fix sketch.** Trim `\r` (or split on either terminator) in the REPL
reader, alongside the comment stripping above.

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

## A type declared but not exported is reported in a constructor field with a self-contradictory `YCHR-60013`

**Documented claim.** `docs/reference/type-system.md` §Type Definition
Validation: an undefined type in a constructor field is `YCHR-60005`
(`UndefinedType`); `YCHR-60013` is the *arity* error for a type applied
to the wrong number of arguments. `docs/reference/language.md` §Type and
constructor exports: a type is exported with `type(Name/Arity)`;
§Modules (lines 93–97) gives `YCHR-20009` for a reference to something
the defining module does not export.

**Test.** Two exporters differing *only* in the export list, and one
consumer used with each.

    % exp_none.chr                        | exp_type.chr
    :- module(exp_none, [mkcol/0]).       | :- module(exp_type, [type(col/0), mkcol/0]).
    :- chr_type col ---> red ; green.     | :- chr_type col ---> red ; green.
    :- function mkcol/0.                  | :- function mkcol/0.
    mkcol() -> red.                       | mkcol() -> red.

    :- module(cons, []).
    :- use_module(exp_none).        % or exp_type
    :- chr_type box ---> bx(col).

    ychr check exp_none.chr cons_exp_none.chr
    ychr check exp_type.chr cons_exp_type.chr

**Expected.** Either the reference is accepted, or it is rejected with an
undefined-type / visibility diagnostic (`YCHR-60005` or an export code).
An arity complaint is not available here: `col` is nullary and is written
with zero arguments.

**Actual.**

    === error ===
    cons_exp_none.chr:3:13: YCHR-60013
    Type 'col' is applied to 0 argument(s) but declared with 0 parameter(s), in constructor 'cons_exp_none:bx' of type 'cons_exp_none:box'
    exit=1

The exported-type control is exit 0 with no output. The message
contradicts itself: applying a name to zero arguments cannot mismatch a
declared arity of zero. If the importer also names the type in its import
list the case is caught earlier and correctly —
`use_module(exp_none, [type(col/0)])` gives `YCHR-20005`, while the same
import against `exp_type` is clean.

**Notes.** The defect is the *diagnostic*, not the visibility rule: the
implausible `60013` should be the documented `60005` (or a visibility
error). The repro is a controlled A/B on the export list, with no value
flow and no zero-arity *call* involved.

**Fix sketch.** In the field-type validation path, distinguish "known but
not visible here" from "known with a different arity" and report the
former as `YCHR-60005` or the applicable export code. Pin the A/B above
as a golden.

## An unimported module's exported constructor reports `YCHR-20010` with a false message, not `YCHR-20014`

**Documented claim.** `docs/reference/language.md` §Modules (lines
93–97): an unimported module is `YCHR-20014` (`ModuleNotImported`).
§Type and constructor exports (lines 140–141) reserves `YCHR-20010` for a
constructor outside the *exporter's* allowlist.

**Test.**

    % palette.chr
    :- module(palette, [type(col/0, [red, green])]).
    :- chr_type col ---> red ; green ; blue.

    % main.chr
    :- module(main, [go/2]).
    :- chr_constraint go/2.
    go(X, R) <=> R = palette:red.

    ychr check main.chr palette.chr

**Expected.** `YCHR-20014 ModuleNotImported` — `main` never imports
`palette`.

**Actual.**

    === error ===
    main.chr:3:14: YCHR-20010
    Module 'palette' does not export data constructor 'red/0'
      Hint: add 'red' to the type's constructor export list in 'palette' (e.g. type(t/n, [red, ...]))
    exit=1

Both the code and the message are wrong: `palette` *does* export `red`;
the defect is the missing import. The function analogue
(`opslib:'<>>'(3,4)` without importing `opslib`) correctly gives
`YCHR-20014`, so the divergence is constructor-specific.

**Notes.** Importing `palette` makes the same reference compile clean,
and importing it with `red` excluded from the allowlist correctly gives
`20010`. `src/YCHR/Internal/Rename.hs:1147-1155` checks a program-wide
constructor provider map before the module-import checks, which is
consistent with the observed precedence.

**Fix sketch.** Order the constructor checks as the function checks are
ordered: unknown module, then not imported, then not exported by that
module, then outside its allowlist. `YCHR-20010`'s message should only
fire when the *exporter* excludes the constructor.

## `ychr compile -t vm -d DIR` fails when `DIR` does not exist

**Documented claim.** `docs/how-to/scheme-repl.md` §1 (line 18) shows
`ychr compile -t scheme -n fib -d /tmp/fib-repl test/golden/fib/fib.chr`
with the expected output "→ /tmp/fib-repl/ychr/generated/fib.sls", i.e.
the output directory is created; line 97 repeats the pattern with
`-d build/`. Neither `--help` nor the reference states whether `-d`
creates the directory.

**Test.**

    ychr compile -t vm -d no_such_dir c.chr
    ychr compile -t scheme -d no_such_dir2 c.chr

**Expected.** The two targets agree, and the how-to's example works as
written.

**Actual.**

    ychr: Uncaught exception ghc-internal:GHC.Internal.IO.Exception.IOException:
    no_such_dir/program.vm: withFile: does not exist (No such file or directory)

for `-t vm`; `-t scheme` *does* create its nested directory. So the
targets disagree, and the `-t vm` failure is an uncaught host exception
with an internal backtrace rather than a diagnostic.

**Fix sketch.** Create the output directory in the `-t vm` writer (the
scheme target already does), or document the requirement and replace the
exception with a diagnostic.

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
