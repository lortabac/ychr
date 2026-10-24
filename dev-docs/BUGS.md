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

## A function call in an aggregate goal is silently compiled as a constraint

**Documented claim.** `docs/reference/aggregates.md` §Diagnostics:
`YCHR-20041` (`MalformedAggregateGoal`) is "A goal conjunct that is
neither a constraint, an aggregate nor a `?` guard."

**Test.** Forget the `?` in front of a goal guard.

    :- use_module(library(aggregates)).
    :- chr_constraint p/1, k/1, res/1, go/1, ask/1.
    p(X), count((k(Y), X == Y), N) ==> res(N).
    res(N) \ ask(R) <=> R = N.
    go(R) <=> k(1), k(2), k(1), p(1), ask(R).

    ychr check --Werror
    ychr run -g 'go(R)' --show-bindings

**Expected.** `YCHR-20041`. A regular head rejects the same thing:
`p(X), X == 1 ==> true` gives `YCHR-16002 'prelude:==' is declared as a
function but appears in a rule head`.

**Actual.** No diagnostic, `check --Werror` exits 0, and the run gives
`R = 0` (`R = 2` with `? X == Y`). `ychr compile -t vm` lists a
constraint type `(qualified "prelude" "==")` in `type-names`: the
function name was made into a constraint type.

**Notes.** Same with `Y > 1`, a user function `f(Y)`,
`exists(X == 1)` and `count(1 + 1, N)`, and same on Scheme. A data
constructor in the same spot is caught (`YCHR-20002`), so only
functions get through. Missing a `?` is an easy typo, and it gives a
wrong count with no warning.

**Fix sketch.** Reject a goal conjunct that resolves to a function,
like the head check does (`16002` or `20041`). Add a golden.

## `_` passed to a goal macro becomes several unrelated variables

**Documented claim.** `docs/reference/macros.md` §Expanding a goal
macro, step 3: "Replace each head variable with the argument term it
was bound to." §Patterns: "An argument that contains `_` is never
identical to anything, since each `_` is a distinct variable."
`docs/reference/language.md` §Lexical syntax: "`_` alone is the
anonymous variable; each occurrence is distinct."

**Test.** A parameter used twice, called with `_`.

    :- use_module(library(aggregates)).
    :- chr_constraint k/1, j/1, p/0, res/1, go/1, ask/1.
    :- macro both(X) ---> [k(X), j(X)].
    p, count(both(_), N) ==> res(N).
    res(N) \ ask(R) <=> R = N.
    go(R) <=> k(1), k(2), j(1), j(3), p, ask(R).

    ychr run -g 'go(R)' --show-bindings

**Expected.** Read together, the spec implies two unrelated
variables: the argument `_` is copied once per occurrence of `X`. That
is surprising, since a user would likely expect a join, as with
`both(Z)`, and nothing warns.

**Actual.** `R = 4` (cross product). `both(Z)` gives `R = 1`. No
warning, `--Werror` passes. With `:- macro big(X) ---> [k(X), ? X > 5]`,
`count(big(_), N)` evaluates `? _ > 5`, which is an instantiation
error, so the aggregate is undefined and the rule never fires. Both
backends agree.

**Fix sketch.** Either keep the behavior and say so plainly in
§Expanding a goal macro (call-by-name), or change it. If the copies
stay distinct, warn when a `_` argument binds a parameter that
occurs more than once in the body.

## A `?` guard in a rule head reports `YCHR-20002`, not `YCHR-20042`

**Documented claim.** `docs/reference/aggregates.md` §Diagnostics:
`YCHR-20042` (`GuardOutsideAggregateGoal`) is "A `?` guard outside an
aggregate goal."

**Test.**

    :- use_module(library(aggregates)).
    :- chr_constraint p/1, go/0.
    p(X), ? X > 5 ==> true.
    go <=> true.

    ychr check

**Expected.** `YCHR-20042`.

**Actual.**

    YCHR-20002
    Unknown name '?/1'

**Notes.** In a body `?` gives `20042` as documented, directly or through
a macro. In a head it is `20002` every way: directly, in the removed
part (`p(X) \ ? X > 5 <=> q`), or through a macro. No golden uses
`20039`–`20042`.

## Body control forms in an aggregate goal report `YCHR-20002`, not `YCHR-20041`

**Documented claim.** `docs/reference/aggregates.md` §Diagnostics,
`YCHR-20041`, as above.

**Test.**

    p(X), count((k(Y), Y = 1), N) ==> q.
    p(X), count((k(Y) ; p(Y)), N) ==> q.
    p(X), count(true, N) ==> q.

    ychr check

**Expected.** `YCHR-20041`.

**Actual.** `YCHR-20002 Unknown name '=/2'`, `';/2'` and `'true/0'`.
`20041` does fire for a number, a string or a variable conjunct
(`count((k(Y), 1), N)`).

**Notes.** That `20041` message says "Invalid aggregate
'aggregate/4'", which names the core form and not the `count/2` the
user wrote.

## `aggregate/4` and the selection names can be declared, then are silently ignored

**Documented claim.** `docs/reference/macros.md` §Heads and
§Diagnostics list the reserved symbols a macro head may not use
(`,`, `;`, …, `tell`, `$compound`, `$atom`). `aggregate`, `argmin`,
`argmax`, `takemin` and `takemax` are not in the list. A goal macro is
"recognized by name and arity in goal positions".

**Test.**

    :- chr_constraint k/1, p/0, best/1, go/1, ask/1.
    :- macro argmin(X, G) ---> [k(X), G].
    p, argmin(X, k(X)) ==> best(X).
    best(X) \ ask(R) <=> R = X.
    go(R) <=> k(3), k(1), p, ask(R).

    ychr run -g 'go(R)' --show-bindings

**Expected.** Either the macro expands (the head becomes
`p, k(X), k(X)`, which never fires here) or the definition is rejected.

**Actual.** Accepted with no warning, the core `argmin` wins
(`R = 1`), and the macro is never used. `go <=> argmin(1, k(2))` gives
`YCHR-20040` rather than an expansion. `:- macro aggregate(A, B, C, D)
---> [...]` is accepted too, and its head use gives "Invalid aggregate
'aggregate/4'". `:- chr_constraint argmin/2` is accepted, but no tell of
it can be written (`20040`).

**Fix sketch.** Reserve the five names for constraints, functions and
macros at those arities, or document which one wins.

## An aggregate in a guard or an expression does not report `YCHR-20040`

**Documented claim.** `docs/reference/aggregates.md` §Diagnostics:
`YCHR-20040` (`AggregateOutsideHead`) is "`aggregate/4` or a selection
form outside a rule head". Its hint says "it cannot appear in a body, a
query or a guard".

**Test.**

    p(X) ==> argmin(Y, k(Y)) | q.
    p(X) ==> takemin(Y, k(Y)) | q.
    p(X), count(k(Y), N) ==> N > 0, aggregate(aggregates:count_spec, 1, k(_), 0) | q.
    p(X), count(k(Y), N) ==> N > 0 | R is aggregate(aggregates:count_spec, 1, k(_), 0), q.

    ychr check

**Expected.** `YCHR-20040`.

**Actual.** In a guard: `YCHR-30002 This expression cannot evaluate to
a boolean and is not valid as a guard`. In an `is` right-hand side: the
warning `YCHR-20101 Undeclared data constructor 'aggregate'`. `20040`
only fires for a body goal or a query goal.

## `argmin` with NaN keys picks a different match than the spec's definition

**Documented claim.** `docs/reference/aggregates.md` §Selection
aggregates: the selected matches are those of
`Goal, \+ (Goal', ? X' < X)`; "On ties, the rule fires with the first
minimal match in goal order", and "The equivalence fixes which match is
selected".

**Test.**

    :- chr_constraint k/1, p/0, best/1, go/1, ask/1.
    p, argmin(X, k(X)) ==> best(X).
    best(X) \ ask(R) <=> R = X.
    go(R) <=> N is 0.0 / 0.0, k(2.0), k(N), k(1.0), p, ask(R).

    ychr run -g 'go(R)' --show-bindings

**Expected.** Under the definition, `2.0` is not minimal (`1.0 < 2.0`).
`NaN` and `1.0` both are, since nothing is `< NaN` and `NaN < 1.0` is
false. The first in goal order is `NaN`.

**Actual.** `R = 1.0`, on both backends. The implementation keeps a
running minimum (§Implementation notes), and that only agrees with the
definition when `<` is a total order.

**Notes.** The Implementation notes mention NaN, but only for the
take-form re-selection.

**Fix sketch.** Most likely a doc fix: say keys must be totally ordered,
or that NaN keys give an unspecified pick.

## The `--dump-splices` example in macros.md is not the real output

**Documented claim.** `docs/reference/macros.md` §Dumping the splices
shows this for the `counter` example:

    :- chr_constraint clicks / 1.
    :- chr_constraint inc_clicks / 0.
    clicks(N), inc_clicks <=> M is N + 1, clicks(M).

**Test.** The `counter` module from the same page.

    ychr check --dump-splices counter.chr

**Actual.**

    % splices for counter.chr (module counter)
    % counter:counter/1 at counter.chr:7:1
    :- chr_constraint clicks / 1, inc_clicks / 0.
    clicks(_decl_0_N), inc_clicks <=> _decl_0_M is _decl_0_N + 1, clicks(_decl_0_M).

**Notes.** Doc only. The output is right: the macro writes one
directive, so the dump shows one line, and body variables show their
fresh names (`_decl_<n>_<Name>`), as §Pipeline placement says. The
example was not captured from a run.

**Fix sketch.** Paste the real output, and add that body variables show
up under their fresh names.

## A user can add equations after a function a declaration macro generated

**Documented claim.** `docs/reference/macros.md` §Expanding a
declaration macro, "Position matters": "…so a declaration macro can
generate a whole function. A user can't add equations to it with
clauses written around the use."

**Test.**

    :- macro_decls fn(F) ---> [(:- function F/1), ('$compound'(F, [0]) -> 1)].
    :- fn(g).
    g(_) -> 2.

    ychr check

**Expected.** Rejected (`YCHR-15001`), going by the quoted sentence.

**Actual.** Accepted. The spliced equations are contiguous, so the
contiguity rule is happy. An equation written *before* the use is
rejected (`15001`), because the generated declaration sits between the
two equations.

**Notes.** The paragraph's own rule, "Contiguity rules apply to the
module as spliced", predicts what happens. The sentence after it says
more than that.

**Fix sketch.** Doc fix: say the user can't add equations *before* the
use, or drop the sentence.
