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

**Cause.** `typeCheckProgram`
(`src/YCHR/Internal/TypeCheck.hs:509`) partitions on
`length f.signatures > 1`, so a 1-signature class lands in
`plainFunctions` and is checked by `checkSingleSigEquation` instead of
`checkClassFunction`'s per-signature attempt sessions. Use sites are
affected the same way: `tellFunctionSigs` (`TypeCheck.hs:750`) emits
`function_sigs` (residual overload resolution) only for 2+ signatures,
so a 1-sig class's calls go through the unify path — in rigid corner
cases that reports `YCHR-60001` inconsistencies where the resolution
path reports `YCHR-60006`. The declaration kind (`:- class` vs
`:- function`) is not consulted; only the signature count is.
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

**Documented claim.** `docs/reference/errors.md` describes `YCHR-20019`
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
module. Relatedly, `Compile.Pipeline.addPreludeImport`
(`src/YCHR/Internal/Compile/Pipeline.hs:393`) is unconditional, whereas
its counterpart `Collect.addLibraryPrelude`
(`src/YCHR/Internal/Collect.hs:138`) guards on `m.name == "prelude"` —
so a user module named `prelude` also gets a synthetic self-import.

**Impact.** Narrow: only programs that declare their own module named
`prelude`. Nothing that previously worked is broken — the two import
entries both name `prelude`, so the narrowing was silently widened
before `YCHR-20019` existed. The defect is a misleading diagnostic,
not lost functionality. More broadly, every name-keyed lookup over
modules (`buildExportEnv`, `buildDeclEnv`) conflates the two `prelude`
modules into one provider list, which is its own latent problem.

**Fix sketch.** Add `"prelude"` to `reservedModuleNames` under a new
`16xxx` code, making the check's premise true by construction rather
than by assumption. This rejects programs that compile today, so it is
a deliberate call, not a silent tightening. Filtering before the
library/module collapse is the alternative, but fights the erasure
that `Collected.hs` documents as intentional. Whichever way, pin it
with a negative golden. Related: the same reasoning would cover the
other stdlib library names (`lists`, `strings`, `meta`), which shadow
just as silently — `validateTypeDecls` already works around exactly
this ("a module that shadows a same-named library … is
indistinguishable from itself here", `Rename.hs:1316-1319`).

## `true` / `false` in a head or equation pattern can never match

**Documented claim.** `docs/reference/language.md` treats `true` and
`false` as the constructors of the prelude's `bool` type
(`libraries/prelude.chr:53`), with no carve-out excluding them from
pattern position. `docs/reference/type-system.md` documents `bool` as an
ordinary algebraic type, so `p(true, R) <=> ...` reads as a normal
constructor pattern.

**Test.**

    :- module(booltest, [go/2, neg_of/2]).
    :- chr_constraint go(bool, any), neg_of(bool, any).
    :- function neg(bool) -> bool.
    neg(true)  -> false.
    neg(false) -> true.
    go(true, R)  <=> R = "yes".
    neg_of(X, R) <=> R is neg(X).

    ychr run -g 'booltest:go(true, R)'     --show-bindings booltest.chr
    ychr run -g 'booltest:neg_of(true, R)' --show-bindings booltest.chr

**Expected.** `R = "yes"` for the rule, `R = false` for the function.

**Actual.** The rule silently does not fire:

    R = _

and the function raises, naming the very equation that should have
matched:

    booltest.chr:4:1: YCHR-60001
    <<function booltest:neg/1>>
    CHR runtime error: no matching equation
    neg(true) -> false

Nested patterns fail the same way: with `type(box/0)` exported and
`:- chr_type box ---> box(bool).`, the goal `nested(box(true), R)`
against `nested(box(true), R) <=> R = "inner".` leaves `R` unbound.

**Cause.** The value side and the pattern side disagree about the
representation. Building a `true` value takes the native-bool fast path
— `compileExpr` / `compileTerm`
(`src/YCHR/Internal/Compile.hs:511-514`, `:566-570`) map the
renamer-canonicalized `prelude:true` / `prelude:false` to
`Lit (BoolLit …)`, which evaluates to `VBool`. Matching a `true`
*pattern* does not: HNF emits a `D.GuardMatch` and `compileMatchGuard`
(`src/YCHR/Internal/Compile.hs:743`) lowers it to
`BMatchTerm operand "prelude__true" 0`, a compound/atom test. `matchTerm`
(`src/YCHR/Internal/Runtime/Var.hs:275-281`) accepts `VAtom` and `VTerm`
only, so a `VBool` falls through to `False`. The Scheme runtime's
`match-term` (`scheme/ychr/var.sls:192-199`) has the identical shape, so
both backends are affected. Bare `true` in a rule *body* is unaffected
(it means "empty body"), and `X == true` in a guard is unaffected (it
compiles to `BEqual` against a `BoolLit`, which `equal` handles).

**Impact.** Every `true` / `false` in a rule-head or function-equation
pattern, at any nesting depth. Rules quietly do not fire; functions
raise `YCHR-60001` pointing at the equation that should have matched.
Pre-dates the goal-argument canonicalization work — it reproduces on the
surface-text path, and a host-built `atom "true"` failed the same way
before canonicalization (as `VAtom "true"` against `"prelude__true"`).

**Fix sketch.** Make the pattern side mirror the value side in the
compiler, where the `prelude:true` / `prelude:false` mapping is already
stated: have `compileMatchGuard` emit `BEqual operand (Lit (BoolLit b))`
for a `GuardMatch` naming those two constructors at arity 0, instead of
a `BMatchTerm`. Teaching `matchTerm` about `VBool` is the alternative,
but that hard-codes the mangled `prelude__true` spelling in both
runtimes rather than keeping the knowledge in the one layer that already
owns it. Pin it with a golden covering all three shapes: head pattern,
equation pattern, and nested pattern.

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
no source of their own (`:130-139`), so `checkSingleSigEquation`
(`src/YCHR/Internal/TypeCheck.hs:1727`) has nothing better to attribute
to. Extension equations gathered from other modules are appended to
that list and inherit the owner's `AnnP`. The per-unit `UnitId` work
keeps such equations' diagnostics *apart*, but cannot place them.

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
