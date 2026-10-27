# Known Bugs

This document tracks known correctness bugs in the YCHR implementation
that have not yet been fixed. Entries are concrete (file:line, code
snippet, repro) so they can be picked up as standalone tasks.

Remove entries from this file when the underlying bug is fixed.

## The `:` compound reaches constraint and function declarations unparsed

**Documented claim.** `docs/reference/language.md` §Modules defines
`module:name` as a qualified reference, resolved the same way in
every position.

**Test.**

    :- module(oc, [fun sz/1]).
    :- open_class sz(int) -> int.
    sz(X) -> X.

    :- module(o1, []).
    :- use_module(oc).
    :- function oc:foo(int) -> int.

    ychr check oc.chr o1.chr

**Expected.** Either a qualified declaration name is rejected (a
declaration always targets the current module), or `oc:foo` resolves
as a genuine qualified reference.

**Actual.** `ychr check` exits 0. `convertFunctionDecl`'s `typedCore`
(`src/YCHR/Internal/Parser.hs`; `convertConstraintDecl`'s generic arm
has the same shape, for `:- chr_constraint oc:foo(int).`) matches the
raw `Compound ":" [Atom "oc", ...]` term, so the declaration is
silently named `:/2` rather than `foo` in module `oc`. No diagnostic.

**Fix sketch.** Reject a `Compound ":"` declaration head with a
dedicated parse error before the generic arm can match it.

## `:- extend_class_type`/`:- extend_class` cannot name their target qualified

**Documented claim.** `dev-docs/PROJECT.md` §Closed and Open Functions
says extension directives "resolve their target through the importing
module's imports," implying `module:name` is legitimate there too.

**Test.**

    :- module(oc, [fun sz/1]).
    :- open_class sz(int) -> int.
    sz(X) -> X.

    :- module(o3, []).
    :- use_module(oc).
    :- extend_class_type oc:sz(string) -> int.
    :- extend_class oc:sz(S) -> 0.

    ychr check oc.chr o3.chr

**Expected.** Either the qualified target resolves (as `sz` with no
qualifier already does), or a diagnostic names the qualifier.

**Actual.** Both lines report `YCHR-20002 Unknown name ':/2'`. The
unqualified spelling (`extend_class_type sz(string) -> int.`) works.

**Notes.** Same parser gap as the entry above. `renameDeclaration`'s
`ExtendClassTypeDecl` case already resolves a qualified `Name` through
imports, so this is plausibly a real feature once the parser stops
reading `oc:sz` as `:/2`.

**Fix sketch.** Give the two directives' head-parsing the same
`Compound ":"` special case `convertConstraint` has.

## `prettyBoundSig` drops a bound's module qualifier

**Documented claim.** None stated.

**Test.** Pretty-print a `requiring` clause naming a qualified bound,
e.g. via the REPL's `:info` command (`renderInfoEntry`, which calls
`prettyConstraintDecl` → `prettyRequiring` → `prettyBoundSig`).

**Expected.** `requiring lib:gt(T, T) -> bool`.

**Actual.** `prettyBoundSig` renders `unqualifiedText b.name`:
`requiring gt(T, T) -> bool`, qualifier silently dropped.

**Notes.** Not as cosmetic as it looks: `renameBoundSig` always
resolves a bound to `Qualified`, so every bound reaching this has a
module to lose.

**Fix sketch.** `flattenName b.name` is not a drop-in fix:
`renderAtom` of the whole flattened text would quote `lib:gt` as one
atom. Build `module ++ ":" ++ renderAtom baseName` instead.

## A restricted import list makes `validateQualified` say the module doesn't export the name

**Documented claim.** `docs/reference/language.md` §Modules:
`validateQualified`'s own Haddock already distinguishes "not exported"
from "excluded by a restricted import list"; the message doesn't.

**Test.**

    :- module(implib, [gt/2, other/1]).
    :- function gt(int, int) -> bool.
    gt(X, Y) -> X > Y.

    :- module(impuser, [bar/2]).
    :- use_module(implib, [other/1]).   % import list omits gt/2
    :- chr_constraint bar(int, int).
    bar(X, Y) <=> implib:gt(X, Y) | true.

    ychr check implib.chr impuser.chr

**Expected.** A message distinguishing "`implib` doesn't export this"
from "your import list doesn't let it through" — the fix differs.

**Actual.**

    === error ===
    impuser.chr:4:15: YCHR-20009
    Module 'implib' does not export 'gt/2'

`implib` *does* export `gt/2`; the restriction is `impuser`'s own
`use_module(implib, [other/1])`. Same for a `requiring` bound naming
`implib:gt` — general `validateQualified` gap, not specific to bounds.

**Fix sketch.** Give `NotExportedByModule` (or a sibling error) a case
for "exported, but excluded by your own import list."

## A missing input file crashes with an uncaught `IOException`

**Documented claim.** None stated; every other compile failure
(parse, rename, resolve, type errors) goes through the diagnostic
envelope (`=== error ===`, a YCHR code) and exits 1.

**Test.**

    ychr check missing.chr
    ychr run -g go missing.chr
    ychr compile missing.chr
    ychr gen-driver -g go missing.chr
    ychr repl missing.chr

**Actual.**

    ychr: Uncaught exception ghc-internal:GHC.Internal.IO.Exception.IOException:
    missing.chr: openFile: does not exist (No such file or directory)

No YCHR code, no banner. `TIO.readFile` in `compileFiles`
(`src/YCHR/Internal/Compile/Pipeline.hs`, around line 729) is
unhandled. The REPL's `:recompile` (`src/YCHR/Internal/Repl.hs`,
around line 276) hits the same path if a loaded file is deleted
before the next `:recompile`, killing the session instead of
reporting the error and keeping the previous program.

**Fix sketch.** A new `FileReadError FilePath Text` constructor on
the `Error` type (`Compile/Pipeline.hs`, re-exported by `YCHR.Run`),
returned by `compileFiles` from a `try @IOException` around the
read, rendered with its own code in `Display.hs`. Add a pytest for
`ychr check missing.chr` and for `:recompile` after
deleting a loaded file.

## `?/1` can be declared, then is silently ignored

**Documented claim.** `docs/reference/macros.md` §Heads and
§Diagnostics list the reserved symbols a macro head may not use
(`,`, `;`, …, `tell`, `$compound`, `$atom`). `?` is not in the list.

**Test.**

    :- chr_constraint '?'/1.
    :- macro '?'(X) ---> [go].

**Expected.** Rejected, like the aggregate keys.

**Actual.** Both are accepted with no warning, but every use — head,
body, or through the macro — reports `YCHR-20042` regardless, so the
declaration is dead weight.

**Fix sketch.** Reserve `?/1`, the way `aggregate/4`, `argmin/2`,
`argmax/2`, `takemin/2` and `takemax/2` now are (`YCHR-20043`,
`Rename.ReservedAggregateName`).

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

## The arity checker misses a wrong-arity use when a constructor name has several arities

**Documented claim.** `docs/reference/type-system.md` §Known
constructors: using a declared constructor at the wrong arity is a
type error (`ConstructorArityMismatch`, YCHR-60008), and the renamer's
own `YCHR-20102` warning reports the same mistake independently.

**Test.**

    % a.chr
    :- module(a, [type(ta/0)]).
    :- chr_type ta ---> foo(int).

    % b.chr
    :- module(b, [type(tb/0)]).
    :- chr_type tb ---> foo(int, int, int).

    % c.chr
    :- module(c, [go/1]).
    :- use_module(a).
    :- use_module(b).
    :- chr_constraint go/1.
    go(R) <=> R = foo(1, 2).

    ychr check a.chr b.chr c.chr

**Expected.** `foo` is declared at arity 1 (module `a`) and arity 3
(module `b`); `foo(1, 2)` matches neither, so the checker should report
`YCHR-60008` the same way it does when `foo` has only one declared
arity.

**Actual.**

    === warning ===
    c.chr:5:11: YCHR-20102
    Data constructor 'foo' used with 2 argument(s) but declared with 1 or 3
    R = foo(1, 2)

Exit code 0. No `YCHR-60008` at all — the checker does not flag the
mismatch when the name resolves to more than one visible arity, even
though it does for the single-arity case
(`test/golden/typecheck_constructor_arity`).

**Notes.** `Rename.canonicalizeDataCon` qualifies a bare constructor
only on an exact `(name, arity)` match, so `foo(1, 2)` reaches the
checker as bare `foo`. The checker's alias table (`typechecker/env.chr`,
`build_con_alias`) is keyed on the name alone and drops any name
declared twice, so `canonicalize_con` leaves it bare, `lookup_con`
misses, and `arity_use_of` takes its `nothing` case, as for an
undeclared name. The renamer keys on `(name, arity)`, so it still sees
`foo/1` and `foo/3`.

**Fix sketch.** Give the checker's constructor-arity check a path for
a bare name that is ambiguous only because of the alias table's
coarser, arity-blind definition: look it up against every type
declaring it (not just the alias table) and compare the used arity
against the set, the way `Rename.warnUnknownDataCon` already does.

## The Scheme `gen-driver` driver does not print variable aliases

**Documented claim.** None; `run` and the Scheme driver disagree.
`SchemeDriver`'s module haddock says it prints bindings "in the same
format as `prettyBindings`."

**Test.**

    :- module(al, [al/2]).
    :- chr_constraint al/2.
    al(R, S) <=> R = S.

    ychr run -g 'al:al(R, S)' --show-bindings al.chr
    ychr gen-driver -g 'al:al(R, S)' al.chr > run.scm
    # then run run.scm with guile against a `-t scheme` compile of al.chr

**Expected.** Both surfaces print the same thing for two query
variables unified together while still unbound.

**Actual.** The Haskell `run --show-bindings` prints:

    R = S
    S = R

The Scheme driver prints:

    R = _
    S = _

**Notes.** `YCHR.Run.executePreparedQuery` groups query variables by
`VarId` and prints each as another member of its alias class rather
than a bare `_`. `SchemeDriver.generateDriver` and `pretty-term` have
no such grouping, so an aliased unbound variable always prints `_`.
The `(ychr repl)` `tell` helper has the same gap.

**Fix sketch.** Port the alias-class grouping to the Scheme side, or
document that it only shows raw unbound-variable output there.

## The Scheme `(ychr repl)` `tell` helper gives `'R 'R` two different variables

**Documented claim.** None stated explicitly, but the same symbol
twice should be the same variable.

**Test.**

    :- module(al, [al/2]).
    :- chr_constraint al/2.
    al(R, S) <=> R = S.

    ; after compiling al.chr to Scheme and importing it:
    (tell s al:al/2 'R 'R)

**Expected.** One fresh variable `R` passed as both arguments; since
`al/2` unifies its two arguments, one `R = <value or _>` line prints.

**Actual.** Two lines print:

    R = _
    R = _

**Notes.** `process-args` calls `make-var` per occurrence with no
symbol table, so `binds` gets two `R` entries.

**Fix sketch.** Have `process-args` memoize symbol → variable within
one call, so a repeat reuses the existing variable instead of making
a new one.

## `YCHR-16002` ignores arity

**Documented claim.** PROJECT.md: function names "cannot collide with
constraint declarations in the same module" (`YCHR-16016`). That check
compares name and arity, so `f/1` as a constraint next to `f/2` as a
function is legal.

**Test.**

    :- chr_constraint p/1, f/1.
    :- function f/2.
    f(X, Y) -> X + Y.
    p(X), f(X) ==> true.

    ychr check n1.chr

**Expected.** No error: `f(X)` in the head is the constraint `f/1`.

**Actual.**

    YCHR-16002
    '<n1>:f' is declared as a function but appears in a rule head

**Notes.** `checkRuleHeads` (`Resolve.hs`) gets
`Set.map qualifiedToName functionNames`, which drops the arity.

## `host:foo(X)` in a rule head is accepted silently

**Documented claim.** `docs/reference/language.md` §Host calls: host
calls are allowed "in every evaluating position". A rule head is not
one, and `YCHR-16002` rejects a function there.

**Test.**

    :- chr_constraint p/1, go/0.
    p(X), host:foo(X) ==> true.
    go <=> p(1).

    ychr check --Werror

**Expected.** An error, like an aggregate goal gives for `host:f(Y)`
(`YCHR-20041`).

**Actual.** No diagnostic, exit 0. `ychr compile -t vm` lists a
constraint type `(qualified "host" "foo")`, and the rule never fires.
