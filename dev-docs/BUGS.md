# Known Bugs

This document tracks known correctness bugs in the YCHR implementation
that have not yet been fixed. Entries are concrete (file:line, code
snippet, repro) so they can be picked up as standalone tasks.

Entries that carry an agreed fix plan have the owner's decisions already
made. A later session can implement straight from the "Fix sketch",
without re-asking what to do. Line numbers are approximate (the file has
moved since).

Remove entries from this file when the underlying bug is fixed.

The four entries below come from an agent QA pass (2026-11-27).


## The `'$call'` diagnostic counts the applied arguments, not the ones written

**Documented claim.** `docs/reference/language.md:1257` and
`docs/reference/type-system.md:1973`: "`'$call'` accepts one to ten
arguments; any other arity, including zero, is `YCHR-16022`".

**Test.** Call it with one written argument, then with eleven.

    :- module(ar1).
    :- function d/0.
    d -> 7.
    :- chr_constraint go/1.
    r @ go(Q) <=> Q is '$call'(fun d/0).

    ychr check ar1.chr

    :- module(ca, [t11/1]).
    :- function d/10.
    d(A, B, C, D, E, F, G, H, I, J) -> J.
    :- chr_constraint t11/1.
    t11(R) <=> R is '$call'(fun d/10, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10).

    ychr run --show-bindings -g 'ca:t11(R)' ca.chr

**Expected.** Both the doc and the message count the same thing. They do
not say which: if "arguments" means the whole compound, `'$call'(F)` is
legal and eleven is not; if it means the ones after the callable, the
message should say "applied arguments" and `'$call'(F)` is "given 0".

**Actual.** The check counts the applied ones
(`callArity = length args - 1`, `src/YCHR/Internal/Resolve.hs:1611`),
so one written argument reads as zero and eleven are accepted.

    ar1.chr:5:15: YCHR-16022
    '$call' takes between 1 and 10 arguments, but was given 0
      Hint: apply the callable to between 1 and 10 arguments
    Q is '$call'(fun d / 0)

Eleven written arguments are accepted (`ca.chr` prints `R = 10`), and
twelve are rejected with "was given 11".

**Notes.** The check is deliberate — `dev-docs/INVARIANTS.md:559` says
out of range includes `'$call'(F)`, and `Resolve.hs:1600-1610` documents
the applied reading — so this is a wording bug, not a semantic one. The
count reaches the user through `UnsupportedCallArity`
(`src/YCHR/Internal/Display.hs:385`). `call/2` to `call/11` are fine.

**Fix sketch.** Not decided. Either name the count in the message and in
both doc sites ("applied arguments"), or count the whole compound, which
then requires accepting `'$call'(F)` and rejecting eleven.


## The catch-boundary example calls `length/1` without importing it

**Documented claim.** `docs/reference/language.md:735-738`: a failure
deep inside a recursive call is caught by the guard, so
`r @ c(L) <=> length(L) > 0 | body.` on `[1|T]` delays.

**Test.** The example with its `body` placeholder filled in.

    :- module(dl2).
    :- chr_constraint c/1, out/1.
    r @ c(L) <=> length(L) > 0 | out(L).

    ychr run -g 'dl2:c([1|T])' dl2.chr

**Expected.** `c([1 | T])` is stored, nothing is reported.

**Actual.**

    === warning ===
    dl2.chr:3:14: YCHR-20101
    Undeclared data constructor 'length'
      Hint: declare it with :- chr_type, or check the spelling
    length(L) > 0
    === runtime error ===
    dl2.chr:3:5: YCHR-60001
    <<rule r>>
    comparison host call: expected 2 int, float or string arguments of the same type, got 2

**Notes.** `length/1` is in `libraries/lists.chr:116`, and a file has to
import a bundled library; only the REPL auto-loads it. So `length(L)` is
an undeclared constructor, the guard is a general failure, and it is
hard instead of delayed. The prose is a fragment (`body` is a
placeholder), but `length(L)` reads as a real call. With
`:- use_module(library(lists)).` it delays as documented, so the guard
machinery is fine. The prelude has no list function to use instead.

**Fix sketch.** Add the import to the example.


## `is` raises on a dereferenced constructor term but returns an inline one

**Documented claim.** `docs/reference/language.md:1029-1030`: a variable
on the right of `is` evaluates "the same way the equivalent expression
written inline evaluates". `:1041-1042`: a compound whose functor is a
data constructor "is not evaluable, so naming one is a runtime error".

**Test.**

    :- module(iso, [b1/1, b2/1, type(pairish/2)]).
    :- chr_type pairish(A, B) ---> pairish(A, B).
    :- chr_constraint b1/1, b2/1.
    b1(R) <=> X = pairish(1, 2), R is X.
    b2(R) <=> R is pairish(1, 2).

    ychr run --show-bindings -g 'iso:b1(R)' iso.chr
    ychr run --show-bindings -g 'iso:b2(R)' iso.chr

**Expected.** One answer for both, per the first claim.

**Actual.**

    === runtime error ===
    iso.chr:4:1: YCHR-60001
    <<rule __rule_20>>
    is: functor is not evaluable: iso:pairish/2

    R = iso:pairish(1, 2)

**Notes.** The split is the tested behaviour: inline construction is
pinned by `test/golden/aggregates_reserved_other_arity`, which expects
`R = aggregates_reserved_other_arity:argmax(1, 2)` from
`is_arg(R) <=> R is argmax(1, 2).`, and the dereferenced form by
`test/golden/is_non_evaluable_error`. So the implementation matches its
goldens and `:1041` is wrong about the inline position. What is really
undecided is a dereferenced term whose functor is a constructor: deep
evaluation walks stored terms (`X = 1 + 1, R is X` gives `2`), and it
has no procedure for a constructor. This is also where the two wholesale
paths part company for constructor *arguments* (`:1050`):
`R is copy_term(pair(1 + 1, 2))` gives `pair(2, 2)`, while
`X = copy_term(pair(1 + 1, 2)), R is X` gives `pair(prelude:(1 + 1), 2)`.

**Fix sketch.** Not decided. Either teach deep evaluation to rebuild
constructor terms, or say in `:1029-1030` and `:1041` that a constructor
term is a value where it is written but not once it comes through a
variable.


## A quoted atom naming a constructor is arity-checked, so `quote(type(P/1))` breaks when a constructor shares the name

**Documented claim.** `docs/reference/language.md:569-571`: "an atom
inside `quote` that names a constructor is that constructor, and the
type checker checks its arity. To name a *type*, use `type(name/arity)`."
And `:599-600`: inside `quote(...)` a type reference "is a plain
compound".

**Test.**

    :- module(tr1).
    :- chr_type box(T) ---> box(T).
    :- chr_constraint go/1, g5/1.
    go(R) <=> R = type(box/1).
    g5(R) <=> R = quote(type(box/1)).

    ychr check tr1.chr

**Expected.** The two sentences cannot both hold: `:571` sends you to
`type(name/arity)`, and `:569-570` rejects the `box` atom inside it
whenever the type has a constructor of the same name, which `:596` calls
normal.

**Actual.**

    tr1.chr:5:11: YCHR-60008
    Data constructor 'tr1:box' is used with 0 argument(s) but declared with 1
    R = quote(type(box / 1))

Without `g5` the module compiles.

**Notes.** Nothing about `type(...)`; any quoted atom that names a
constructor is affected, including plain `quote(box / 1)`, and a
non-parametric type (`:- chr_type box ---> box(int).` with
`quote(type(box/0))`) gives the same 60008. The check is raised by
`typechecker/pure.chr:345` and reported through
`src/YCHR/Internal/TypeCheck.hs:329`. A type whose constructor has
another name is fine: `:- chr_type pair(T) ---> mkpair(T, T).` with
`quote(type(pair/1))` compiles. So a quoted `name/arity` cannot be built
when `name` is a constructor, which is the synthetic-data use `quote`
exists for (`:566-568`).

**Fix sketch.** Not decided. Either exempt the left operand of a quoted
`/`-compound from the constructor arity check, or document the trap and
qualify `:571`.
