# Known Bugs

This document tracks known correctness bugs in the YCHR implementation
that have not yet been fixed. Entries are concrete (file:line, code
snippet, repro) so they can be picked up as standalone tasks.

Entries that carry an agreed fix plan have the owner's decisions already
made. A later session can implement straight from the "Fix sketch",
without re-asking what to do. Line numbers are approximate (the file has
moved since).

Remove entries from this file when the underlying bug is fixed.

The two entries below come from an agent QA pass (2026-11-27).


## `is` raises on a dereferenced constructor term but returns an inline one

**Documented claim.** `docs/reference/language.md:1030-1031`: a variable
on the right of `is` evaluates "the same way the equivalent expression
written inline evaluates". `:1042-1043`: a compound whose functor is a
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
goldens and `:1042` is wrong about the inline position. What is really
undecided is a dereferenced term whose functor is a constructor: deep
evaluation walks stored terms (`X = 1 + 1, R is X` gives `2`), and it
has no procedure for a constructor. This is also where the two wholesale
paths part company for constructor *arguments* (`:1051`):
`R is copy_term(pair(1 + 1, 2))` gives `pair(2, 2)`, while
`X = copy_term(pair(1 + 1, 2)), R is X` gives `pair(prelude:(1 + 1), 2)`.

**Fix sketch.** Not decided. Either teach deep evaluation to rebuild
constructor terms, or say in `:1030-1031` and `:1042` that a constructor
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
