# Known Bugs

This document tracks known correctness bugs in the YCHR implementation
that have not yet been fixed. Entries are concrete (file:line, code
snippet, repro) so they can be picked up as standalone tasks.

Entries that carry an agreed fix plan have the owner's decisions already
made. A later session can implement straight from the "Fix sketch",
without re-asking what to do. Line numbers are approximate (the file has
moved since).

Remove entries from this file when the underlying bug is fixed.

The entry below comes from an agent QA pass (2026-11-27).


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
