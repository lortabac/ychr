# Known Bugs

This document tracks known correctness bugs in the YCHR implementation
that have not yet been fixed. Entries are concrete (file:line, code
snippet, repro) so they can be picked up as standalone tasks.

Entries that carry an agreed fix plan have the owner's decisions already
made. A later session can implement straight from the "Fix sketch",
without re-asking what to do. Line numbers are approximate (the file has
moved since).

Remove entries from this file when the underlying bug is fixed.

The first entry below comes from an agent QA pass (2026-11-27). The two
after it came out of the review of the `is` walker rewrite (2026-11-28).


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


## `is` cannot reach a nullary function through a variable: a stored `zero` stays an atom

**Documented claim.** `docs/reference/language.md:1030-1031`: a variable
on the right of `is` evaluates "the same way the equivalent expression
written inline evaluates". `:1057-1059` records the exception this entry
is about.

**Test.**

    :- module(nullary, [z1/1, z2/1]).
    :- chr_constraint z1/1, z2/1.
    :- function zero/0.
    zero -> 42.
    z1(R) <=> R is zero.
    z2(R) <=> X = zero, R is X.

    ychr run --show-bindings -g 'nullary:z1(R)' nullary.chr
    ychr run --show-bindings -g 'nullary:z2(R)' nullary.chr

**Expected.** One answer for both, per the first claim.

**Actual.**

    R = 42            (z1)
    R = nullary:zero  (z2)

The `z2` run also warns `YCHR-20101` ("Undeclared data constructor
'zero'") on the `X = zero` line, because no type declares `zero`.

**Notes.** `z1` is a compiled call and never reaches the walker, so a
nullary function is only reached where it is written. `z2` stores the
function's vmName (`nullary__zero`, which is why it prints qualified) as
a value, and a zero-arity compound has no `VTerm` to walk: it collapses
to `VAtom` (`src/YCHR/Internal/Runtime/Types.hs:66-68`). Both walkers
dispatch `VTerm` only (`src/YCHR/Internal/Runtime/Interpreter.hs:1211`
`deepEvalValue`, `scheme/ychr/runtime.sls:334` `deep-eval-value`), so an
atom passes through untouched.

What makes this decidable: the stored atom carries the mangled functor,
the same shape `evaluables` (`Program.evaluables`) is keyed by, so an
atom can be looked up at arity 0 without mistaking ordinary data for a
call. The cost is that every atom the walk meets pays a table lookup,
and an atom that names a nullary function stops being printable data.

**Fix sketch.** Not decided. Either dispatch an atom whose text is an
`(functor, 0)` key in both walkers, or keep the behaviour and rely on
`:1057-1059` as the documented caveat.


## `is` on a cyclic term does not terminate

**Documented claim.** None: `docs/reference/language.md:1030-1060` does
not say what `is` does with a cyclic value. `resolveValue` documents the
same limitation for its own walk
(`src/YCHR/Internal/Runtime/Search.hs:656-658`: "Does not terminate on a
cyclic term (unification has no occurs check), like `copyTerm` and
`collectVars`").

**Test.**

    :- module(cyc, [go/1, type(pair/2)]).
    :- chr_type pair(A, B) ---> pair(A, B).
    :- chr_constraint go/1.
    go(R) <=> X = pair(X, 1), R is X.

    ychr run --show-bindings -g 'cyc:go(R)' cyc.chr

**Expected.** Termination — the value cannot be walked, and `resolveValue`
says so for its own walk.

**Actual.** The run never returns: no answer, no error, killed by hand
after 20 s. Nothing bounds the depth.

**Notes.** Unification has no occurs check, so `X = pair(X, 1)` builds a
one-cell cycle, and both walkers recurse into the argument values without
a visited set (`src/YCHR/Internal/Runtime/Interpreter.hs:1211`
`deepEvalValue`, `scheme/ychr/runtime.sls:334` `deep-eval-value`).

The rewrite that taught the walker to rebuild constructor terms made this
reachable for every cycle. Before it, a cycle under an evaluable functor
hung too, but a constructor-headed one failed immediately with
`is: functor is not evaluable`, so the cheapest cycles — the ones with a
constructor at the top — used to be errors.

**Fix sketch.** Not decided. Either detect the cycle during the walk (a
visited set keyed by variable or term identity, or a depth cap that
raises the runtime's general error), or document the limitation in the
`is` section as `resolveValue` does in its own comment.
