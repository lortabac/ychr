# Passive Occurrences

> **Audience:** contributors working on the CHR-to-VM compiler, and
> readers wondering why a compiled program has fewer occurrence
> procedures than the rules suggest.
> **You will:** find which occurrences the compiler elides, how it sees
> through Head Normal Form to prove them redundant, and why that is
> sound.
> **Skip if:** you are writing CHR rather than compiling it — the
> optimization changes nothing you can observe from a program.

This document specifies the *passive occurrences* optimization performed
by the CHR-to-VM compiler. It is a static analysis over the numbered
occurrences of a desugared program: occurrences that provably can never
fire are marked *passive*, and the compiler then elides their occurrence
procedure and the call to it from the constraint's `activate` procedure.

The optimization is described in Van Weert, Wuille, Schrijvers &
Demoen, *CHR for Imperative Host Languages*, §5.3 ("Passive Occurrences").


## Background: occurrences and activation

For each constraint the compiler emits one `activate_c` procedure that,
when a constraint of type `c` becomes active, tries every *occurrence* of
`c` in turn (paper §5.2). An occurrence is one appearance of `c` in a rule
head; occurrence numbering follows the refined operational semantics ωr:
within a rule, removed heads are tried before kept heads, right-to-left,
and numbering runs top-down across the whole program (see
`YCHR.Internal.Compile.Occurrences`).

Trying an occurrence means searching the constraint store for partner
constraints, checking guards, and — if everything matches — firing the
rule. When it can be shown *statically* that a given occurrence can never
lead to a firing with the active constraint in that role, the whole
search is dead code.


## Definition

An occurrence is *passive* if it can be derived that the rule can never
fire with the active constraint matching that occurrence. A passive
occurrence contributes no `occurrence_c_j` procedure and no call from
`activate_c`; it is otherwise still *numbered* exactly as ωr requires, so
the numbers of the remaining (active) occurrences are unchanged.

The analysis is conservative: it marks an occurrence passive only when
soundness is guaranteed. Failing to mark a genuinely-passive occurrence
costs a missed optimization; wrongly marking a live occurrence would drop
firings and change program behavior. The guiding principle is therefore
*correctness over completeness* — every predicate below is a sufficient,
not a necessary, condition for passivity.


## v1 sources of passivity

The analysis runs *after* occurrence numbering and *after* Head Normal
Form (HNF), so it sees head arguments already normalized to distinct
variables with the induced equalities materialized as guards. v1 detects
the *subsumption / symmetry* source. The paper's *never-stored* source
is deferred — as explained in [Deferred](#deferred--future-work), its only
storage-independent criterion is vacuous until Late Storage exists.

### Subsumption / symmetry

> An occurrence subsumed by an earlier *removed* occurrence is passive.

Because ωr tries removed occurrences first (and right-to-left), when two
occurrences of a rule match the same set of constraint tuples, the
earlier-numbered one always fires first and the later one is redundant.
v1 recognizes two exact rule shapes:

**Idempotence** — a simpagation whose kept and removed heads are the same
constraint with structurally identical arguments:

```
idempotence @ leq(X, Y) \ leq(X, Y) <=> true.
```

The kept occurrence is subsumed by the removed one and is made passive.

**Symmetric two-head simplification** — a simplification whose two removed
heads are the same constraint, related by swapping their argument
positions:

```
antisymmetry @ leq(X, Y), leq(Y, X) <=> X = Y.
```

The two occurrences match the same unordered pair of stored constraints,
differing only in which matched constraint is labelled "active". One
occurrence is therefore redundant; the higher-numbered one is made
passive. (The body need not be symmetric — see [Soundness](#soundness) for
why the ωr-earlier occurrence always preempts the later one.)


## Seeing through HNF (canonicalization)

Raw head comparison is not enough. After HNF the removed head of the
idempotence rule is rewritten so that the two heads no longer share
syntactic variables — for example `leq(X, Y) \ leq(X, Y)` becomes, in
effect, `leq(X, Y) \ leq(H0, H1)` with induced guards `X = H0, Y = H1`.
The subsumption analysis must undo this before comparing heads.

For each rule the analysis:

1. Builds an equivalence relation on head variables from the induced
   equality guards — every guard that equates two head variables merges
   their classes (union-find).
2. Sets aside all *residual* guards: any guard that is not a head-variable
   equality (user guards such as `X < Y`, structural match guards, or
   equalities touching a non-head variable).
3. Defines `canonHead` of a head constraint as its constraint type paired
   with the list of class representatives of its arguments (each wildcard
   becomes a fresh singleton class).

Idempotence is then "kept and removed heads have equal `canonHead` and no
residual guards"; symmetry is "the two removed heads' `canonHead`s are
invariant under swapping the heads, and no residual guards". The
residual-guard condition is what makes the analysis reject asymmetric
variants such as

```
leq(X, Y), leq(Y, X) <=> X < Y | ...
```

whose `X < Y` guard is *not* symmetric under the swap, so neither
occurrence is passive.

For v1 the residual-guard requirement is the strict form "no residual
guards at all". This is sufficient for the idempotence and antisymmetry
patterns (both have only head-variable equalities) and is trivially sound.


## Worked example: `leq`

```
:- chr_constraint leq/2.
reflexivity  @ leq(X, X) <=> true.
antisymmetry @ leq(X, Y), leq(Y, X) <=> X = Y.
idempotence  @ leq(X, Y) \ leq(X, Y) <=> true.
transitivity @ leq(X, Y), leq(Y, Z) ==> leq(X, Z).
```

`leq/2` has seven occurrences after ωr numbering:

| # | rule         | active head        | status                       |
|---|--------------|--------------------|------------------------------|
| 1 | reflexivity  | `leq(X, X)`        | active (has HNF `X = H` guard)|
| 2 | antisymmetry | right `leq(Y, X)`  | active                       |
| 3 | antisymmetry | left `leq(X, Y)`   | **passive (symmetry)**       |
| 4 | idempotence  | removed head       | active                       |
| 5 | idempotence  | kept head          | **passive (subsumption)**    |
| 6 | transitivity | left `leq(X, Y)`   | active                       |
| 7 | transitivity | right `leq(Y, Z)`  | active                       |

Note that `leq` itself is *not* never-stored: reflexivity is a
single-headed simplification, but after HNF `leq(X, X)` carries the guard
`X = H`, so it is not *guardless*; and antisymmetry/idempotence/transitivity
are multi-headed. Occurrences 3 and 5 are elided; the compiler emits five
occurrence procedures for `leq/2` instead of seven, and `activate_order__leq2`
chains five calls instead of seven.


## Soundness

- **Numbering stability.** Passivity is computed after numbering, so
  passive occurrences keep their ωr numbers; only their procedure and
  their `activate` call disappear. No part of the compiler references
  another occurrence's number (the propagation history is keyed on head
  *positions*, not occurrence numbers), so eliding is local.
- **Preemption.** For both families, soundness follows from ωr
  try-order plus early drop, *not* from the body being symmetric: the
  surviving occurrence is a removed head with the lower occurrence
  number, so `activate` tries it first, and whenever the passive
  occurrence could match a partner, the survivor matches the *same*
  partner — firing it removes the active constraint before the passive
  occurrence is ever reached (see
  [Relationship to early drop](#relationship-to-early-drop) for the
  full argument). In the symmetry case the two occurrences fire with
  *swapped* variable bindings (`{X=a, Y=b}` versus `{X=b, Y=a}`),
  which is why the body need not be symmetric: the survivor always
  wins the race, so its binding is the one that would have been
  produced anyway.
- **Propagation history & reactivation** are unaffected: a passive
  occurrence never fires, so it never records history and is never a
  reactivation or backjump target; the surviving occurrences fire the same
  rule instances with the same head-position-keyed history tuples.

### Relationship to early drop

The subsumption/symmetry passivity above is not independent of the rest of
the compilation scheme: its soundness *relies on early drop* (paper §5.3,
Listing 8). Two ωr facts combine to make the passive occurrence
unreachable:

1. ωr tries *removed occurrences before kept ones* (and right-to-left),
   so the surviving occurrence always has the lower occurrence number and
   `activate` reaches it first.
2. Once the active constraint is *removed from the store, its remaining
   occurrences are not tried*. This is exactly what early drop implements:
   an occurrence procedure returns `true` when the active constraint was
   killed, and `activate` stops chaining as soon as an occurrence returns
   `true`.

Fact 2 is what "the passive occurrence is unreachable" ultimately rests
on. If the activation loop kept trying occurrences *after* the active
constraint had been removed, the would-be-passive occurrence would not
merely be redundant — it could actively corrupt the store. For idempotence
`c(X, Y) \ c(X, Y) <=> true` with two copies `C1`, `C2` and `C1` active,
the removed occurrence fires and kills `C1`, correctly leaving `C2`.
Without early drop the kept (would-be-passive) occurrence would then run,
find the still-live `C2`, and fire — killing `C2` too, leaving *zero*
copies. So the occurrence is passive *only because* early drop keeps it
from being reached.

Equivalently: early drop is the faithful implementation of the ωr property
that a removed active constraint is no longer active, so "requires early
drop" reduces to "requires an ωr-conformant activation loop", which this
compiler provides. Note this coupling is specific to the
subsumption/symmetry family (subsumed by an earlier *removed* occurrence);
the deferred [never-stored](#deferred--future-work) source is orthogonal —
it makes an occurrence passive because the partner's `Foreach` is provably
empty, which holds regardless of early drop.


## Deferred / future work

The following are intentionally out of scope for v1:

- **Never-stored analysis.** An occurrence whose partner is a constraint
  that is never stored can never fire (its `Foreach` is always empty).
  However, the only *storage-independent* criterion for "never stored" — a
  constraint all of whose head occurrences are single-headed guardless
  simplification rules — is vacuous for partner elimination without Late
  Storage: to be a partner of an occurrence, a constraint must appear in
  a multi-headed rule head, which immediately disqualifies it from that
  criterion. The paper's useful never-stored analysis instead derives
  "never stored" from a *Late Storage* pass (a constraint removed before
  it is ever committed to the store, even though it appears in multi-headed
  rules). This source is therefore deferred until Late Storage is
  implemented.
- **General subsumption / guard simplification.** Full subsumption
  analysis compares arbitrary occurrences modulo guards and partner
  constraints, and benefits from guard simplification (replacing redundant
  guard conjuncts with `true`). v1 recognizes only the two exact rule
  shapes above.
- **Index-structure elimination.** Once a constraint's occurrences are all
  passive (or it is never stored), the runtime need not build indexes for
  it. v1 changes only which procedures are emitted, not runtime store
  layout.
