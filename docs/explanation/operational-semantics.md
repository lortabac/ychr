# The Refined Operational Semantics

> **Audience:** readers who want to understand precisely *when* a rule
> fires and in what order.

This page is a stub.

## Why "refined"?

The theoretical operational semantics of CHR is non-deterministic in
several ways. Real implementations need to commit to a deterministic
firing order so that programs behave predictably. The **refined
operational semantics** (ωr) introduced by Duck, Stuckey, García de la
Banda, and Holzbaur (ICLP 2004) is the standard such commitment, and is
the semantics YCHR implements.

## Core ideas (preview)

> **TODO:** flesh out:
>
> 1. The *active constraint* — at any moment one constraint is being
>    actively scheduled against the rules.
> 2. **Occurrence order** — top-to-bottom, right-to-left within heads;
>    occurrences within a rule are tried in this order.
> 3. **Removed before kept** — within the same rule, removed occurrences
>    are tried before kept occurrences.
> 4. **Propagation history** — prevents the same propagation rule from
>    firing twice on the same combination of constraints.
> 5. **Reactivation** — when a variable bound by `=` affects a stored
>    constraint, that constraint becomes the active constraint again.
>    YCHR uses *selective* reactivation (observer-based).

## Termination, confluence

> **TODO:** brief, conceptual notes on what termination and confluence
> mean for CHR and pointers to deeper material.

## Seeing ωr in action

The REPL's `:trace GOAL` command runs a goal with the interpreter's
tracer enabled, printing one indented line per ωr event (and per
function / host-call entry). It is the easiest way to see exactly how
a rule fires, which constraints become active, when partner
constraints are picked up, and when reactivation kicks in. See
[`:trace`](../reference/repl.md#trace) in the REPL reference for the
full event list.

## See also

- Reference paper: `dev-docs/chr-for-imperative-host-languages.pdf`.
- Tutorial: [CHR primer](../tutorials/02-chr-primer.md).
- Reference: [VM specification](../reference/vm.md) — concrete
  realization of these semantics in YCHR's abstract VM.
- Reference: [REPL `:trace`](../reference/repl.md#trace) — interactive
  exploration of ωr step by step.
