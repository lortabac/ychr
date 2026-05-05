# Design Rationale

> **Audience:** readers curious about why YCHR is shaped the way it is.

This page is a stub.

## A small abstract VM

> **TODO:** explain why YCHR compiles through an abstract VM rather than
> directly to each target language: it isolates backend implementors
> from the surface language, lets the compiler stay simple, and makes
> the runtime contract explicit.

## Erlang-style functions instead of Prolog goals for guards

> **TODO:** rationale for adopting functional, returning-a-boolean
> guards over Prolog's success/failure model.

## Gradual types

> **TODO:** why gradual rather than fully static, why consistency-based
> rather than subtyping, and the relationship to Siek & Taha's gradual
> typing.

## Selective reactivation

> **TODO:** why YCHR implements observer-based selective reactivation
> instead of the blanket `reactivate_all` pattern from the paper.

## See also

- [VM specification](../reference/vm.md) — the concrete VM design.
- [Type-system specification](../reference/type-system.md).
- Contributor doc: `dev-docs/PROJECT.md` — broader architectural notes.
