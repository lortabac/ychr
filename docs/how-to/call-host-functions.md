# How to call host-language functions

> **Goal:** invoke a host primitive from a YCHR program and wrap it in a
> typed CHR function.

This page is a stub.

## The `host:` namespace

> **TODO:** explain that `host:f(args)` calls a function provided by the
> backend's runtime, that arguments and return are untyped (`any` from
> the type checker's perspective), and that arithmetic operators in the
> prelude are thin wrappers over `host:` primitives.

```prolog
X + Y -> host:'+'(X, Y).
```

## Wrapping a host call with a typed signature

> **TODO:** show how a `:- function` declaration narrows the types at
> the wrapper boundary even though the underlying `host:` call is
> untyped.

## Available host primitives

> **TODO:** list of primitives provided by the Haskell runtime
> (arithmetic, comparisons, type predicates, term meta, I/O, `'$call'`).
> Until written, see `libraries/prelude.chr` and `src/YCHR/Runtime/`.

## See also

- [Prelude reference](../reference/prelude.md).
