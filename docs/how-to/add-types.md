# How to add types to a YCHR program

> **Goal:** annotate constraints and functions, declare algebraic types,
> and run the type checker.

This page is a stub.

## Run the type checker

```sh
ychr check file.chr
```

The checker is gradual: programs without annotations pass without errors.

## Annotate a constraint

> **TODO:** before/after example for `:- chr_constraint leq/2.` →
> `:- chr_constraint leq(int, int).`

## Annotate a function

> **TODO:** single-signature, then overloaded.

## Define an algebraic type

> **TODO:** `:- chr_type option(A) ---> none ; some(A).` and a use site.

## Reading error messages

> **TODO:** show a representative inconsistency error and how to read it.

## See also

- [Type-system specification](../reference/type-system.md).
- Tutorial: [Functions, types, and lambdas](../tutorials/04-functions-and-types.md).
