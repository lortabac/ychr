# Functions, Types, and Lambdas

> **Audience:** readers who finished
> [Your first YCHR program](03-your-first-program.md).
> **You will:** add user-defined functions, type annotations, and lambdas
> to a YCHR program.

This page is a stub. The eventual flow:

## User-defined functions

> **TODO:** introduce `:- function name/arity` plus Erlang-style equations
> with `->`, guards on equations with `|`, the role of pattern matching,
> and where functions can be called (guards, `is` RHS, body).

```prolog
:- function factorial/1.

factorial(0)         -> 1.
factorial(N) | N > 0 -> N * factorial(N - 1).
```

## Adding types

> **TODO:** show how to annotate constraints and functions, define an
> algebraic type with `:- chr_type`, and read the resulting checker
> messages. Cross-link to [type-system.md](../reference/type-system.md)
> for the full spec.

## Lambdas and `'$call'`

> **TODO:** Erlang-style `fun(X) -> Expr end` syntax, closures, function
> references via `fun name/arity`, and the `call/N` wrapper.

## Where to go next

- How-to: [add types to an existing program](../how-to/add-types.md).
- How-to: [organize code into modules](../how-to/organize-modules.md).
- Reference: [prelude / standard library](../reference/prelude.md).
