# YCHR Language Reference

YCHR accepts standard CHR with Prolog-compatible syntax: constraint
declarations, simplification rules (`<=>`), propagation rules (`==>`),
simpagation rules (`\`), guards, and rule bodies. This document
describes the ways YCHR diverges from the K.U.Leuven CHR-in-Prolog
dialect.

## Modules

Every program is organized into modules. A module declares its name and
its export list, and may import other modules:

```
:- module(order, [leq/2]).
:- use_module(library(lists)).
:- chr_constraint leq/2.

reflexivity   @ leq(X, X) <=> true.
antisymmetry  @ leq(X, Y), leq(Y, X) <=> X = Y.
idempotence   @ leq(X, Y) \ leq(X, Y) <=> true.
transitivity  @ leq(X, Y), leq(Y, Z) ==> leq(X, Z).
```

A module may also be declared without an export list:

```
:- module(order).
```

This form exports every constraint, function, type, and operator
declared in the module.

Constraint and function names are qualified with their defining module;
unqualified references in source are resolved against the module's
imports.

## Functions

When CHR is embedded in Prolog, guards rely on predicate success or
failure. In YCHR, guards are functional expressions that return a
boolean. They can call host-language procedures or user-defined
*functions*.

Functions are declared with `:- function` and defined with Erlang-style
equations using `->`, evaluated top-to-bottom by pattern matching:

```
:- function member/2.

member(_, [])     -> false.
member(X, [X|_])  -> true.
member(X, [_|Xs]) -> member(X, Xs).
```

Guard clauses on equations are written with `|`:

```
:- function factorial/1.

factorial(0)              -> 1.
factorial(N) | N > 0      -> N * factorial(N - 1).
```

Functions are callable in guards, on the right-hand side of `is`, and
in rule body position (where the result is discarded). If no equation
matches, a runtime error is raised.

## The `is` operator

`is` is generalized to accept any expression on the RHS, including
calls to user-defined functions and host-language functions.

```
ychr> R is member(1, [0, 1, 2]).
R = true.
```

## Lambdas and function references

Anonymous functions use Erlang-style syntax with `end` delimiting the
body, so lambdas can appear inside compound-term arguments without
extra parentheses:

```
:- function apply/2.
apply(F, X) -> '$call'(F, X).

result(R) <=> R is apply(fun(X) -> X + 1 end, 5).
```

Lambdas are first-class values: they can be passed as arguments,
returned from functions, and called with `'$call'`. They capture free
variables from the enclosing scope, so a function returning a lambda
retains the captured values:

```
:- function make_adder/1.
make_adder(N) -> fun(X) -> X + N end.
```

Named functions are referenced by `fun name/arity` (e.g. `fun member/2`)
and called via `'$call'`.

## Optional static type checking

Programs may annotate constraints and functions with type signatures.
The type checker is gradual: programs without annotations are accepted
unchanged. See [type-system.md](type-system.md) for the full
specification.
