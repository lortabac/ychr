# Functions, Types, and Lambdas

Rule bodies often need to *compute*. User-defined functions are
pattern-matched equations, tried top-to-bottom, callable from guards,
from the right-hand side of `is`, and in body position.

## 1. A first function: factorial

[`examples/factorial.chr`](../../examples/factorial.chr):

```prolog
:- module(factorial, [compute/2, fun factorial/1]).
:- chr_constraint compute(int, int).
:- function factorial(int) -> int.

factorial(0)         -> 1.
factorial(N) | N > 0 -> N * factorial(N - 1).

compute(N, R) <=> R is factorial(N).
```

- `:- module(factorial, [compute/2, fun factorial/1]).` — functions
  are exported as `fun name/arity`, constraints as `name/arity`.
  Unexported names are invisible outside the module, REPL goals
  included.
- `:- function factorial(int) -> int.` declares the function with its
  type; `:- function factorial/1.` would leave everything at `any`
  (§2). Function and constraint names share a namespace and may not
  collide.
- `:- chr_constraint compute(int, int).` types the constraint's
  arguments.
- The `factorial(...) -> ...` lines are *equations*, tried
  top-to-bottom. `| N > 0` is a guard, the same `|` as in rules.
- `R is factorial(N)` evaluates the right-hand side and unifies the
  result with `R`.

```sh
ychr repl examples/factorial.chr
```

```ychr-repl
ychr> R is factorial(5).
R = 120.
ychr> R is factorial(10).
R = 3628800.
ychr>
```

`is` works at the REPL top level, so `compute/2` is not needed there.
It exists because `ychr run -g` only accepts a single declared
constraint as its goal, so calling a function from the CLI needs a
constraint wrapper:

```sh
ychr run -g 'compute(5, R)' --show-bindings examples/factorial.chr
```

```
R = 120
```

[`examples/fib.chr`](../../examples/fib.chr) has two base-case
equations and a guarded recursive one.

## 2. Adding types

Types are optional. `:- chr_constraint compute/2.` and
`:- function factorial/1.` run the same as the annotated forms above
but leave every argument and result at `any`, which the checker never
rejects. Annotate, and the checker polices the shape.

### Running the checker

```sh
ychr check examples/factorial.chr
```

No output, exit status 0: well-typed.

### Catching a mismatch

Change the rule body to call `factorial` with a string:

```prolog
compute(N, R) <=> R is factorial("hello").
```

```sh
ychr check examples/factorial.chr
```

```
=== error ===
examples/factorial.chr:16:19: YCHR-60001
Type mismatch: 'string' does not match 'int'
R is factorial("hello")
```

Revert before continuing.

### Algebraic types

[`examples/traffic.chr`](../../examples/traffic.chr):

```prolog
:- module(traffic, [intensity_of/2, type(color/0, [red, green, yellow])]).
:- chr_type color ---> red ; green ; yellow.
:- chr_constraint intensity_of(color, int).
:- function intensity(color) -> int.

intensity(red)    -> 100.
intensity(yellow) -> 60.
intensity(green)  -> 20.

intensity_of(C, R) <=> R is intensity(C).
```

`:- chr_type color ---> red ; green ; yellow.` is a sum type with three
nullary constructors. The export form
`type(color/0, [red, green, yellow])` exports the type with its
constructors; without it they stay private to the module.

```sh
ychr repl examples/traffic.chr
```

```ychr-repl
ychr> intensity_of(red, R).
R = 100.
ychr> intensity_of(green, R).
R = 20.
ychr> intensity_of(yellow, R).
R = 60.
ychr>
```

Polymorphism, overloading, `any`, narrowed constructor imports: [type
system reference](../reference/type-system.md).

## 3. Lambdas and function references

Functions are values. [`examples/closures.chr`](../../examples/closures.chr)
shows the three forms a callable can take:

```prolog
:- module(callables,
          [by_ref/1, lambda/1, closure/1,
           fun double/1, fun make_adder/1]).
:- chr_constraint by_ref/1, lambda/1, closure/1.
:- function double/1.
:- function make_adder/1.

double(X) -> X + X.

make_adder(N) -> fun(X) -> X + N end.

by_ref(R)  <=> R is call(fun double/1, 21).
lambda(R)  <=> R is call(fun(X) -> X * X end, 7).
closure(R) <=> Add10 is make_adder(10), R is call(Add10, 5).
```

- `fun name/arity` — a reference to a top-level function.
- `fun(X) -> Body end` — an anonymous function. `end` delimits the
  body, so a lambda can sit inside an argument list without extra
  parentheses.
- `call(F, X)` — apply a callable (reference, lambda, or closure). The
  prelude's typed `call/N` family covers `call/2` through `call/11`
  (unary through ten-argument application); the wired-in
  `'$call'(F, A1, …, An)` is the untyped primitive underneath.

```sh
ychr run -g 'by_ref(R)' --show-bindings examples/closures.chr
```

```
R = 42
```

```sh
ychr run -g 'lambda(R)' --show-bindings examples/closures.chr
```

```
R = 49
```

```sh
ychr run -g 'closure(R)' --show-bindings examples/closures.chr
```

```
R = 15
```

`make_adder(10)` returns a closure with `N` captured as `10`. Each call
to `make_adder` makes an independent closure.

## 4. Where to go next

- [Type system reference](../reference/type-system.md) — annotations,
  polymorphism, overload resolution.
- [`libraries/prelude.chr`](../../libraries/prelude.chr) — the built-in
  functions and operators.
