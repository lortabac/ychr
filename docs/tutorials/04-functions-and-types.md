# Functions, Types, and Lambdas

> **Audience:** readers who finished
> [Your first YCHR program](03-your-first-program.md) and want
> deterministic computation, optional type checking, and first-class
> functions.
> **You will:** write user-defined functions, add type annotations and
> watch `ychr check` catch a mismatch, and pass lambdas and function
> references around as values.

CHR is relational: the constraint store rewrites itself by matching
heads. Once a rule fires, though, the body often wants to *compute*
something — multiply, look up, format a string. That's what
**user-defined functions** are for. Functions are deterministic,
pattern-matched, top-to-bottom equations callable from guards, from
the right-hand side of `is`, and from rule body position.

## 1. A first function: factorial

Pattern-matching, top-to-bottom, with a guard on the second equation.
The companion file is
[`examples/factorial.chr`](../../examples/factorial.chr):

```chr
:- module(factorial, [compute/2, fun factorial/1]).
:- use_module(prelude).
:- chr_constraint compute(int, int).
:- function factorial(int) -> int.

factorial(0)         -> 1.
factorial(N) | N > 0 -> N * factorial(N - 1).

compute(N, R) <=> R is factorial(N).
```

Five pieces of language to point out.

- `:- module(factorial, [compute/2, fun factorial/1]).` declares the
  module and its exports. Functions are exported with the `fun
  name/arity` form; constraints are exported as plain `name/arity`.
  Names that aren't exported cannot be referenced from outside the
  module — including from a REPL goal.
- `:- function factorial(int) -> int.` declares the function and its
  type. The name and arity live in the same namespace as constraint
  names, but the two cannot collide. The argument and return types
  here are explicit; if you write `:- function factorial/1.` instead,
  both default to `any` and skip type-checking. §3 covers types in
  more depth.
- `:- chr_constraint compute(int, int).` similarly types the
  constraint's two arguments.
- The two `factorial(...) -> ...` lines are **equations**. They are
  tried top-to-bottom. The first one matches only when the argument is
  literally `0`. The second one matches any `N` and uses a **guard**
  (`| N > 0`) to exclude negatives. Equation guards use the same `|`
  operator as rule guards.
- `compute(N, R) <=> R is factorial(N).` is an ordinary CHR rule. The
  body uses `is` — the same operator Prolog uses to evaluate
  arithmetic — to compute the right-hand side and unify the result with
  the left-hand side.

Load the file in the REPL and call the function directly:

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

The `compute/2` constraint in the file isn't needed in the REPL — `is`
works at the top level. It's there because `ychr run -g` only accepts a
single constraint as its goal, so calling a function from the CLI
requires a constraint wrapper:

```sh
ychr run -g 'compute(5, R)' --show-bindings examples/factorial.chr
```

```
R = 120
```

## 2. A function inside a rule body: fibonacci

The same pattern scales naturally to recursion across multiple
equations. The companion file
[`examples/fib.chr`](../../examples/fib.chr):

```chr
:- module(fib, [compute/2, fun fib/1]).
:- use_module(prelude).
:- chr_constraint compute(int, int).
:- function fib(int) -> int.

fib(0) -> 0.
fib(1) -> 1.
fib(N) | N > 1 -> fib(N - 1) + fib(N - 2).

compute(N, R) <=> R is fib(N).
```

```sh
ychr repl examples/fib.chr
```

```ychr-repl
ychr> R is fib(10).
R = 55.
ychr> R is fib(15).
R = 610.
ychr>
```

Two pattern-matching equations supply the base cases; the third covers
the recursive case under a guard. There is nothing CHR-specific here —
it's exactly the recursion you'd write in any pattern-matching
language. The `compute/2` constraint plays the same role as in §1: a
CLI-friendly wrapper for `ychr run -g`.

## 3. Adding types

YCHR has an *optional* gradual type system. Every declaration can be
written in a plain form (no types) or an annotated form (with types);
the checker enforces consistency only on the annotated parts. The
factorial program in §1 used the annotated form throughout:

```chr
:- chr_constraint compute(int, int).
:- function factorial(int) -> int.
```

The plain forms `:- chr_constraint compute/2.` and
`:- function factorial/1.` mean the same thing operationally, except
they leave every argument and return at the catch-all type `any` —
the checker accepts anything for them. Annotating commits you to a
shape that the checker will police.

### Running the checker

```sh
ychr check examples/factorial.chr
```

No output, exit status 0 — the program is well-typed.

### Catching a mismatch

To see the checker work, break it on purpose. Edit
`examples/factorial.chr` so the body calls `factorial` with a string
instead of `N`:

```chr
compute(N, R) <=> R is factorial("hello").
```

Now rerun the checker:

```sh
ychr check examples/factorial.chr
```

```
=== error ===
examples/factorial.chr:17:19: YCHR-60001
Type mismatch: 'typechecker:string' does not match 'typechecker:int'
R is factorial("hello")
```

The checker rejects the program and points at the offending call.
Revert the change before continuing.

### Algebraic types

You can also define your own types with a list of constructors. The
companion file [`examples/traffic.chr`](../../examples/traffic.chr)
defines a three-valued `color` and a function over it:

```chr
:- module(traffic, [intensity_of/2, type(color/0, [red, green, yellow])]).
:- chr_type color ---> red ; green ; yellow.
:- chr_constraint intensity_of(color, int).
:- function intensity(color) -> int.

intensity(red)    -> 100.
intensity(yellow) -> 60.
intensity(green)  -> 20.

intensity_of(C, R) <=> R is intensity(C).
```

`:- chr_type color ---> red ; green ; yellow.` declares a sum type with
three nullary constructors. The function pattern-matches on them.

The export form `type(color/0, [red, green, yellow])` exports the
`color` type along with all three constructors — without this, the
constructors stay private to the declaring module. Load the file in
the REPL and call the constraint with bare constructor names:

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

The full rules — polymorphism, overloading, gradual interaction with
`any`, narrowing constructor imports — are in the
[type system reference](../reference/type-system.md).

## 4. Lambdas and function references

Functions are also values. You can pass them around, return them, and
call them indirectly. The companion file
[`examples/closures.chr`](../../examples/closures.chr) shows the three
forms a callable value can take:

```chr
:- module(callables,
          [by_ref/1, lambda/1, closure/1,
           fun double/1, fun make_adder/1]).
:- use_module(prelude).
:- chr_constraint by_ref/1, lambda/1, closure/1.
:- function double/1.
:- function make_adder/1.

double(X) -> X + X.

make_adder(N) -> fun(X) -> X + N end.

by_ref(R)  <=> R is call(fun double/1, 21).
lambda(R)  <=> R is call(fun(X) -> X * X end, 7).
closure(R) <=> Add10 is make_adder(10), R is call(Add10, 5).
```

Three pieces of syntax:

- **`fun name/arity`** — a reference to an existing top-level function.
  `fun double/1` is the value "the `double` function".
- **`fun(X) -> Body end`** — an anonymous function (Erlang-style). The
  `end` keyword delimits the body so lambdas can appear inside other
  expressions without needing extra parentheses.
- **`call(F, X)`** — apply a callable value (function reference,
  lambda, or closure) to an argument. It's a typed prelude function;
  `call(F, X, Y)` is the two-argument variant, and so on for higher
  arities.

The three example constraints each invoke `call` with a different kind
of callable:

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

The third case is the interesting one. `make_adder(10)` returns
`fun(X) -> X + N end` with `N` bound to `10` — a **closure** that
remembers its captured value. Calling that closure with `5` gives
`10 + 5 = 15`. Each call to `make_adder` produces an independent
closure with its own captured `N`.

## 5. Where to go next

- [Type system reference](../reference/type-system.md) — the full
  rules for type annotations, polymorphism, and overload resolution.
- [Prelude reference](../reference/prelude.md) — the built-in
  functions and constraints (`is`, arithmetic, comparisons, list
  primitives, `call/N`) that this tutorial drew on.
- [Language reference](../reference/language.md) — the precise spec
  for everything introduced in tutorials 01–04.
