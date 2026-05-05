# Prelude Reference

> **Audience:** anyone calling library functions or using arithmetic
> and comparison operators.
> **You will:** learn how the prelude is structured, then look up the
> signature of each export.

The prelude is a small CHR module ([`libraries/prelude.chr`](../../libraries/prelude.chr))
that ships with YCHR. It defines arithmetic and comparison operators,
type-predicate functions, term-introspection helpers, and a handful of
I/O constraints.

## How the prelude is structured

The prelude is **implicitly imported** in every program: you do not
need `:- use_module(library(prelude))`. Its identifiers are visible
without qualification — `+` resolves to `prelude:'+'`, `integer/1` to
`prelude:integer/1`, and so on.

Two patterns are worth understanding before reading the tables:

- **Operator overloading by signature.** Arithmetic and comparison
  operators are declared with one signature per concrete combination
  of types, e.g.
  ```
  :- function
      ('+'(int, int) -> int),
      ('+'(float, float) -> float).
  ```
  The implementation is a single equation that delegates to a host
  call. The type checker picks the matching signature based on the
  types of the actual arguments. See
  [type-system.md](type-system.md) for the resolution rules.

- **Functions are evaluated, constraints are stored.** Most prelude
  exports are *functions* (declared with `:- function`) and are
  callable in guards and on the right of `is`. A few exports —
  `write/1`, `nl/0`, `writeln/1` — are *constraints* (declared with
  `:- chr_constraint`) that perform I/O when added to the store.

A small precedence note: `is/2` binds tighter than the comparison
operators, so `B is 1 < 2` is a parse error. Use `B is (1 < 2)`.

## Arithmetic

Operators on numbers. Each is overloaded for `int` and `float`.

| Identifier | Signature(s) | Notes |
|------------|--------------|-------|
| `+` | `(int, int) -> int`, `(float, float) -> float` | Addition. |
| `-` | `(int, int) -> int`, `(float, float) -> float` | Subtraction. |
| `*` | `(int, int) -> int`, `(float, float) -> float` | Multiplication. |
| `/` | `(float, float) -> float` | Float division. For integer division, use `div`. |
| `div` | `(int, int) -> int` | Integer division. |
| `mod` | `(int, int) -> int` | Integer modulo. |
| `rem` | `_/2` | Remainder; signatures default to `any`. |

Operator precedence and associativity (declared via `op/3`):

| Priority | Type | Operators |
|----------|------|-----------|
| 400 | `yfx` | `*`, `/`, `div`, `mod`, `rem` |
| 500 | `yfx` | `+`, `-` |

```ychr-repl
ychr> X is 2 + 3.
X = 5.
ychr> Y is 2.0 + 3.5.
Y = 5.5.
```

## Comparisons and equality

Each comparison is overloaded for `int` and `float` and returns `bool`.

| Identifier | Signature(s) |
|------------|--------------|
| `<` | `(int, int) -> bool`, `(float, float) -> bool` |
| `>` | `(int, int) -> bool`, `(float, float) -> bool` |
| `>=` | `(int, int) -> bool`, `(float, float) -> bool` |
| `=<` | `(int, int) -> bool`, `(float, float) -> bool` |
| `==` | `(A, A) -> bool` | Polymorphic structural equality. |

All comparison operators have priority `700`, type `xfx`.

```ychr-repl
ychr> B is (1 < 2).
B = true.
ychr> B is (5 == 5).
B = true.
```

## Aggregators

| Identifier | Notes |
|------------|-------|
| `max/2` | Larger of two values (uses `>=`). |
| `min/2` | Smaller of two values (uses `=<`). |

```ychr-repl
ychr> Z is max(7, 4).
Z = 7.
```

## Type predicates

All type predicates take a value of type `any` and return `bool`.

| Identifier | Returns `true` when… |
|------------|-----------------------|
| `var/1` | The argument is an unbound logical variable. |
| `nonvar/1` | The argument is not an unbound variable. |
| `integer/1` | The argument is an `int` literal. |
| `float/1` | The argument is a `float` literal. |
| `atom/1` | The argument is an atom (symbolic constant). |
| `boolean/1` | The argument is `true` or `false`. |
| `string/1` | The argument is a string literal. |
| `ground/1` | The argument contains no unbound variables anywhere. |

```ychr-repl
ychr> B is var(X).
B = true,
X = _.
ychr> B is ground(foo(1, 2)).
B = true.
```

## Numeric conversion

| Identifier | Signature |
|------------|-----------|
| `int_to_float/1` | `(int) -> float` |
| `float_to_int/1` | `(float) -> int` |

## Term introspection

| Identifier | Signature | Notes |
|------------|-----------|-------|
| `unifiable/2` | `(any, any) -> bool` | True if the two terms could unify. No mutation. |
| `term_variables/1` | `_/1` | Returns the list of unbound variables in a term. |
| `compound_to_list/1` | `(any) -> list(any)` | Converts a compound term into a `[Functor, Arg1, …]` list. |
| `list_to_compound/1` | `(list(any)) -> any` | Inverse of `compound_to_list/1`. |
| `copy_term/1` | `(A) -> A` | Fresh copy of a term with fresh variables. |

```ychr-repl
ychr> Vs is term_variables(foo(X, bar(Y, X))).
Vs = [_, _],
X = _,
Y = _.
```

## First-class function call

| Identifier | Signature |
|------------|-----------|
| `call/2` | `(fun(A) -> B end, A) -> B` |
| `call/3` | `(fun(A, B) -> C end, A, B) -> C` |

`call/N` is a typed wrapper over the host primitive `'$call'`. Use it
to invoke first-class function values (lambdas, function references).

## I/O constraints

These are constraints, not functions — added to the store with `,` in
a body or directly at the prompt:

| Identifier | Effect |
|------------|--------|
| `write/1` | Print the argument with no trailing newline. |
| `nl/0` | Print a newline. |
| `writeln/1` | Print the argument followed by a newline. |

## Other libraries

The bundled libraries `lists`, `strings`, `meta`, and `test` ship
alongside the prelude under [`libraries/`](../../libraries/). Their
contents are not yet documented here — read the source for now:

- [`libraries/lists.chr`](../../libraries/lists.chr) — list operations.
- [`libraries/strings.chr`](../../libraries/strings.chr) — string operations.
- [`libraries/meta.chr`](../../libraries/meta.chr) — `print_store/0`,
  `print/1`, `read_term_from_string/1`, `write_term_to_string/1`,
  `write_store_to_list/0`.
- [`libraries/test.chr`](../../libraries/test.chr) — test helpers.

Unlike the prelude, these are **not** auto-loaded outside the REPL —
inside the REPL all of them are available; in compiled programs use
`:- use_module(library(name)).` to import explicitly.

## See also

- [Language reference](language.md).
- [Type system](type-system.md) — how the overloaded signatures are
  resolved.
- [How-to: call host functions](../how-to/call-host-functions.md).
