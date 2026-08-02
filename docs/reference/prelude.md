# Prelude Reference

> **Audience:** anyone calling library functions or using arithmetic
> and comparison operators.
> **You will:** learn how the prelude is structured, then look up the
> signature of each export.

The prelude is a small CHR module ([`libraries/prelude.chr`](../../libraries/prelude.chr))
that ships with YCHR. It defines arithmetic and comparison operators,
type-predicate functions, term-introspection helpers, and a handful of
I/O functions.

## How the prelude is structured

The prelude is *implicitly imported* in every program: you do not
need `:- use_module(library(prelude))`. Its identifiers are visible
without qualification — `+` resolves to `prelude:'+'`, `integer/1` to
`prelude:integer/1`, and so on.

Two patterns run through the tables below:

- **Operator overloading by signature.** Operators that are genuinely
  overloaded across `int` and `float` — `+`, `-`, `*`, `<`, `>`, `>=`,
  `=<` — are declared as `:- class` with one signature per concrete
  combination of types, e.g.
  ```
  :- class
      ('+'(int, int) -> int),
      ('+'(float, float) -> float).
  ```
  The implementation is a single equation that delegates to a host
  call. The type checker picks the matching signature based on the
  types of the actual arguments. See
  [type-system.md](type-system.md) for the resolution rules.

  The remaining operators have only *one* signature each and so are
  ordinary `:- function`s, not classes: `/`, `div`, `mod`, and `rem`
  are each specific to one numeric type, and `==` is polymorphic
  (`(A, A) -> bool`). With a single signature there is nothing to
  resolve. The practical difference shows up in diagnostics: a type
  mismatch on a class operator reports `YCHR-60006` (no matching
  overload), while a mismatch on a single-signature function operator
  reports `YCHR-60001` (type mismatch).

- **Functions are evaluated, constraints are stored.** All prelude
  exports are *functions* or *classes* (declared with `:- function`
  / `:- class`) and are callable in guards, on the right of `is`,
  and in body / top-level position. I/O entries (`write/1`, `nl/0`,
  `writeln/1`) are functions too: they perform their side effect on
  evaluation and their unit return is discarded.

## Types

Besides functions and classes, the prelude exports two algebraic
types:

| Type | Declaration | Notes |
|------|-------------|-------|
| `bool` | `:- chr_type bool ---> true ; false.` | The boolean type. Not built into the type system — see [type-system.md](type-system.md#built-in-types). |
| `list(T)` | `:- chr_type list(T) ---> [] ; [T\|list(T)].` | Prolog-style lists; `[a, b]` sugar produces this type. |

## Arithmetic

Operators on numbers. Each is overloaded for `int` and `float`. `int`
arithmetic is arbitrary-precision and never overflows; `float`
arithmetic uses the host's IEEE-754 doubles.

| Identifier | Signature(s) | Notes |
|------------|--------------|-------|
| `+` | `(int, int) -> int`, `(float, float) -> float` | Addition. |
| `-` | `(int, int) -> int`, `(float, float) -> float` | Subtraction. |
| `*` | `(int, int) -> int`, `(float, float) -> float` | Multiplication. |
| `/` | `(float, float) -> float` | Float division. For integer division, use `div`. |
| `div` | `(int, int) -> int` | Integer division. |
| `mod` | `(int, int) -> int` | Integer modulo. |
| `rem` | `(int, int) -> int` | Integer remainder. |

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

| Identifier | Signature(s) | Notes |
|------------|--------------|-------|
| `<` | `(int, int) -> bool`, `(float, float) -> bool` | |
| `>` | `(int, int) -> bool`, `(float, float) -> bool` | |
| `>=` | `(int, int) -> bool`, `(float, float) -> bool` | |
| `=<` | `(int, int) -> bool`, `(float, float) -> bool` | |
| `==` | `(A, A) -> bool` | Polymorphic structural equality. |
| `not` | `(bool) -> bool` | Boolean negation. Not an operator — call it. |

The four ordering operators have priority `700`, type `xfx`, as does `==`.
`not` is an ordinary function, not an operator.

```ychr-repl
ychr> B is 1 < 2.
B = true.
ychr> B is 5 == 5.
B = true.
```

`==` is *ask* equality (Prolog's `==`): it never binds, and two distinct
unbound variables compare unequal. Use `=` for unification.

There is no `\=`, `\==`, or `=\=` operator. Write the negation with
`not/1`:

```ychr-repl
ychr> B is not(1 == 2).
B = true.
ychr> B is not(unifiable(1, 2)).
B = true.
```

`not/1` works in guard position too, which is mainly why it exists:

```prolog
t(X, Y, R) <=> not(X == Y) | R = different.
t(_, _, R) <=> R = same.
```

It rejects non-booleans rather than treating any non-`false` value as
true, so `not(1)` is an error.

## Aggregators

| Identifier | Signature | Notes |
|------------|-----------|-------|
| `max` | `(T, T) -> T requiring '>='(T, T) -> bool` | Larger of two values. |
| `min` | `(T, T) -> T requiring '=<'(T, T) -> bool` | Smaller of two values. |

These are the prelude's only bounded declarations. Each bound names a
prelude comparison — `>=` for `max`, `=<` for `min` — and those are
closed classes over `int` and `float`, so `max` and `min` work at those
two types only: `max("a", "b")` is rejected with `YCHR-60012`. See
[type-system.md](type-system.md#bounded-polymorphism) for what a bound
means.

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
| `atom/1` | The argument is an atom or 0-arity data constructor (e.g. `red`, `prelude:[]`, declared `mlt`). The two are interchangeable at the value level. |
| `boolean/1` | The argument is `true` or `false`. |
| `string/1` | The argument is a string literal. |
| `ground/1` | The argument contains no unbound variables anywhere. |

```ychr-repl
ychr> B is var(X).
B = true,
X = _.
ychr> B is ground(quote(foo(1, 2))).
B = true.
```

`foo/2` is not a declared constructor here, so it is wrapped in `quote/1` —
the quoting form that passes a compound as opaque data. Without the wrapper
the query still answers `B = true`, but it also emits a `YCHR-20101`
undeclared-constructor warning.

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
ychr> Vs is term_variables(quote(foo(X, bar(Y, X)))).
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

## I/O

These are functions: calling them in a rule body or at the prompt
evaluates them for their side effect and discards the unit return.

| Identifier | Effect |
|------------|--------|
| `write/1` | `(string) -> any`. Print the argument with no trailing newline. |
| `nl/0` | `() -> any`. Print a newline. |
| `writeln/1` | `(string) -> any`. Print the argument followed by a newline. |

`write/1` and `writeln/1` take a *string*, not an arbitrary term:
`write(1)` is a type error. Use `write_term_to_string/1` from `meta` to
render a term first, or `print/1` to print one directly.

## Other libraries

The bundled libraries `lists`, `strings`, and `meta` ship
alongside the prelude under [`libraries/`](../../libraries/).

Unlike the prelude, these are *not* auto-loaded outside the REPL —
inside the REPL all of them are available; in compiled programs use
`:- use_module(library(name)).` to import explicitly.

### `lists`

[`libraries/lists.chr`](../../libraries/lists.chr). Written in CHR
itself rather than delegated to host calls.

| Function | Description |
|---|---|
| `cons(T, list(T)) -> list(T)` | Prepend an element. |
| `head/1`, `tail/1` | First element / everything after it. Partial: a runtime error on `[]`. |
| `length(list(T)) -> int` | Number of elements. |
| `member(T, list(T)) -> bool` | Membership test, using `==`. |
| `append(list(T), list(T)) -> list(T)` | Concatenate two lists. |
| `maplist(fun(A) -> B end, list(A)) -> list(B)` | Apply a function to each element. |
| `foldl(fun(B, A) -> B end, B, list(A)) -> B` | Left fold with an initial accumulator. |
| `sum_list(list(int)) -> int` | Sum. Integers only — the accumulator starts at `0`. |
| `product_list(list(int)) -> int` | Product. Integers only, starting at `1`. |
| `nth/2` | 0-based indexing. Partial: a runtime error if the index is out of range. |

`head/1`, `tail/1` and `nth/2` carry no type signature. They are
genuinely partial, and a signature is what enables the exhaustiveness
checker — so annotating them would make every importing module emit
`YCHR-20103`, which `--Werror` turns fatal. Their arguments are
therefore `any` to the type checker.

### `strings`

[`libraries/strings.chr`](../../libraries/strings.chr). Thin wrappers
over host primitives.

| Function | Description |
|---|---|
| `string_concat(string, string) -> string` | Concatenation. |
| `string_length(string) -> int` | Length in characters. |
| `string_upper(string) -> string` | Upper-case. |
| `string_lower(string) -> string` | Lower-case. |

There is no splitting, slicing, or search yet, and no conversion between
strings and atoms or numbers.

### `meta`

[`libraries/meta.chr`](../../libraries/meta.chr). Reflection over the
store and over terms.

| Function | Description |
|---|---|
| `print/1` | Print a term in its source-like form. |
| `read_term_from_string/1` | Parse a term from text. |
| `write_term_to_string/1` | Render a term back to text. |
| `print_store/0` | Print the whole constraint store. |
| `write_store_to_list/0` | Return the store as a list of terms. |

Only `print/1` works on both backends. `read_term_from_string/1`,
`write_term_to_string/1`, `write_store_to_list/0` and `print_store/0` are
Haskell-only — the Scheme runtime either stubs them out or has no
implementation at all, so calling them from compiled Scheme fails (see
`dev-docs/SCHEME_BACKEND_GAPS.md`).

## See also

- [Language reference](language.md).
- [Type system](type-system.md) — how the overloaded signatures are
  resolved.
- [How-to: call host functions](../how-to/call-host-functions.md).
