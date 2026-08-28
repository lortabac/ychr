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

The import is always the *whole* prelude, and it cannot be narrowed.
Writing `:- use_module(library(prelude)).` explicitly is accepted but
redundant; attaching an import list to it is an error
([`YCHR-20019`](errors.md)). Resolve a clash with a prelude name by
renaming your own identifier, not by adjusting imports.

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

The bundled libraries `lists`, `maybe`, `pairs`, `strings`, and `meta`
ship alongside the prelude under [`libraries/`](../../libraries/).

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
| `reverse(list(T)) -> list(T)` | Reverse. |
| `maplist(fun(A) -> B end, list(A)) -> list(B)` | Apply a function to each element. |
| `filter(fun(A) -> bool end, list(A)) -> list(A)` | Keep the elements satisfying a predicate. |
| `foldl(fun(B, A) -> B end, B, list(A)) -> B` | Left fold with an initial accumulator. |
| `foldr(fun(A, B) -> B end, B, list(A)) -> B` | Right fold with an initial accumulator. |
| `zip_with(fun(A, B) -> C end, list(A), list(B)) -> list(C)` | Combine two lists element-wise, stopping at the shorter one. (To pair them up instead, see `zip/2` in [`pairs`](#pairs).) |
| `all(fun(A) -> bool end, list(A)) -> bool` | True when every element satisfies the predicate. |
| `any(fun(A) -> bool end, list(A)) -> bool` | True when some element does. |
| `take(int, list(T)) -> list(T)` | The first `N` elements; the whole list if it is shorter, `[]` for `N =< 0`. |
| `drop(int, list(T)) -> list(T)` | Everything after the first `N` elements; `[]` if the list is shorter, the whole list for `N =< 0`. |
| `sum_list(list(int)) -> int` | Sum. Integers only — the accumulator starts at `0`. |
| `product_list(list(int)) -> int` | Product. Integers only, starting at `1`. |
| `nth/2` | 0-based indexing. Partial: a runtime error if the index is out of range. |

`head/1`, `tail/1` and `nth/2` carry no type signature. They are
genuinely partial, and a signature is what enables the exhaustiveness
checker — so annotating them would make every importing module emit
`YCHR-20103`, which `--Werror` turns fatal. Their arguments are
therefore `any` to the type checker.

`take/2` and `drop/2` clamp rather than fail: an out-of-range count is
not an error.

Every function here matches on the list spine, so a *partial* list —
one whose tail is still an unbound variable, like `[1|T]` — is a
runtime error (`YCHR-60001`, "argument 1 of … is not sufficiently
instantiated to select an equation"), not a suspension. There is no
delaying: the list argument must be a proper list by the time the call
is evaluated. The message distinguishes this from a genuine mismatch
such as `length(foo)`, which reports "no matching equation in
`lists:length/1`".

### `maybe`

[`libraries/maybe.chr`](../../libraries/maybe.chr). An optional value —
the result of a computation that may not produce one.

```prolog
:- chr_type maybe(A) ---> just(A) ; nothing.
```

| Function | Description |
|---|---|
| `map_maybe(fun(A) -> B end, maybe(A)) -> maybe(B)` | Apply a function to the value inside, if any (functor). |
| `map_maybe(fun(A, B) -> C end, maybe(A), maybe(B)) -> maybe(C)` | Combine two optional values, yielding one only when both are present. |
| `maybe_and_then(maybe(A), fun(A) -> maybe(B) end) -> maybe(B)` | Sequence a second optional computation after this one (monad). |
| `M >>= F`, `F =<< M` | Operator spellings of `maybe_and_then/2`, in both directions. |
| `is_just(maybe(A)) -> bool`, `is_nothing(maybe(A)) -> bool` | Which case this is. |
| `from_maybe(A, maybe(A)) -> A` | The value, or a default. |
| `foldr_maybe(B, fun(A) -> B end, maybe(A)) -> B` | Eliminate a `maybe` in one step: a default for `nothing`, a function for `just`. |

`>>=` is `yfx` and `=<<` is `xfy`, both at priority 740 — tighter than
`is` (750), so `R is M >>= F` needs no parentheses, and looser than the
comparisons (700).

```prolog
R is just(2) >>= fun(X) -> just(X + 1) end
             >>= fun(Y) -> just(Y * 10) end.   % just(30)
```

`map_maybe` is named for the arity it maps over: `map_maybe/2` is the
functor map, `map_maybe/3` the applicative lift. There is no
`map_maybe/4` — it would need to apply a three-argument function, and
`'$call'`, hence `call/N`, supports one and two arguments only.

### `pairs`

[`libraries/pairs.chr`](../../libraries/pairs.chr). Key/value pairs and
association lists, also written in CHR. Imports [`maybe`](#maybe), which
is what `assoc_get/2` and `zip_exact/2` return.

```prolog
:- chr_type pair(K, V) ---> kv(K, V).
```

The pair constructor is `kv/2`, not Prolog's `-/2`: `-` is the prelude's
subtraction function, and a bare reference to a name that is a function
in one module and a data constructor in another is ambiguous, hence
rejected (`YCHR-20020`).

| Function | Description |
|---|---|
| `key(pair(K, V)) -> K` | First component. |
| `value(pair(K, V)) -> V` | Second component. |
| `zip(list(A), list(B)) -> list(pair(A, B))` | Pair up two lists, stopping at the shorter one. |
| `zip_exact(list(A), list(B)) -> maybe(list(pair(A, B)))` | Pair up two lists of equal length; `nothing` if the lengths differ. |
| `assoc_get(K, list(pair(K, V))) -> maybe(V)` | Look up a key: `just(V)` or `nothing`. |
| `assoc_put(K, V, list(pair(K, V))) -> list(pair(K, V))` | Replace the first entry for the key, or append a new one. |
| `assoc_update(K, fun(V) -> V end, list(pair(K, V))) -> list(pair(K, V))` | Apply a function to the first entry's value. A list with no entry for the key is returned unchanged. |
| `assoc_delete(K, list(pair(K, V))) -> list(pair(K, V))` | Remove the first entry for the key, if any. |
| `assoc_member(K, list(pair(K, V))) -> bool` | Whether the key is present. |
| `assoc_keys(list(pair(K, V))) -> list(K)` | The keys, in order. |
| `assoc_values(list(pair(K, V))) -> list(V)` | The values, in order. |

An association list is an ordinary `list(pair(K, V))` — there is no
abstract map type — and every operation is a linear scan touching only
the *first* entry for a key.

Keys are compared with `==`, which is *identity*, not unification. An
unbound key therefore matches an entry keyed on that same variable, and
nothing else: `assoc_get(K, [kv(K, 1)])` is `just(1)`, while
`assoc_get(K, [kv(K2, 1)])` for a different unbound `K2` is `nothing`.
By the same rule `assoc_put` with an unbound key appends rather than
replaces — and if that key is bound later, the list can end up holding
two entries for it, of which only the first is ever found.

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
| `run_chr_session/1` | Run a goal in a fresh session of the current program. |

`run_chr_session/1` takes one constraint term — or a list of them, run
in order — wrapped in `quote/1` to keep it symbolic. The sub-session
has its own store, propagation history, and reactivation queue but the
same rules, functions, and host calls; the goal's constraints are
resolved through the program's exports, so they must be exported (an
unknown or unexported goal constraint is a runtime error in the
caller, not a `false` result). It returns `true` when the sub-session
runs to quiescence and `false` when it raises a runtime error. Unbound
variables inside the goal are shared with the sub-session, so bindings
made there survive the call — pass fresh out-variables to read results
back:

```prolog
probe(N, R) <=> R is N + 1.
go(Ok, R) <=> Ok is run_chr_session(quote(probe(41, R))).
```

Running the goal `go(Ok, R)` yields:

```
Ok = true
R = 42
```

Reactivation does not cross the boundary: binding a shared variable
reactivates only the binding session's own stored constraints. So a
*live* stored constraint of one session must not depend on a variable
the other session binds — it would simply not be reactivated. In
practice, pass only ground terms and fresh variables in, and have the
sub-session bind its out-variables before it quiesces. See
`test/golden/run_chr_session_test/` for worked examples, including
nesting.

Only `print/1` works on both backends. `read_term_from_string/1`,
`write_term_to_string/1`, `write_store_to_list/0`, `print_store/0` and
`run_chr_session/1` are
Haskell-only — the Scheme runtime either stubs them out or has no
implementation at all, so calling them from compiled Scheme fails (see
`dev-docs/SCHEME_BACKEND_GAPS.md`).

## See also

- [Language reference](language.md).
- [Type system](type-system.md) — how the overloaded signatures are
  resolved.
- [How-to: call host functions](../how-to/call-host-functions.md).
