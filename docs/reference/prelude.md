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
  overloaded — `+`, `-`, `*` across `int` and `float`, and `<`, `>`,
  `>=`, `=<` across those and `string` — are declared as `:- class`
  with one signature per concrete combination of types, e.g.
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

The four ordering operators are overloaded for `int`, `float` and
`string`; each returns `bool`. Strings order lexicographically by
code point — case-sensitive, and following no locale's collation
rules, so `"Z" < "a"` is `true`. There is no mixed-type
comparison: `1 < "a"` matches no signature (`YCHR-60006`).

| Identifier | Signature(s) | Notes |
|------------|--------------|-------|
| `<` | `(int, int) -> bool`, `(float, float) -> bool`, `(string, string) -> bool` | |
| `>` | `(int, int) -> bool`, `(float, float) -> bool`, `(string, string) -> bool` | |
| `>=` | `(int, int) -> bool`, `(float, float) -> bool`, `(string, string) -> bool` | |
| `=<` | `(int, int) -> bool`, `(float, float) -> bool`, `(string, string) -> bool` | |
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
closed classes over `int`, `float` and `string`, so `max` and `min`
work at exactly those three types: `max("pear", "apple")` is
`"pear"`, while `max(red, green)` over a user type is rejected with
`YCHR-60012`, there being no `>=` signature for it. See
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

The bundled libraries `lists`, `maybe`, `pairs`, `strings`, `meta`, and
`search` ship alongside the prelude under
[`libraries/`](../../libraries/).

Unlike the prelude, these are *not* auto-loaded outside the REPL —
inside the REPL all of them are available; in compiled programs use
`:- use_module(library(name)).` to import explicitly.

### `lists`

[`libraries/lists.chr`](../../libraries/lists.chr). Written in CHR
itself rather than delegated to host calls. Imports
[`maybe`](#maybe), which is what `nth_maybe/2` returns.

| Function | Description |
|---|---|
| `cons(T, list(T)) -> list(T)` | Prepend an element. |
| `head/1`, `tail/1` | First element / everything after it. Partial: a runtime error on `[]`. |
| `length(list(T)) -> int` | Number of elements. |
| `same_length(list(A), list(B)) -> bool` | Whether two lists have the same number of elements, without counting either. |
| `member(T, list(T)) -> bool` | Membership test, using `==`. |
| `append(list(T), list(T)) -> list(T)` | Concatenate two lists. |
| `concat(list(list(T))) -> list(T)` | Flatten one level of nesting. |
| `reverse(list(T)) -> list(T)` | Reverse. |
| `maplist(fun(A) -> B end, list(A)) -> list(B)` | Apply a function to each element. |
| `concat_map(fun(A) -> list(B) end, list(A)) -> list(B)` | Apply a list-valued function to each element and concatenate the results. |
| `filter(fun(A) -> bool end, list(A)) -> list(A)` | Keep the elements satisfying a predicate. |
| `foldl(fun(B, A) -> B end, B, list(A)) -> B` | Left fold with an initial accumulator. |
| `foldr(fun(A, B) -> B end, B, list(A)) -> B` | Right fold with an initial accumulator. |
| `zip_with(fun(A, B) -> C end, list(A), list(B)) -> list(C)` | Combine two lists element-wise, stopping at the shorter one. (To pair them up instead, see `zip/2` in [`pairs`](#pairs).) |
| `all(fun(A) -> bool end, list(A)) -> bool` | True when every element satisfies the predicate. |
| `all2(fun(A, B) -> bool end, list(A), list(B)) -> bool` | Pairwise `all`: the predicate holds of every pair at the same position, and the lengths agree. `false` on a length mismatch. |
| `any(fun(A) -> bool end, list(A)) -> bool` | True when some element does. |
| `take(int, list(T)) -> list(T)` | The first `N` elements; the whole list if it is shorter, `[]` for `N =< 0`. |
| `drop(int, list(T)) -> list(T)` | Everything after the first `N` elements; `[]` if the list is shorter, the whole list for `N =< 0`. |
| `replicate(int, T) -> list(T)` | `N` copies of one element; `[]` for `N =< 0`. |
| `distinct(list(T)) -> list(T)` | The elements in order, with every repeat of an earlier one dropped. Uses `==`; keeps the *first* occurrence. |
| `sort_by(fun(A, A) -> bool end, list(A)) -> list(A)` | Sort under a caller-supplied strict less-than. Stable. |
| `sum_list(list(int)) -> int` | Sum. Integers only — the accumulator starts at `0`. |
| `product_list(list(int)) -> int` | Product. Integers only, starting at `1`. |
| `nth/2` | 0-based indexing. Partial: a runtime error if the index is out of range. |
| `nth_maybe(int, list(T)) -> maybe(T)` | 0-based indexing, total: `nothing` for an index that is negative or past the end. |

`head/1`, `tail/1` and `nth/2` carry no type signature. They are
genuinely partial, and a signature is what enables the exhaustiveness
checker — so annotating them would make every importing module emit
`YCHR-20103`, which `--Werror` turns fatal. Their arguments are
therefore `any` to the type checker. `nth_maybe/2` is the typed,
total alternative to `nth/2`.

`take/2`, `drop/2` and `replicate/2` clamp rather than fail: an
out-of-range count is not an error.

`sort_by/2` takes a *strict* less-than — a comparison that answers
`false` for two elements it considers equal. Stability follows: ties
keep their input order, so sorting twice under two orderings refines
rather than scrambles.

```prolog
R is sort_by(fun(A, B) -> A < B end, [3, 1, 2]).   % [1, 2, 3]
```

Every function here matches on the list spine, so a *partial* list —
one whose tail is still an unbound variable, like `[1|T]` — cannot be
processed: dispatch reaches a spine test with nothing to inspect. This
is an *instantiation* failure ("argument 1 of … is not sufficiently
instantiated to select an equation"), which the message distinguishes
from a genuine mismatch such as `length(foo)` ("no matching equation
in `lists:length/1`").

Where that leaves you depends on the position. In an `is` expression,
a rule body or a top-level goal it is a hard runtime error
(`YCHR-60001`): the list must be proper by the time the call is
evaluated. In a *rule guard* it soft-fails — the guard evaluates to
false, the rule does not fire, and binding the tail reactivates the
constraint so the rule is retried on the completed list (see
[Soft guard failure](language.md#soft-guard-failure)). There is still
no suspension inside the call itself; the retry is whole-rule.

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
| `assoc_put_with(fun(V, V) -> V end, K, V, list(pair(K, V))) -> list(pair(K, V))` | The same, except that an existing value is *combined* with the new one instead of overwritten. The function takes the new value first and the existing one second, as `Map.insertWith` does. |
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

Ordering strings needs nothing from this library: `<`, `>`, `=<` and
`>=` carry a `(string, string) -> bool` signature alongside their
numeric ones. There is no splitting, slicing, or search yet, and no conversion between
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
| `name_base/1` | The local part of a name atom: `mod:foo` → `foo`. |

`name_base/1` drops a name atom's module qualifier, leaving an
unqualified atom untouched. Two names have the same base exactly when
their unqualified spellings agree, which is how a program recognizes a
name without knowing which module declared it. Given a module `palette`
declaring `red` and a module `other` declaring its own `red`:

```prolog
:- module(palette, [qualified/1, same_base/1]).
:- chr_type colour ---> red ; green.

% `green` is this module's constructor, so it canonicalizes to
% `palette:green` and its base is `green`.
q @ qualified(R) <=> R is name_base(green).

% Two `red`s from different modules: different atoms, same base.
s @ same_base(R) <=> R is name_base(palette:red) == name_base(other:red).
```

binds `R = green` and `R = true` respectively. A non-atom argument is a
runtime error. An *unbound* argument is an instantiation failure, so a
rule guard calling `name_base/1` delays and is retried when the
variable is bound, rather than aborting the query (see
[Soft guard failure](language.md#soft-guard-failure)).

`run_chr_session/1` takes one constraint term — or a list of them, run
in order — wrapped in `quote/1` to keep it symbolic. The sub-session
has its own store, propagation history, and reactivation queue but the
same rules, functions, and host calls; the goal's constraints are
resolved through the program's exports, so they must be exported (an
unknown or unexported goal constraint is a runtime error in the
caller, not a `false` result). It returns `true` if and only if the
sub-session runs to quiescence, and `false` otherwise — a runtime
error, or (inside a search branch) a `search:fail/0`. Bindings the
sub-session made before failing are not rolled back. Unbound variables
inside the goal are shared with the sub-session, so bindings made there
survive the call — pass fresh out-variables to read results back:

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

`print/1` and `name_base/1` work on both backends.
`read_term_from_string/1`,
`write_term_to_string/1`, `write_store_to_list/0`, `print_store/0` and
`run_chr_session/1` are
Haskell-only — the Scheme runtime either stubs them out or has no
implementation at all, so calling them from compiled Scheme fails (see
`dev-docs/SCHEME_BACKEND_GAPS.md`).

### `search`

[`libraries/search.chr`](../../libraries/search.chr). Opt-in search:
explore alternative bindings and undo the ones that do not work out.
Nothing here affects a program that does not import it.

| Name | Kind | Description |
|---|---|---|
| `choose/2` | constraint | `choose(X, Alts)` marks a pending choice. It has no rules — it sits in the store until the driver reaches it. |
| `solve/1` | `(any) -> bool` | Run a goal, stop at its first solution and keep its bindings. `false` when the space is exhausted, with everything undone. |
| `find_all/2` | `(any, any) -> list(any)` | Every solution of a goal, as a list of copies of a template. Fully undone afterwards. |
| `fail/0` | `() -> any` | Fail the current branch. Outside a search, a runtime error. |
| `try_unify/2` | constraint | Prolog's `=`: unify, or fail the branch instead of erroring. |

The model is *choice at quiescence*: run the goal to a fixpoint, take
the oldest `choose` left in the store, bind its variable to each
alternative in turn, propagate again, and undo a branch that fails.

```prolog
:- use_module(library(search)).
:- chr_constraint pair(any, any, any), sum_is(any, any, any).

pair(X, Y, S) <=> choose(X, [1, 2, 3]), choose(Y, [1, 2, 3]), sum_is(X, Y, S).
sum_is(X, Y, S) <=> not(X + Y == S) | fail.
```

With that program, `solve(quote(pair(X, Y, 5)))` is `true` with
`X = 2, Y = 3`, and `find_all([X, Y], quote(pair(X, Y, 5)))` is
`[[2, 3], [3, 2]]` with `X` and `Y` left unbound.

Failure is not error: a runtime error inside a branch propagates out of
the search rather than failing the branch, and body `=` still errors on
a mismatch — write `try_unify/2` where a mismatch is a dead end. Goals
run in a fresh sub-session, so the caller's store is not searched. The
whole library is Haskell-only.

For the full contract — commit and undo rules, nesting, the ωr
interaction, and every edge case — see the
[search specification](search.md).

## See also

- [Language reference](language.md).
- [Search](search.md) — the `search` library's specification.
- [Type system](type-system.md) — how the overloaded signatures are
  resolved.
- [How-to: call host functions](../how-to/call-host-functions.md).
