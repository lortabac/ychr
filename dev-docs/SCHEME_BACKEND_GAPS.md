# Scheme Backend Gaps

This document lists known divergences between the Haskell interpreter (the
reference implementation) and the Scheme backend, as surfaced by the golden
test suite. Each gap is a candidate fix; resolving one usually means removing
an entry from `HASKELL_ONLY` or `HASKELL_ONLY_CASES` in
`test/scheme/test_golden.py`.

The scope is the Scheme backend (`src/YCHR/Backend/Scheme.hs`) plus its
runtime in `scheme/ychr/`. Goals are run through `guile3.0 --r6rs` per
`Makefile`'s `test-scheme` target.


## Missing meta primitives

| Primitive               | Status |
|-------------------------|--------|
| `read_term_from_string` | Stubbed in `runtime.sls` as `(error "%read-term-from-string" "not implemented")`. The whole `read_term_test` directory is in `HASKELL_ONLY`. |
| `write_store_to_list`   | No Scheme-side implementation; `write_store_to_list_test` is in `HASKELL_ONLY` (parallels the unimplemented `print_store`). |


## Atom pretty-printing divergences

The Haskell `prettyTerm` (`src/YCHR/PExpr.hs`) quotes atoms whose text is
not a bare lowercase identifier, escaping embedded quotes — so `'hello
world'`, `'café'`, and `'你好'` are quoted on output. The Scheme
`pretty-term` (`scheme/ychr/pretty.sls`) emits symbols via
`symbol->string` (after the qualified-name unmangle pass) with no
quoting.

Tests still skipped on the Scheme backend:

- `("unicode_atoms_strings", "quoted_with_space" | "quoted_unicode" |
  "quoted_chinese")` — Scheme prints the bare text where Haskell quotes
  it.

**Fix sketch:** teach `scheme/ychr/pretty.sls` the same `needsQuoting`
logic as `renderAtom` — bare lowercase + alphanumeric + underscore stays
unquoted, anything else gets `'…'` with embedded `'` doubled.


## Lambda-body constructor leaks mangled name (Haskell-side)

All cases under `typecheck_constructor_in_lambda_body` are skipped via
`HASKELL_ONLY`. The `.expected` files pin `R = 'tc__just'(0)`. After
the qualified-name unmangle pass landed in `pretty.sls`, the Scheme
backend now prints `R = tc:just(0)` for the same goal — the *correct*
qualified-atom rendering. The Haskell interpreter still produces
`'tc__just'(0)`, meaning the lambda-lifting / constructor-handling path
in `src/YCHR/Desugar.hs` (or downstream) is leaking the mangled name as
an `Unqualified` atom rather than keeping it as `Qualified tc just`.
The quoting on the Haskell side is incidental — it kicks in because
`tc__just` contains `__`, which is illegal in an unquoted atom.

**Fix sketch:** trace where the constructor reference inside the
lifted lambda body loses its qualified form. Once that is corrected,
both backends will print `tc:just(0)` and the `.expected` files can be
updated, then the entry removed from `HASKELL_ONLY`.


## `ground/1` in goal queries with nested unbound vars

The case `("type_predicates", "grd_no")` runs the goal
`type_predicates:t(grd, p(1, X), R)`. The Scheme runtime's `%ground?`
appears correct in isolation, but the generated driver produced by
`ychr gen-driver` for a goal that introduces an unbound variable inside
a compound argument (`X` inside `p(1, X)`) does not bind that variable
before passing it to the constraint, so Guile rejects with
`Unbound variable: X`. This is a driver-side bug, not a runtime one.
Needs investigation before claiming a root cause.


## Closed gaps (reference)

The following used to live here and are now closed. Kept as a brief
record of which fixes have already shipped.

- **`==` on compound terms** — was `eqv?` (atomic identity); now
  `equal?/chr` (structural). Fixed a latent bug in `equal*` where
  flonums fell through to `#f` (covered by widening the integer case to
  `(number? d)`).
- **Integer `div` / `mod`** — Guile's `(rnrs)` lacks `quotient`/`modulo`,
  and r6rs `div`/`mod` is Euclidean while the test contract is floor
  division. Now implemented as `%idiv` / `%imod` in
  `scheme/ychr/runtime.sls` using `(exact (floor (/ n d)))`.
- **`int_to_float` / `float_to_int`** — `exact->inexact` and
  `exact-truncate` are not in Guile's r6rs subset. Now `%int-to-float` /
  `%float-to-int` in `runtime.sls`, using `inexact` and
  `(exact (truncate x))`.
- **Negative-number pretty-printing** — `pretty-term` now wraps negative
  numbers in `(...)` to match the Haskell contract. Same edit also
  fixes a bug where inexact integer-valued floats (e.g. `1000000.0`)
  rendered as `"1000000"` because `(integer? 1000000.0)` is `#t` in
  Scheme; we now distinguish exact integers from inexact numbers.
- **`copy_term`** — implemented as `%copy-term` in `runtime.sls`,
  mirroring `copyTerm` in `src/YCHR/Runtime/Registry.hs` (sharing
  preserved via an id→fresh-var hashtable). The backend grew a
  `sessionHostCalls` set so host calls that need the session can have
  `%s` threaded as their first argument.
- **HNF float literal match** — `tag(1.5, R) <=> R = one_half` now
  matches because the underlying `Equal` VM expression already routes
  through `equal?/chr`, and the equality fix above means flonum-flonum
  compares structurally.
- **Qualified-name separator (`__` vs `:`)** — `pretty-term` in
  `scheme/ychr/pretty.sls` now unmangles `module__name` back to
  `module:name` on output (via `unmangle-qualified`, splitting on the
  first `__` at position ≥ 1). This is safe because the lexer
  (`src/YCHR/PExpr.hs`) rejects `__` inside any user atom. Closed
  `HASKELL_ONLY_CASES` entries for `type_export_constructor_allowlist`
  and `type_import_constructor_narrowing`. The unicode-escape form
  `__u<hex>__` still passes through unchanged and is covered by the
  unicode quoting divergence above.
