# Scheme Backend Gaps

This document lists known divergences between the Haskell interpreter (the
reference implementation) and the Scheme backend, as surfaced by the golden
test suite. Each gap is a candidate fix; resolving one usually means removing
an entry from `HASKELL_ONLY` or `HASKELL_ONLY_CASES` in
`test/scheme/test_golden.py`.

The scope is the Scheme backend (`src/YCHR/Internal/Backend/Scheme.hs`) plus its
runtime in `scheme/ychr/`. Goals are run through `guile3.0 --r6rs` per
`Makefile`'s `test-scheme` target.


## Missing meta primitives

| Primitive               | Status |
|-------------------------|--------|
| `read_term_from_string` | Stubbed in `runtime.sls` as `(error "%read-term-from-string" "not implemented")`. The whole `read_term_test` directory is in `HASKELL_ONLY`. |
| `write_store_to_list`   | No Scheme-side implementation; `write_store_to_list_test` is in `HASKELL_ONLY` (parallels the unimplemented `print_store`). |
| `write_term_to_string`  | No Scheme-side implementation and no `hostCallMap` entry, so a call lowers to a bare verbatim identifier and fails as an unbound variable at load time. No golden test covers it, so it is in neither `HASKELL_ONLY` nor this file's test lists. |


## `deep-eval` host-call lookup ignores arity

Haskell's `HostCallRegistry` is keyed by name alone, so
`deepEvalValue`'s fallback (`src/YCHR/Internal/Runtime/Interpreter.hs`,
`Map.lookup key.functor`) discards the arity. The Scheme table
(`*prelude-host-calls*`) keys by `(name, arity)`. Consequence, for an
arity that no host primitive provides:

    X = '-'(1), R is X.

- **Haskell**: reaches the 2-ary `-` primitive and reports
  `arithmetic host call: expected 2 numeric arguments of same type, got 1`.
- **Scheme**: no `(- . 1)` key, so it reports the intended
  `is: functor is not evaluable: -/1`.

Scheme's message is the better one (it matches SWI Prolog's
`type_error(evaluable, F/N)`). Fixing Haskell means keying the registry
by `(name, arity)`, which changes a public type
(`YCHR.Convert.HostCallRegistry`) and so is deferred past 0.1.


## Prelude host calls missing from `*prelude-host-calls*`

The table's comment says to keep it in sync with `baseHostCallRegistry`.
`write` and `writeln` are absent, so deep-eval diverges. The fallback is
reached only by `R is X` with `X` bound to a compound — note that `=`
does not evaluate, and that wrapping in `term/1` would keep the outer
functor unevaluable:

    X = writeln("x"), R is X.

- **Haskell**: prints `x`, then `R = '()'`.
- **Scheme**: `is: functor is not evaluable: writeln/1`.

Same for `write/1`. `__chr_error` is also absent, but `__` is reserved by
the lexer so no source program can name it.

`print` and `read_term_from_string` live in `metaHostCallRegistry` rather
than `baseHostCallRegistry`, so their absence is by design — but the
comment names only `baseHostCallRegistry` and so understates what
Haskell's `is` can reach.


## Dead `host__` bridge in the generated driver

`SchemeDriver.hostBridgeName` emits `host__<f>` and claims to mirror
`Scheme.compileHostCall`, which actually emits the `hostCallMap` name
(`%irem`, `equal?/chr`, …). No `host__*` procedure exists anywhere in
`scheme/`, so a goal containing a direct `host:` call generates an
unbound identifier. No golden test passes a bare `host:` call in a goal.


## Atom pretty-printing divergences

The Haskell `prettyTerm` (`src/YCHR/Internal/PExpr.hs`) quotes atoms whose text is
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
  mirroring `copyTerm` in `src/YCHR/Internal/Runtime/Registry.hs` (sharing
  preserved via an id→fresh-var hashtable). The backend grew a
  `sessionHostCalls` set so host calls that need the session can have
  `%s` threaded as their first argument.
- **HNF float literal match** — `tag(1.5, R) <=> R = one_half` now
  matches because the underlying `Equal` VM expression already routes
  through `equal?/chr`, and the equality fix above means flonum-flonum
  compares structurally.
- **Qualified n-arity constructor leaked mangled name (Haskell side)**
  — `valueToTerm` in `src/YCHR/Internal/Meta.hs` only unmangled the runtime
  functor `m__n` back into `Qualified m n` for **0-arity** terms; any
  `VTerm "m__n" (x:_)` fell through to `Unqualified "m__n"`, so a
  qualified constructor like `just(X)` (whether produced directly by
  the interpreter or via a lifted lambda body) pretty-printed as
  `'mod__just'(X)` instead of `mod:just(X)`. Fixed by extending the
  split to any arity, guarded by a non-empty module prefix so internal
  names starting with `__` still flow through as `Unqualified`.
  Closed `HASKELL_ONLY` entry for
  `typecheck_constructor_in_lambda_body`; `.expected` files updated
  from `'tc__just'(N)` to `tc:just(N)`. Regression locked by
  `test/golden/qualified_constructor_with_args/` (non-lambda path).
- **Qualified-name separator (`__` vs `:`)** — `pretty-term` in
  `scheme/ychr/pretty.sls` now unmangles `module__name` back to
  `module:name` on output (via `unmangle-qualified`, splitting on the
  first `__` at position ≥ 1). This is safe because the lexer
  (`src/YCHR/Internal/PExpr.hs`) rejects `__` inside any user atom, and the
  encoder (`encodeText` in `Compile/Names.hs`) emits no `__` of its
  own (non-ASCII characters use the `%%u<6 hex>` escape instead).
  Closed `HASKELL_ONLY_CASES` entries for
  `type_export_constructor_allowlist` and
  `type_import_constructor_narrowing`.
