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
| `run_chr_session`       | No Scheme-side implementation — it spawns a nested interpreter session (the search driver, `YCHR.Internal.Runtime.Search`, on the Haskell side). `run_chr_session_test` is in `HASKELL_ONLY`. |


## `library(search)`

No Scheme-side implementation of `solve/1`, `find_all/2`,
`fold_solutions/4` or `fail/0` (`forall/3` and `find_n/3` are derived
in CHR and need nothing of their own).
The search driver needs three things the Scheme runtime does not have:
a session fork (as `run_chr_session` above), a snapshot of the store /
suspension-map / history / reactivation-queue references, and an undo
trail hooked into every variable-cell and suspension-flag write
(`src/YCHR/Internal/Runtime/{Search,Trail}.hs`). Every `search_*`
directory with runnable goals is in `HASKELL_ONLY`: `search_alt`,
`search_basic`, `search_disj`, `search_fold`, `search_generate`,
`search_label`, `search_label_alt` and `search_nested`. The two
compilation-negative directories, `search_disj_no_import` and
`search_disj_type_error`, need no entry: the Scheme harness discovers
cases from `.goal` files and they have none.

Compilation itself succeeds. The library wrappers become ordinary
compiled procedures (`func_search__solve1`, `func_search__fail0`, …),
but the `host:` call inside each has no `hostCallMap` entry, so
`Scheme.compileHostCall` lowers it to a bare verbatim identifier —
`(solve (deref arg_0))`, `(fail)`. Importing the generated library
still succeeds under Guile, which resolves free identifiers lazily;
the failure comes when a search is first *called*:

    ERROR: In procedure %resolve-variable:
    Unbound variable: solve

`alt/1`, `choose/2` and `try_unify/2` need nothing special — they are
ordinary CHR and compile and run fine; a program that only tells a
choice point without ever calling `solve/1` behaves identically on both
backends (the choice just sits in the store).

Note that the Haskell driver deliberately does *not* reuse the trail
for anything outside a search: `SessionEnv.trail` is `Nothing` at the
top level, so a Scheme implementation would not have to pay for the
hook in ordinary programs either.


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
does not evaluate, and that wrapping in `quote/1` would keep the outer
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


## Numeric primitives accept more than Haskell's

Orthogonal to which *failures* are classified (that gap is closed
below): the Scheme numeric primitives succeed on operand combinations
the Haskell registry rejects. Long-standing, and deliberately left
alone when the classification wrappers went in, because tightening it
can move golden output and is a separate question.

| Call | Haskell | Scheme |
|---|---|---|
| `1 + 1.0` | `arithmetic host call: expected 2 numeric arguments of same type` | `2.0` |
| `1 < 2.0` | `comparison host call: … of the same type` | `true` |
| `5.0 div 2.0` | `integer arithmetic host call: expected 2 Int arguments` | `2` |

A type-checked program cannot reach any of these — the prelude's
`:- class` signatures are same-type — so this is only visible from
untyped code and `host:` calls.

One consequence does touch soft guards. `%add`/`%sub`/`%mul`/`%fdiv`
are strictly 2-ary where the native `+ - * /` they replaced were
variadic, so `host:'+'(X, 1, 2)` raises an untagged `&assertion` and
aborts a guard, where Haskell's `numArith2` reaches `argError`, sees
the unbound `X`, and delays. Wrong-arity host calls to a prelude
primitive are the only way in.


## Closed gaps (reference)

The following used to live here and are now closed. Kept as a brief
record of which fixes have already shipped.

- **[Soft guard failure](../docs/reference/language.md#soft-guard-failure)**
  — the `bsoft-guard` VM form was implemented, but the failures it is
  meant to catch were not all tagged. Two halves, both now fixed.
  *Host-primitive classification*: the strict primitives were bare
  native Scheme procedures raising an untagged wrong-type condition, so
  a guard blocked on one aborted instead of delaying. Each now routes
  its failure through `%arg-error` in `runtime.sls`, which raises
  `%chr-inst-error` when an argument derefs to an unbound variable and
  `%chr-error` otherwise — the same failure-path split `argError` makes
  in `src/YCHR/Internal/Runtime/Registry.hs`, so a correct program pays
  nothing. `hostCallMap` grew entries for `+ - * /`, the `string_*`
  operations and `write`, which previously lowered to native procedures
  the runtime never saw. *`bfrom-val`*: it lowered to the bare value
  expression and let Scheme truthiness decide, so an unbound variable
  in guard position read as *true*; it now goes through
  `%bool-from-value`, mirroring `boolFromValue`. Closed
  `HASKELL_ONLY_CASES` entries for `("mode_boundness_guard",
  "unguarded")`, both `soft_guard_retry` cases,
  `("soft_guard_permanent", "run")`, both
  `soft_guard_equation_propagation` cases, and
  `("soft_guard_var_guard", "reject")`. The classification itself is
  pinned directly by `scheme/test/test-runtime.scm`, since the golden
  harness runs positive cases only.
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
- **Dead `host__` bridge in the generated driver** — `ychr gen-driver`
  compiled a `host:` call in a goal argument to `(host__<f> …)`, a name
  no Scheme module defines, because `SchemeDriver.hostBridgeName`
  invented its own mangling instead of mirroring
  `Scheme.compileHostCall`. The procedure name and the session predicate
  now come from a shared `Scheme.hostCallTarget`, so driver and library
  emit `(%add (deref …) …)` / `(%copy-term %s …)` identically; the
  driver arm derefs its arguments too, and no longer leaves the stray
  space `(host__now )` on a zero-arity call. Pinned by
  `test/golden/driver_host_call/` (three cases, run on both backends)
  and by `test/scheme/test_golden.py::test_gen_driver_host_call_mapping`.
