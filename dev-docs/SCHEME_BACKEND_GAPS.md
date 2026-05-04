# Scheme Backend Gaps

This document lists known divergences between the Haskell interpreter (the
reference implementation) and the Scheme backend, as surfaced by the golden
test suite. Each gap is a candidate fix; resolving one usually means removing
an entry from `HASKELL_ONLY` or `HASKELL_ONLY_CASES` in
`test/scheme/test_golden.py`.

The scope is the Scheme backend (`src/YCHR/Backend/Scheme.hs`) plus its
runtime in `scheme/ychr/`. Goals are run through `guile3.0 --r6rs` per
`Makefile`'s `test-scheme` target.


## Unbound runtime primitives

The Scheme backend emits names that are not bound in Guile's r6rs subset,
so any goal that hits these crashes with `Unbound variable: <name>`.

| Source side          | `hostCallMap` target | Status in r6rs / runtime |
|----------------------|----------------------|--------------------------|
| `div` (integer)      | `quotient`           | Unbound — `(rnrs)` only exposes `div`/`mod`/`div0`/`mod0`. |
| `mod` (integer)      | `modulo`             | Unbound for the same reason. |
| `rem`                | `mod0`               | `mod0` exists in `(rnrs)`; not exercised by current tests but worth confirming. |
| `int_to_float`       | `exact->inexact`     | Unbound in Guile's r6rs subset. |
| `float_to_int`       | `exact-truncate`     | Not a standard r6rs binding. |

These cases are the entire reason `arith_int` div/mod and
`int_float_conversion` are currently in `HASKELL_ONLY_CASES`.

**Fix sketch:** either change the mapping in `hostCallMap`
(`src/YCHR/Backend/Scheme.hs:352`) to a binding that exists in Guile's r6rs
(e.g. `div`/`mod` for integer division), or add `(rnrs r5rs)` /
`(scheme base)` imports in the generated driver / runtime so the legacy
names resolve. Truncation toward zero for `float_to_int` will need a small
helper since `exact` rounds rather than truncates.


## Missing meta primitives

Some primitives the prelude exports have no implementation on the Scheme
side at all.

| Primitive    | Where it should live | Status |
|--------------|----------------------|--------|
| `copy_term`  | `scheme/ychr/runtime.sls` + `hostCallMap` | No entry in `hostCallMap`, no `%copy-term` export. The generated code emits a literal `copy_term` call that Guile cannot resolve. |
| `read_term_from_string` | `runtime.sls` | Stubbed: `(error "%read-term-from-string" "not implemented")` — already covered by the `read_term_test` entry in `HASKELL_ONLY`. |

**Fix sketch for `copy_term`:** mirror the Haskell implementation —
recursively walk the term, allocate fresh vars on each first encounter of
an unbound variable, preserve sharing via an id→fresh-var hashtable. Add a
`%copy-term` export in `scheme/ychr/runtime.sls` and a corresponding
`("copy_term", "%copy-term")` entry in `hostCallMap`.


## Equality and groundness divergences

| Symptom | Affected case | Root cause |
|---------|---------------|------------|
| `==` on equal compound terms returns `false` on Scheme. | `comparisons-term_eq` | `hostCallMap` maps `==` to `eqv?`, which is reference / atom equality in r6rs and does not recurse into compound terms. The Haskell runtime uses a structural `equal` that follows binding chains. |
| `ground/1` reports a different answer for a partially-unbound term. | `type_predicates-grd_no` | `%ground?` in `runtime.sls` looks correct on inspection; the divergence is more likely in how the Scheme-side test harness builds the probe value (or in deref on closure-captured vars). Needs investigation before claiming a root cause. |
| Float literal in head pattern doesn't match. | `hnf_literal_in_head-float_15` | Unconfirmed — likely the Scheme-side `match-term` or literal compilation does not compare floats by value. |

**Fix sketch for `==`:** swap `eqv?` for the existing `equal?/chr` export
from `(ychr var)` (used by `Equal` already), or introduce a dedicated
`%==` wrapper.


## Pretty-printing divergences

These don't reflect runtime bugs — both backends compute the same value —
but the goal-output format differs, which is what golden tests check.

| Output | Haskell | Scheme |
|--------|---------|--------|
| Negative integer literal | `(-2)` | `-2` |
| Negative float literal   | `(-3.14)` | `-3.14` |
| Small float              | `1.0e-6` | (decimal expansion or different exponent form) |
| Large float              | `1.0e10` | (decimal expansion) |
| Quoted atom with space   | `'hello world'` | `hello world` (no quotes) |
| Quoted unicode atom      | `'café'`, `'你好'` | renders without surrounding quotes |
| Locally-declared constructor in lambda body | `'tc__just'(0)` (mangled) | renders differently |

The Haskell side goes through `prettyTerm` (`src/YCHR/Pretty.hs`), which
uses operator-precedence rules to add parentheses around negative-prefix
operators and the `renderAtom` quoting rules from `(ychr pretty)` are
quote-aware.

The Scheme side uses `pretty-term` in `scheme/ychr/pretty.sls`, which
formats numbers via Guile's `number->string` and atoms via plain symbol
display.

**Fix sketch:** unify the two pretty-printers around the same rules. The
straightforward path is to teach `scheme/ychr/pretty.sls` the same
parenthesizing and atom-quoting logic as `prettyTerm`, since the Haskell
output is the documented contract for `prettyBindings`.


## Test-suite mapping

For each gap above, the corresponding golden tests are skipped on the
Scheme backend via lists in `test/scheme/test_golden.py`:

- Whole directories (every case affected): `copy_term_sharing`,
  `int_float_conversion`, `typecheck_constructor_in_lambda_body`, plus
  the long-standing `copy_term_fn` and `read_term_test` exclusions.
- Specific cases: see `HASKELL_ONLY_CASES` in `test/scheme/test_golden.py`
  for the full list, grouped by symptom (negative-number rendering,
  unbound `quotient`/`exact->inexact`, term-`==` divergence, unicode
  atom quoting, etc.).

Removing an entry should be the last step of a fix: make the gap go away
in the Scheme backend / runtime, regenerate any affected `.expected` if
appropriate, then drop the skip-list entry and confirm `make test`
passes.


## Suggested order of fixes

1. **Unify pretty-printing** — purely cosmetic, but unblocks ~20 cases at
   once and lets future tests pin negative-number output without
   special-casing.
2. **Fix the `hostCallMap` integer-arithmetic bindings** — small mapping
   change, unblocks `arith_int` div/mod cases.
3. **Implement `copy_term` in the Scheme runtime** — well-scoped; the
   Haskell version in `src/YCHR/Runtime/Registry.hs` is a faithful
   reference.
4. **Fix `==` for compound terms** — one-line mapping change once
   `equal?/chr` is reused.
5. **Implement `int_to_float` / `float_to_int`** — likely a small driver
   adjustment plus a truncation helper.
6. **Investigate `ground/1` and HNF float-match divergences** before
   claiming root cause.
