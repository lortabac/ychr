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

`library(meta)`'s host calls all have Scheme implementations. Every one
is mapped in `hostCallMap` to a bound procedure in `runtime.sls`, which
is what keeps `library(meta)` importable: a generated library defines
*every* function of an imported library, so an unmapped name lowers to a
bare identifier and the whole module fails to load on a strict R6RS
implementation (Chez reports `attempt to reference unbound identifier
run_chr_session`), even for a program that only calls `print/1`.

| Primitive               | Status |
|-------------------------|--------|
| `run_chr_session`       | Implemented as `%run-chr-session`; it spawns a nested interpreter session via the search driver. `run_chr_session_test` is in `HASKELL_ONLY` for the divergence recorded under `library(search)`. |
| `run_chr_session_ep`    | Implemented as `%run-chr-session-ep`; the same driver as `run_chr_session`, without the error catch. |

The load-time invariant is pinned, without Guile, by
`test/scheme/test_golden.py::test_meta_module_host_calls_are_bound`.

`run_chr_session` is absent from `*prelude-host-calls*`, so
deep-evaluating a `host:` *term* with arguments (rather than calling
the function directly) reports `is: functor is not evaluable` instead
of reaching the implementation — the same distinction the section below
draws. `read_term_from_string` and `write_term_to_string` were in the
same state but are now implemented and registered (see *Closed gaps*).

`print_store` and `write_store_to_list` are implemented but are
deliberately *not* registered, because only their arity-0 key is
unreachable: a nullary `host:` compound collapses to an atom on both
backends (`T = host:print_store(), R is T.` binds the atom
`host:print_store`), and the deep evaluator dispatches only `term?`
values, so a `(name, 0)` key can never be asked for. At any arity ≥ 1
they are an instance of *deep-eval host-call lookup ignores arity*
above: the reference's name-keyed registry ignores the extra argument,
so `T = host:write_store_to_list(9), R is T.` returns the store on the
Haskell side while the Scheme `(name, arity)` table reports
`is: functor is not evaluable: host:write_store_to_list/1`. A *direct*
wrong-arity call (`R is host:print_store(1).`) reaches the fixed-arity
procedure on the Scheme side and raises the host's own argument-count
condition, as for every other fixed-arity primitive.


## `library(search)`

`solve/1`, `findall/2`, `fold_solutions/4` and `fail/0` are implemented
on the Scheme backend, along with `library(meta)`'s `run_chr_session/1`
and `run_chr_session_ep/1`. `forall/3`, `find_n/3` and `between/3` are
derived in CHR and needed nothing of their own.

The runtime lives in `scheme/ychr/trail.sls` (a global trail box, undo
thunks, mark/unwind, and the outermost-driver install/restore used by
`dynamic-wind`), plus the search section of `scheme/ychr/runtime.sls`
and the trailing hooks in `var.sls` (variable cells and observer lists),
`store.sls` (growable counts, `alive`/`stored` flags, the store-index
pointer) and `history.sls` (deletions).

Two things on top of the trail are what make a fork correct, and both
are easy to miss:

* The fork shares the store *objects*, not copies of them, so a `'copy`
  search's kills write the caller's own suspension flags. Every exit —
  including an escaping condition — must unwind and deactivate the
  trail; `drive-search` wraps its body in `dynamic-wind` for the normal
  paths and a `guard` for the escaping one.
* `stored` is recorded only on the *first, effective* store, and
  `kill-constraint` writes only `alive` — both matching the reference
  (`Store.hs`'s `storeConstraint` guards on `unless stored` and
  `killConstraint` never touches the flag). A re-store of an
  already-stored suspension is a no-op that Late Storage emits at the end
  of every activation; recording a trail entry for it would let a search
  exit clear `stored` on a suspension still in the store, which both
  defeats `checkUnwatched` (it reads `alive` *and* `stored` together) and
  lets the next re-store append the same constraint twice.

`src/YCHR/Internal/Backend/Scheme.hs` supplies the rest. It emits, into
the generated library's session:

* one `register-goal!` per declared constraint, from the compiler's
  symbol table (the only place arities are recorded), keyed by the
  mangled functor and arity a compiled term carries. Every declared
  constraint is registered, not only exported ones: a choice point's
  alternatives routinely name module-internal constraints the compiler
  lifted out of a `;`;
* one `register-short-export!` per exported `(name, arity)`, which is
  the driver's `resolveByExport` precomputed;
* the inert-type vector, as `%make-session`'s fifth argument. Honouring
  it is what keeps a deep search linear: an inert type's suspensions
  register no observers, so a rule-less choice point costs nothing at
  every later binding.

The search entry points are all in `sessionHostCalls`, so the code
generator threads the session into each of them.

Every search-related golden directory now runs on the Scheme backend,
along with `state_run` and `run_chr_session_test`. The compile-negative
directories need no entry: the harness discovers cases from `.goal` files
and they have none.


## `deep-eval` host-call lookup ignores arity

Both deep evaluators dispatch in the same three tiers: the evaluables
table, the host-call registry under the raw functor (a bare name built
by `quote`), and the host-call registry under the bare name of a
`host:` term. The last tier matches the /mangled/ functor
structurally — the vmName `host__F` — so an unqualified atom that
merely reads `host:F` is never promoted to a host call
(`Interpreter.hostCallName` on the Haskell side, `host-bare-name`
plus `evaluable-key-proc` in `scheme/ychr/runtime.sls`).

What remains divergent is what happens when the *arity* is not one a
primitive provides. Haskell's `HostCallRegistry` is keyed by name
alone, so once a name is registered the primitive itself reports the
mismatch; the Scheme table (`*prelude-host-calls*`) keys by
`(name, arity)`, so it reports the intended not-evaluable error. Both
a `host:` term and a bare name hit this:

    X = host:'-'(3), R is X.
    X is list_to_compound(quote([copy_term, 1, 2])), R is X.

- **Haskell**: reaches the primitive and reports its own arity error —
  `arithmetic host call: expected 2 numeric arguments of same type, got 1`
  for the first, `copy_term: expected 1 argument` for the second.
  The first is pinned by `test/golden/host_term_wrong_arity/`.
- **Scheme**: no `(- . 1)` / `(copy_term . 2)` key, so it reports
  `is: functor is not evaluable: host:-/1` and `…: copy_term/2`.

Scheme's message is the better one (it matches SWI Prolog's
`type_error(evaluable, F/N)`). Fixing Haskell means keying the registry
by `(name, arity)`, which changes a public type
(`YCHR.Convert.HostCallRegistry`) and so is deferred past 0.1. The
mixed-arity case is therefore the one golden directory in the Scheme
harness's `HASKELL_ONLY` list that pins a divergence rather than a
missing primitive.

Both backends do agree on the *decoded* name in the diagnostic: a
not-evaluable functor prints as `host:-/1` / `m:pair/2` / `pair/2`,
never as the vmName `host__-/2`. Locked by the Haskell golden cases in
`test/golden/is_evaluable_host_term/` and
`test/golden/is_non_evaluable_error/`, and on the Scheme side by
`scheme/test/test-runtime.scm`'s `host functor deep-eval` group.

## Prelude host calls missing from `*prelude-host-calls*`

The table's comment asks for it to be kept in sync with the Haskell
registries (`baseHostCallRegistry`, and the reachable part of
`metaHostCallRegistry`).
`write` and `writeln` were absent, so this used to diverge:

    X = writeln("x"), R is X.

- **Haskell**: prints `x`, then `R = '()'`.
- **Scheme**: used to be `is: functor is not evaluable: writeln/1`.

Both names are now registered with arity 1, and `%write`/`%writeln`
return the unit atom `()` so the bound result is the same value on both
backends. Pinned by `scheme/test/test-runtime.scm`'s `host functor
deep-eval` group.

`__chr_error` remains absent by design: `__` is reserved by the lexer,
so no source program can name it.

`name_base` is absent even though `%name-base` exists, so
`T = host:name_base(foo), R is T.` still reports
`is: functor is not evaluable: host:name_base/1` where Haskell answers
`R = foo`. `print` and `read_term_from_string` were in the same state
and are now registered (see *Closed gaps* below). All of them live in
`metaHostCallRegistry` rather than `baseHostCallRegistry`; the table's
comment now names that registry alongside the base one.


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


## Float pretty-printing uses the host's own format

`pretty-term` renders a flonum with `number->string`, where the
interpreter renders it with Haskell's `show`. The two agree on the
common shapes (`1.5`, `0.1`, `-2.5`, `0.0`) but not on the magnitude
ranges where `show` switches to scientific notation — roughly
`|x| < 0.1` or `|x| >= 1e7`:

| Value | Haskell (`show`) | Scheme (`number->string`) |
|---|---|---|
| `0.01` | `1.0e-2` | `0.01` |
| `0.001` | `1.0e-3` | `0.001` |
| `12345678.0` | `1.2345678e7` | `12345678.0` |

Both Scheme implementations agree with each other (Guile and Chez were
checked), and the difference is in the printer rather than in the
numbers: `decimal`/`tagged` matches and arithmetic results are
unaffected, because `Equal` and the store compare values, not their
rendering. It shows up wherever the printer's text escapes the runtime
— `write_term_to_string/1`, `print/1`, and the binding lines a driver
prints. It pre-dates `write_term_to_string/1`, which merely made it
easy to observe; a port of `show`'s float layout (shortest round-trip
digits plus `show`'s exponent thresholds) would close it, and the
printer is shared, so that is a change of its own.


## Closure pretty-printing does not unwrap the source form

The reference printer unwraps a closure value before rendering it:
`runtimeToPExpr` turns `__closure`(identity, sourceForm, captures…) into
the source form and runs `unquoteToPExpr` over it, which also renders a
0-arity atom whose name looks like a variable (uppercase- or
`_`-initial) as a variable rather than a quoted atom
(`src/YCHR/Internal/Pretty.hs`). `pretty-term` has no such branch, so a
bound closure prints as the internal compound. With a function
`mk(X) -> fun(Y) -> X + Y end.` and
`go(X, R) <=> T is mk(X), R is write_term_to_string(T).`:

    Haskell: R = "fun(Y) -> prelude:(X + Y) end"
    Scheme : R = "'__closure'(pp:'__lambda_0', fun('Y') -> prelude:('X' + 'Y') end, 1)"

The operator port below improved the *inner* source form (it used to
render `'->'('fun'('Y'), prelude:('X' + 'Y'))`), but the wrapper is
still shown. This pre-dates the operator port and no golden case pins
it; closing it needs an `unquoteToPExpr` equivalent in `value->pexpr`
and a `render-pexpr` `var` node, and the printer is shared, so it is a
change of its own.


## Scheme runtime ABI

Reference contract for the boundary between `src/YCHR/Internal/Backend/Scheme.hs`
and the runtime in `scheme/ychr/`. This is not a gap: both sides must satisfy
it, and none of it is scheduled to change. `INVARIANTS.md` §5 records the same
contracts from the invariant side.

- **Import.** Every generated library imports `(ychr runtime)` alongside
  `(rnrs)` (`importClause`), so each runtime name the backend emits has to be
  exported from `runtime.sls`.
- **Session first.** Every generated constraint/function procedure takes `%s`,
  the session, as its first parameter after the name (`compileProcedure`); the
  only exception is the exported session thunk, which is zero-argument. Emitted
  calls thread `%s` explicitly — `compileValExpr (CallExpr …)` produces
  `(proc %s arg …)`.
- **Tail values vs `call/cc`.** A procedure whose `Return`s can only leave it
  from tail position compiles to a plain value-producing expression
  (`compileTailStmts`). Only a `Return` trapped inside a `Foreach` or
  `DrainReactivationQueue` body keeps a `call/cc` escape
  (`needsEscape`/`wrapReturn`, emitting `(call/cc (lambda (%return) body #f))`);
  a tail expression over `maxTailExprNodes` falls back to the same escape.
  `compileStmt (Return e)` is `(%return <value>)`.
- **`Break`/`Continue`.** Each gets its own `call/cc` at the loop that owns the
  label, and only when the loop body actually names that label
  (`hasBreak`/`hasContinue`). `Break` wraps the whole `Foreach` (continuation
  parameter `breakName lbl`); `Continue` wraps one iteration inside the alive
  check (parameter `continueName lbl`).
- **Session thunk.** The exported zero-argument thunk calls
  `(%make-session N POSITIONS TABLE TYPES)`: `N` is the program's type count,
  `POSITIONS` is `indexPositionsSExpr`'s alist of `(cons TYPE (list POS …))`
  entries (or `(list)` when nothing is indexed), `TABLE` is
  `(make-op-table (quote ((FIXITY TYPE "name") …)))` over `opTableEntries`, and
  `TYPES` is `typeNamesSExpr`'s `(vector …)` of one mangled `vmName` per
  constraint type in index order, which `print_store` and
  `write_store_to_list` split at the first `__` to label a stored constraint.
  `%make-session`'s shorter clauses install the unindexed store (`'()`),
  `builtin-op-table` and the empty type-name table for the arguments not
  supplied.
- **Queue drain.** `DrainReactivationQueue` emits
  `(drain-queue! %s (lambda (sv) (when (alive-constraint? sv) …)))`: the
  runtime's `drain-queue!` takes `(session, callback)` and calls the callback
  on every dequeued constraint id, so the liveness check lives in the generated
  lambda rather than the runtime.
- **Snapshot shape.** `Foreach` destructures two values from the runtime with
  `(let-values (((%vec %count) CANDIDATES)) …)`; both `store-snapshot` and
  `candidate-suspensions` return `(values storage count)`.
- **`If` fall-through.** In the tail compilation an `If` with a `Return` in an
  arm is emitted as `(if c ARM-spliced-before-rest ARM-spliced-before-rest)`,
  so a binder an arm introduces lexically scopes over the statements after the
  `If`. That matches the interpreter's flat mutable `Env`, and is sound only
  because no emitted `If` leaves a name in the rest that an arm bound; see
  `INVARIANTS.md` §5, "Two properties of emitted code are what make that
  reading sound", rather than restating the argument here.
- **Binding printer.** `pretty-term` renders operators from the fixed
  `pretty-ops` table (`builtin-op-entries` plus the standard arithmetic
  entries), the port of `Pretty.prettyOps`, not the session's `op-table`, so a
  user-declared operator still prints as a compound.


## Closed gaps (reference)

The following used to live here and are now closed. Kept as a brief
record of which fixes have already shipped.

- **`library(search)`** — `solve/1`, `findall/2`, `fold_solutions/4`,
  `fail/0`, `run_chr_session/1` and `run_chr_session_ep/1` were bound
  stubs raising `not implemented`, and eleven `search_*` directories
  plus `state_run` were in `HASKELL_ONLY`. They are now implemented on
  top of `(ychr trail)` and the search section of the runtime; see
  *`library(search)`* above for the design and the three cases that
  still diverge.

- **`print_store` / `write_store_to_list`** — the two meta primitives that
  expose the store were bound stubs raising `not implemented`, and
  `write_store_to_list_test` was in `HASKELL_ONLY`. They are now
  `%print-store` / `%write-store-to-list` on top of the port of
  `getAllStoredConstraints`: every alive constraint, grouped by constraint
  type in ascending index order and, within a type, in store order, with
  each argument deeply dereferenced (`deep-deref`, the port of
  `deepDeref`). `print_store` renders each value with the shared
  `pretty-term` on its own line and returns the unit atom;
  `write_store_to_list` returns them as a list, the empty store being
  `[]`. Both need the session, so `Scheme.sessionHostCalls` grew both
  names and `scheme/test/test_golden.py`'s
  `test_gen_driver_host_call_mapping` pins the driver's
  `(%print-store %s)` / `(%write-store-to-list %s)`.
  *Value shape*: `constraint-value` is a direct port of the reference's
  `constraintAsValue` — an unqualified type is the type name applied to
  its arguments, a qualified one the surface `:` compound
  (`m:c(1)`), never the mangled `m__c` functor a compiled term of the
  same spelling carries. That choice is the reference's, and it has the
  same consequence there: a value from `write_store_to_list` does not
  unify with the equivalent written term on either backend
  (`R is write_store_to_list(), R = [m:c(1)]` fails on both). Printing,
  which is what the golden harness compares, is identical either way.
  *Type names*: the session grew an immutable `type-names` field and
  `%make-session` a fourth argument, `typeNamesSExpr`'s `(vector …)` of
  the compiler's mangled `vmName` for each entry of
  `CompiledProgram.typeNames`, in index order. The runtime splits an
  entry at the first `__` (`split-mangled-name`, the same decode the
  printer applies to a functor), so the table travels in the one encoding
  that inverts unambiguously even for a quoted base name containing `:`;
  a hand-built session with no table falls back to the `c#type_N` label
  `constraintTypeLabel` uses. That fallback is a deliberate Scheme-side
  extrapolation: the reference iterates its own type-name table, so a
  session built without names has no store buckets and cannot reach the
  case at all, while `make-store-by-type` always creates one bucket per
  type. The shorter `%make-session` clauses keep loading older generated
  libraries and the hand-built test sessions.
  `write_store_to_list_test` left `HASKELL_ONLY`; the new
  `test/scheme/test_golden.py::test_meta_print_store_end_to_end` pins
  `print_store`'s stdout (no shared golden case is possible — the Haskell
  runner compares bindings only, while the Scheme runner compares all of
  stdout), `scheme/test/test-runtime.scm` pins both primitives directly
  (ordering, dead-constraint filtering, the `:` compound, deep
  dereference, 0-arity constraints, an indexed bucket and the fallback
  label), and `test/YCHR/Backend/SchemeTest.hs` pins the emitted
  type-name vector.
  Neither name joined `*prelude-host-calls*`: only their `(name, 0)` key
  is unreachable (a nullary `host:` compound is an atom on both
  backends), and a `host:` term at arity ≥ 1 is the separate,
  pre-existing *deep-eval host-call lookup ignores arity* divergence
  recorded above, not something this port changes.

- **`write_term_to_string`** — the Scheme procedure was a stub raising
  `not implemented`, and no golden test covered it at all. It is now
  `%write-term-to-string`, a one-line call to the shared `pretty-term`
  (the port of `prettyTerm`), the counterpart of the reference's
  `prettyValue`: `write_term_to_string/1` is declared `(any) -> string`,
  so nothing is classified — an unbound variable is a *success* that
  renders `_`, as `valueToTerm` does for a variable with no alias — and
  the argument is dereferenced by the printer, so no session is
  threaded (`sessionHostCalls` deliberately does not grow the name).
  The name joined `*prelude-host-calls*` at arity 1, so
  `T = host:write_term_to_string(1), R is T.` is deep-evaluable like
  `host:read_term_from_string`; at any other arity it still reports
  `is: functor is not evaluable: host:write_term_to_string/N`, the
  `(name, arity)` keying all the table's entries share. The new
  `test/golden/write_term_test/` directory pins the host-call path on
  both backends (compound, string-literal quoting, the unbound case,
  and an improper list), and `scheme/test/test-runtime.scm` pins the
  primitive directly, including its `deep-eval` route. The one printer
  divergence left is flonum rendering (see *Float pretty-printing*
  above), which pre-dates this call and is shared by `print/1`.

- **`read_term_from_string`** — the Scheme procedure was a stub raising
  `not implemented`, and the whole `read_term_test` directory was in
  `HASKELL_ONLY`. It is now a port of the reference reader: the new
  `(ychr read)` library carries the Pratt parser of
  `YCHR.Internal.PExpr`, and
  converts the parse the way `convertTerm` + `termToValue` do — a named
  variable is one fresh logical variable shared between its occurrences,
  `_` is fresh per occurrence, `true`/`false` (and the `prelude:` forms)
  are native booleans, a 0-arity name is an atom, and a `module:name` is
  kept in the reference's colon spelling rather than the compiler's
  mangled form. `runtime.sls`'s `%read-term-from-string` wraps it: a
  non-string argument is classified by `%arg-error` (unbound ⇒
  instantiation, bound wrong type ⇒ general), while a parse failure is a
  general error and so stays fatal in a soft guard. The name joined
  `Scheme.sessionHostCalls` so the session is threaded for the fresh
  variables, and `*prelude-host-calls*` at arity 1 so a
  `host:read_term_from_string` *term* is deep-evaluable as well.
  `read_term_test` left `HASKELL_ONLY`; the reader is pinned directly by
  `scheme/test/test-runtime.scm`, including its `deep-eval` route.
  (The reference reader's table later became program-dependent — it
  reads `SessionEnv.opTable` rather than `builtinOps` — which the Scheme
  reader now does too; see *`read_term_from_string` ignores the
  program's operators* under *Closed gaps*.)
  One deliberate classification divergence remains: the interpreter's
  name-keyed registry reports a *general* error for any non-text
  argument, whereas the Scheme primitive treats an unbound one as an
  instantiation failure, so `p(S) <=> boolean(read_term_from_string(S)) |
  out(1).` delays on `p(Y)` here and aborts there. That is the same
  choice every other strict Scheme primitive makes (see *Soft guard
  failure*): an argument that must be there but is not is exactly what a
  soft guard is for.

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
- **`host:` terms in data position were not deep-evaluable** — a
  `host:` call stored in a term keeps the vmName `host__F` as its
  functor, and both runtimes looked that raw functor up in a registry
  keyed by the bare name `F`, so `T = host:'+'(1, 1), R is T.` raised
  `is: functor is not evaluable: host__+/2`. The Haskell
  `invokeByKey` and the Scheme `deep-eval-value` now decode the functor
  before the fallback, and both render the diagnostic from the decoded
  name. `write/1` and `writeln/1` were also added to
  `*prelude-host-calls*` (and made to return the unit atom), closing
  the `writeln/1` divergence above. Pinned by
  `test/golden/is_evaluable_host_term/` (two cases, run on both
  backends) and by the `host functor deep-eval` group in
  `scheme/test/test-runtime.scm`.
- **`ground/1` in goal queries with nested unbound vars** — never a
  runtime gap: the Scheme `%ground?` was correct all along. The
  generated driver collected goal variables over the *top-level*
  arguments only (`nub [n | VarTerm n <- constraint.args]` in the old
  `YCHR.Backend.SchemeDriver`), so a variable nested inside a compound
  argument (then spelled `p(1, X)`, today `quote(p(1, X))`) was
  emitted as a bare identifier that no `let*` declared, and Guile
  rejected the script with `Unbound variable: X` before any constraint
  ran. Already fixed when
  `0c50265` ("Evaluate constraint arguments") rewrote `generateDriver`
  to take `[R.Expr]` and collect variables with the structural
  `exprVars`. Closed the `HASKELL_ONLY_CASES` entry for
  `("type_predicates", "grd_no")`; the driver-side invariant stays
  pinned without Guile by
  `test/scheme/test_golden.py::test_gen_driver_nested_goal_var_declaration`.
- **`print/1`** — the host-call wiring existed (`hostCallMap` already
  mapped `print` to `%print`), but `%print` was
  `(display v) (newline)`, so a compound printed as a Scheme record
  (`#<term functor: …>`), a string printed unquoted, a list printed as
  a cons record, and the call returned the unspecified value of
  `newline` instead of the unit atom. `print` was also absent from
  `*prelude-host-calls*`, so the `is`-on-a-variable path diverged:
  `T = host:print(1), R is T.` printed `1` and bound `R = '()'` on
  Haskell, but reported `is: functor is not evaluable: host:print/1` on
  Scheme. `%print` now renders each argument through `pretty-term`
  (the Haskell `prettyTerm`) on its own line and returns the unit atom,
  and `print/1` is registered in the prelude table, so both the
  `meta:print/1` wrapper and direct `host:print(...)` calls agree with
  the Haskell interpreter on the printed lines and the returned value
  (the unit atom now renders as `'()'` on both backends; see *Closed
  gaps* — atom pretty-printing). The direct path is variadic, matching
  Haskell's name-keyed registry; `print` at arities other than 1 is
  still not deep-evaluable, the same `(name, arity)`-keying divergence
  as `host:-/1`. Pinned by the `%print` and `host functor deep-eval`
  groups in `scheme/test/test-runtime.scm` and by
  `test/scheme/test_golden.py::test_meta_print_end_to_end` (no shared
  golden case is possible: the Haskell runner compares bindings only,
  while the Scheme runner compares all of stdout).
- **Atom pretty-printing** — `pretty-term` emitted atoms via
  `symbol->string` with no quoting, so `'hello world'`, `'你好'`,
  `mymodule:'£foo'`, the unit atom `'()'`, uppercase-leading and
  symbolic atoms, and embedded quotes all lost their surface spelling
  (`hello world`, `你好`, `mymodule:£foo`, `()`, `Abc`, `+`, `a'b`).
  The printer now ports `needsQuoting`/`renderAtom`
  (`src/YCHR/Internal/PExpr.hs`): a non-empty bare lowercase identifier
  of letters, digits and underscores stays bare unless it collides with
  a word operator of the fixed `prettyOps` table (`fun`, `is`,
  `chr_constraint`, `div`, …, so `'is'` prints quoted) or contains
  `__`; anything else is wrapped in `'…'` with each embedded `'`
  doubled and with `\\`, `\n` and `\t` escaping a backslash, newline and
  tab (the pairs the reader decodes; without the backslash escape the
  emitted atom would not read back as the same name). The predicate
  uses `char-general-category` (via
  `(rnrs unicode)`) rather than `char-alphabetic?`/`char-numeric?`,
  because Haskell's `isAlphaNum` also covers the `Nl`/`No` categories:
  `a²` and `aⅧ` must stay bare on both backends. Quoting is applied per
  segment — the module and base halves unmangle independently, as
  Haskell renders them through separate `renderAtom` calls — so a
  mangled `mymodule__%%u0000a3foo` prints `mymodule:'£foo'`, never
  `'mymodule:£foo'`. `decode-mangled-name` still renders the unquoted
  decoded name, so diagnostics (`is: functor is not evaluable:
  host:-/1`, `m:pair/2`) are unchanged. Closed the
  `HASKELL_ONLY_CASES` entries for the three `unicode_atoms_strings`
  cases and for `("qualified_unicode_ctor", "pound_foo")`. The shared
  rule is pinned by the new `test/golden/atom_quoting/` directory (unit
  atom, word operator, uppercase lead, embedded quote, symbolic atom,
  and the `Nl`/`No` non-regressions) and, on the Scheme side alone, by
  the `pretty-term quotes atoms like renderAtom` group in
  `scheme/test/test-runtime.scm`.

- **`read_term_from_string` ignores the program's operators** — the
  Scheme reader parsed with the built-in table only, so a string
  spelling an operator the program had (the prelude's `+`, a declared
  `&&&`) was a parse error there while the interpreter read it. The
  table now travels the reference's path. The new `(ychr optable)`
  library owns the table (`#(INFIX PREFIX WORD)`), its `builtinOps`
  transcription as `(fixity type name)` entries, `make-op-table` and
  the lookups. `YCHR.Internal.Backend.Scheme` emits the program's merged
  table (`CompiledProgram.opTable`) as a
  `(make-op-table (quote ((FIXITY TYPE "name") …)))` literal — the
  analogue of the embed generator's `PExpr.mkOpTable` literal — in the
  session thunk, as `%make-session`'s third argument. The session record
  gains an immutable `op-table` field (`session-op-table`), and every
  parser procedure of `read.sls` takes the table as its first argument,
  mirroring `PExpr`'s `OpTable ->` threading; `parse-term` reads it from
  the session. `%make-session`'s one- and two-argument clauses install
  `builtin-op-table`, the counterpart of the `builtinOps`
  `initSessionEnv` gives the reference's hand-built sessions, so
  `scheme/test/test-runtime.scm`'s "a prelude operator is not readable"
  case still holds for a hand-built session; a new group pins a session
  that carries a program table. The printer had to follow: `pretty-term`
  rendered every compound as `functor(args)`, so the reader fix alone
  would have read `1 + 1` but printed `'+'(1, 1)` where the reference
  prints `1 + 1`. `(ychr pretty)` now ports `prettyPrec`/`prettyOps`
  over a `runtimeToPExpr`-shaped intermediate — infix/prefix/postfix
  with precedence-based parenthesization, the `:`/`,`/`;` spacing rules,
  the `fun(…) -> … end` lambda form and argument-precedence list
  elements — while keeping the fixed built-ins-plus-arithmetic table
  `prettyTerm` uses, so an operator a program declares still prints as a
  compound. `("read_term_test", "arith_op")` left
  `HASKELL_ONLY_CASES`, and the new `declared_op` case
  (`op(500, yfx, '&&&')` exported by `read_term_test.chr`, expected
  `R = '&&&'(a, b)`) pins both halves on both backends. The emitter is
  pinned without Guile by `test/YCHR/Backend/SchemeTest.hs`'s "the
  generated library threads the program's operator table"; the printer
  by the `pretty-term renders operators like prettyTerm` group in
  `scheme/test/test-runtime.scm`.
