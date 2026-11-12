# Scheme Backend Gaps

This document lists known divergences between the Haskell interpreter (the
reference implementation) and the Scheme backend, as surfaced by the golden
test suite. Each gap is a candidate fix; resolving one usually means removing
an entry from `HASKELL_ONLY` or `HASKELL_ONLY_CASES` in
`test/scheme/test_golden.py`.

The scope is the Scheme backend (`src/YCHR/Internal/Backend/Scheme.hs`) plus its
runtime in `scheme/ychr/`. Goals are run through `guile3.0 --r6rs` per
`Makefile`'s `test-scheme` target.


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
(`YCHR.Convert.HostCallRegistry`), so it is deferred.
`host_term_wrong_arity` is in the Scheme harness's `HASKELL_ONLY`
list for this reason.

Both backends do agree on the *decoded* name in the diagnostic: a
not-evaluable functor prints as `host:-/1` / `m:pair/2` / `pair/2`,
never as the vmName `host__-/2`. Locked by the Haskell golden cases in
`test/golden/is_evaluable_host_term/` and
`test/golden/is_non_evaluable_error/`, and on the Scheme side by
`scheme/test/test-runtime.scm`'s `host functor deep-eval` group.

## Record types are never freed

Mostly closed. Open only for qualified functors made at run time.

A functor whose name holds `__` (`m__f`, `__closure`) gets its own
record type per arity ("Flat compounds" below), and nothing frees it:
the type, its uid, its constructor and predicate, and the
`compound-type` table entry stay for the life of the process. The uid is
what pins it. Measured on Chez 10.3: a nongenerative type with no table
entry at all still keeps about 560 bytes, and an ephemeron table does
not help. A generative type in an ephemeron table is freed, but it can't
be written with fasl and can't be the type a library defines statically.

So only those names get a type. Any other functor (`foo`, and what
`list_to_compound`, `=..` or `read_term_from_string` usually build)
shares one record type per arity, with the functor in a field. Measured
on Chez 10.3 with 100000 new functors, each built once and dropped:

| | bare (`f1`, `f2`, …) | qualified (`m__f1`, …) |
|---|---|---|
| memory kept per functor, before | 642 bytes | 656 bytes |
| memory kept per functor, now | 0 | 656 bytes |
| time for its first term, before | 6.8 µs | 4.8 µs |
| time for its first term, now | 0.2 µs | 4.3 µs |

What it costs: a bare term has one more field, so it is 16 bytes bigger
at odd arities (Chez rounds a record to 16 bytes; even arities are the
same size). Generic code is as fast as before on both kinds.

What is left: a program that keeps reading new *qualified* names
(`m:f1(…)`, `m:f2(…)`, …) from open-ended input still grows, about 656
bytes per name. Qualified names normally come from declarations, so this
needs data that invents module-qualified functors. Closing it would take
a registry of the functors loaded libraries define, plus a way to deal
with a library loaded after terms of its functor exist. Not planned.

## Host calls left out of `*prelude-host-calls*`

The table mirrors the Haskell registries (`baseHostCallRegistry`,
the reachable part of `metaHostCallRegistry`, and the search
entries).

`print_store` and `write_store_to_list` are left out on purpose. Their
only arity is 0, and a nullary `host:` compound is an atom on both
backends, so the deep evaluator never asks for that key. At arity ≥ 1
they hit the arity gap above.

`__chr_error`, `__chr_inst_error` and `__chr_is_unbound` are out by
design: the lexer reserves `__`, so no source program can name them.


## Numeric primitives accept more than Haskell's

The Scheme numeric primitives succeed on operand combinations the
Haskell registry rejects. Failure classification already matches;
only the accept set differs. Left alone because tightening it can move
golden output.

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


## `library(search)` implementation notes

Not a gap: the search driver runs on both backends. These notes cover
how the Scheme side does it. `solve/1`, `findall/2`,
`fold_solutions/4`, `fail/0`, `run_chr_session/1` and
`run_chr_session_ep/1` are runtime primitives; `forall/3`, `find_n/3`
and `between/3` are derived in CHR.

The runtime lives in `scheme/ychr/trail.sls` (a global trail box, undo
thunks, mark/unwind, and the outermost driver's install/restore),
plus the search section of `scheme/ychr/runtime.sls`
and the trailing hooks in `var.sls` (variable cells and observer lists),
`store.sls` (growable counts, `alive`/`stored` flags, the store-index
pointer and every index entry filed while a search is active) and
`history.sls` (deletions).

Two things on top of the trail are what make a fork correct, and both
are easy to miss:

* The fork shares the store *objects*, not copies of them, so a `'copy`
  search's kills write the caller's own suspension flags. Every exit —
  including an escaping condition — must unwind and deactivate the
  trail; `drive-search` does both on its normal return and in a `guard`
  that re-raises an escaping condition. No continuation escape crosses
  the host call, so a `dynamic-wind` would add nothing.
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
  `(%make-session N POSITIONS TABLE TYPES INERT)`: `N` is the program's type count,
  `POSITIONS` is `indexPositionsSExpr`'s alist of `(cons TYPE (list POS …))`
  entries (or `(list)` when nothing is indexed), `TABLE` is
  `(make-op-table (quote ((FIXITY TYPE "name") …)))` over `opTableEntries`, and
  `TYPES` is `typeNamesSExpr`'s `(vector …)` of one mangled `vmName` per
  constraint type in index order, which `print_store` and
  `write_store_to_list` split at the first `__` to label a stored constraint,
  and `INERT` is `inertTypesSExpr`'s vector marking the inert types.
  `%make-session`'s shorter clauses install the unindexed store (`'()`),
  `builtin-op-table`, the empty type-name table and no inert types for the
  arguments not supplied.
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
- **REPL exports.** The generated library also exports the mangled tell
  procedure of every exported constraint and `reactivate_dispatch`. The
  REPL's Chez backend evaluates compiled query code outside the library,
  so it reaches those procedures through the export list. This is the
  only addition to the export surface.
- **Chez query ABI.** `scheme/ychr/repl-server.scm` imports the fixed
  library `(ychr generated repl)` and evaluates one expression per stdin
  form in `(interaction-environment)`. A generated query is a single
  expression, not a sequence of top-level definitions, because Chez's
  `eval` rejects a `define` in expression position; query-time lifted
  lambdas are `letrec` bindings and are registered with
  `register-callable!`. The expression uses the server's `%s` session,
  `fresh-session`, `start-timer`, `report-timer` and `(ychr pretty)`'s
  `pretty-query-result`. User output and bindings go to stdout (inherited
  by the REPL); one `YCHR-REPL-OK` or `YCHR-REPL-ERR <escaped>` frame per
  query goes to stderr.
- **Lists are native.** A `prelude__.`/2 cell is a Scheme pair and the
  atom `prelude__[]` is `'()`; every other compound is a flat record (next
  item). The backend emits `cons`, `'()`, `pair?` and
  `null?` for these (`makeTermSExpr`, `compileAtom`, `matchTermSExpr`), and
  the runtime's `make-term` builds a pair for that functor too, so a cons
  cell has one spelling. `term?`/`term-functor`/`term-arity`/`term-arg`
  treat a pair as a 2-ary `prelude__.` term, so generic code needs no pair
  case.
  Since `'()` is not a symbol, code that asks "is this an atom" must use
  `chr-atom?`, and code that builds an atom from a name must use
  `symbol->atom`. Only the canonical spellings map: the bare `.`/2 and
  `[]` the string reader builds stay a record and a symbol, distinct
  values as they are on the Haskell side.
- **Flat compounds.** A compound of arity 1..8 is a record whose type
  is a child of `compound1` … `compound8` (the arguments as fields);
  above 8 its type is a child of `compound*` (a vector of arguments).
  The functor's name picks the child (`scheme/ychr/var.sls`, "Functor
  types"), and nothing else does, so every library, process and fasl
  file agrees:
  - *Typed*, a name that holds `__` (`m__f`, `__closure`): a child per
    functor, sealed, no fields of its own, named after the functor, so
    the functor is the type's name and not a field. Above 8 one child
    per functor covers every arity, and the vector length is the arity.
    `compound-type` makes a child the first time it is asked for and
    caches it; its uid is fixed by functor and arity
    (`ychr:c2:m__f:1`). It keeps the last functor asked for per arity,
    so a run of terms of one functor skips the table.
  - *Bare*, any other name: the shared child `dyn1` … `dyn8` or `dyn*`
    of its arity, sealed, with the functor in one extra field. All nine
    are named `ychr:dyn`, which is how `compound-functor` tells them
    from a typed child. No table, nothing kept per functor (see "Record
    types are never freed" above for why).

  `compound?`, `term-arity` and `term-arg` test the parents;
  `term-functor` reads the type's name, or the field of a bare term;
  unification compares the two record types, and the functors too when
  the type is a bare one; `term-map` rebuilds arities 1–3 without a
  vector.
  A generated library defines the type of each typed functor it builds
  or tests with `define-record-type`, under the same uid
  (`hoistFunctorTypes`, `functorDefinitions`), so Chez inlines the
  constructor and predicate. That needs a functor that is an identifier
  and holds `__` (no imported name does), of arity
  1–8, since the functor is the record name; a
  functor used at several arities (`__closure`) is static at its first
  one only. The others, and a query, look their constructor and
  predicate up once (`compound-constructor`, `compound-predicate`; for a
  bare functor these are closures over the shared type); a
  driver goes through the by-functor `make-compoundN`. `get-arg` stays
  generic. A looked-up closure is not inlined: it made `size/ground`
  about twice as slow and the `terms` benchmark 7–9% slower, which is
  why the static definitions exist. `ychr scheme-types` writes its
  static definitions in a separate records library: Guile only accepts
  one in a library that imports `(rnrs)` without a prefix (its expansion
  uses plain `quote`), and the types library imports it with one.
  On Chez a typed term is the size of a native record of the same
  arity; a bare one has one more field. Guile checks a parent type by
  walking the ancestry, about 4.5 times a sealed check, so generic term
  code is slower there. The parents and the bare types are nongenerative
  (`ychr:compound2:3`, `ychr:dyn2:1` and so on, plus `ychr:var:1`), so a
  ground term written with Chez's `fasl-write` reads back in another
  process (`test/scheme/test_fasl.py`). Bump a uid's suffix when its
  layout changes. The parents went from `:2` to `:3` when bare functors
  moved to the shared types, so a file written before that is not
  read as current terms: its types have the old parents, and Chez
  raises "incompatible record type" when the same functor's type is
  asked for with the new one.
- **No wrapper that can do nothing.** The backend builds `deref`,
  `%bool-from-value` and `equal?/chr` calls through `derefS`,
  `boolFromValueS` and `equalS` (`Backend/Scheme.hs`), which leave the
  call out when it cannot change the result:
  - `(deref e)` is `e` when `e` is a literal, another `deref`, or a call
    of a runtime procedure that returns a number, a string or a boolean
    (`plainResultProcs`, `booleanProcs`).
  - `(%bool-from-value e)` is `e` when `e` is `#t`, `#f` or a call in
    `booleanProcs`.
  - `(equal?/chr a LIT)` is `(eqv? (deref a) LIT)` for a number, boolean
    or symbol literal on either side, which is what `equal*` does for
    those. This covers both `BEqual` and the `==` host call.

  A procedure may be added to one of the two sets only if it can never
  return a variable (or, for `booleanProcs`, anything but a boolean);
  raising is fine. A `Foreach` index condition goes through `equalS`
  too, and a driver leaves the `deref` out the same way (`derefArg` in
  `Backend/SchemeDriver.hs`).
  On Chez, three interleaved rounds: `sum` about 30%
  faster (0.07 to 0.05 ms), `fib` 12% (1.14 to 1.01 ms), `terms` about
  10%, `copy` about 4%, the others unchanged.
- **Query-scope dynamic tell.** `%tell-term` special-cases the compiler's
  `<query>` scope: it resolves the goal through the program's exports
  (`resolve-export` + the session's goals table), as the Haskell
  `tellGoalConstraint` does, instead of using the module-scoped tellables
  table. Rule-body tells are unchanged. The unbound and not-a-term
  messages carry the Haskell `CHR runtime error: ` prefix only in that
  query scope.
