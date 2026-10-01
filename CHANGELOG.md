# Revision history for ychr

## Unreleased

The Scheme backend now implements the paper's *Indexing* optimization
(§5.3), the same one the Haskell runtime gained earlier, with the same
interface and the same on-demand threshold. The compiler was already
emitting the `Foreach` index conditions its guard equalities imply; a
generated loop now answers such a condition from a key bucket plus the
position's non-ground fallback set instead of scanning the whole type
bucket, exactly as the interpreter does. The compiler emits the
`(constraint type, argument position)` pairs the program looks up through
an index condition (`YCHR.Internal.VM.Index.indexablePositions`) as a
second argument to `%make-session`; the session files every store whose
type has such a position once the type's bucket reaches `indexThreshold`,
and a `Foreach` whose condition can drive the index is compiled to a
loop-entry lookup that hands the first usable key to
`candidate-suspensions`.

The index may only narrow the iterator, never lose a candidate. A
suspension is filed under a key only when its indexed argument was fully
ground when it was stored — a suspension stored with an unbound argument
goes to the position's fallback set, which every lookup for that position
scans, and binding that argument later does not move it — and candidates
stay in ascending store order, so rule-firing order is unchanged. A
lookup whose type has not reached the threshold, whose condition names a
position the store does not index, or whose candidate set would not be
smaller than the whole bucket is the `store-snapshot` scan it was before.
A condition may only be evaluated eagerly at loop entry if it is total:
`nonRaising` moves to `YCHR.Internal.VM.Index` for this (the interpreter
keeps the same predicate over its slot AST, and the build's exhaustiveness
checks keep the two in step), and the generated code short-circuits the
key bindings on the type's index state, so an unindexed type evaluates no
condition at all.

Keys are ordinary Scheme data compared with `equal?` — `(num . n)`,
`(atom . s)`, `(text . s)`, `(bool . b)`, and a structural
`(term functor key …)` — normalized so that key equality is never finer
than ask-equality (`equal?/chr`): `0.0` and `-0.0` share a key even though
`eqv?` distinguishes them, and every NaN shares one. Terms are keyed by
functor and arguments, never by identity: `equal?` on a record would
compare by identity, and a bucket keyed that way could never be found.
The Scheme runtime has no search driver, so unlike the Haskell index it
has no snapshot or undo counterpart; `dev-docs/INVARIANTS.md` records that
one must capture and restore it with the store if a search driver ever
lands.

Measured on this machine by interleaving three default rounds of the Guile
suite against a build of the parent commit (min ms, median of the three
rounds): `leq_closure`, the store-heavy transitive closure whose `leq`
bucket reaches the hundreds, falls from 199.8 ms to 70.3 ms — **−65%**
(medians 200.0 → 70.6 ms). Everything else is within the suite's
run-to-run spread except `graph`, a sub-millisecond case whose types stay
below the threshold: it pays the one per-loop type-index check and goes
0.29 → 0.31 ms median (≈20 µs, +7%) — nothing measurable on Chez — while
the case that does index saves ≈130 ms per iteration. On Chez Scheme the same rounds give `leq_closure`
1.81 → 0.69 ms (**−62%**) with every other case unmoved. The Haskell
suite is unchanged: the VM and the interpreter are untouched apart from
the shared `nonRaising` move.

No change to the emitted VM, its serialization or its format version: the
index is a runtime-only implementation of the `Foreach` interface. The
Scheme runtime gains `scheme/ychr/store.sls`'s index
(`index-threshold`, `make-index-positions`, `make-store-index`,
`indexed-positions-for`, `candidate-suspensions`) and
`scheme/ychr/var.sls`'s `ground-key` / `add-observer-and-key` (one
traversal per stored argument registers the observers *and* computes an
indexed argument's key). `%make-session` gains an optional second
argument — the compiler-emitted position alist — with a one-argument
`case-lambda` clause so hand-built sessions (the unit tests) keep working
and simply do not index; the session record gains `index-positions` and
`store-index`. `test/golden/index_ground_fallback` gains a `compound`
goal (a lookup keyed by a ground compound) and now exercises the indexed
path on the Scheme backend too, and `scheme/test/test-index.scm` pins the
candidate lists and key normalization directly.

The Haskell interpreter no longer runs the VM AST. It runs a second,
interpreter-owned AST — the new `YCHR.Internal.Interpreter.Slots` — in which
every local variable is a per-procedure integer slot, and its local
environment is an `IntMap` keyed by that slot instead of a `Map` keyed by
`Name`. The VM identifies a local by name because that is what the code
generation backends need: `YCHR.Internal.Backend.Scheme` emits a
target-language binder per local (`let (mangle-name n) …`, and a `let`
for a `Foreach` loop variable), where the target's own lexical
addressing already does what a slot does and where the emitted
identifier has to be a name anyway; the planned JavaScript backend is a
code generator too. A tree-walking interpreter is the one backend that
maintains a per-call environment itself, and it was paying a `Text`
comparison and a `Map` rebalance for every variable access and every
binding.

The phase is total and structure-preserving: every VM `Stmt`, `ValExpr`,
`BoolExpr`, `IdExpr` and `CallArg` constructor has exactly one
counterpart, and the lowering rewrites nothing but the local-variable
references and binders. A VM constructor added without its counterpart
makes the lowering non-exhaustive — a compile error under
`-Wall -Werror` — which is what keeps the phase from going silently
stale. A name the walk cannot place gets a fresh slot that nothing
binds, so the interpreter still reports its own "unbound variable"
runtime error rather than the phase failing. Slots are numbered from one
counter per procedure, shared by both kinds, because a parameter is
heterogeneous at run time: `bindParams` binds by the runtime tag of the
argument it is handed, so parameter *i* must be slot *i* whether the
value lands in the value map or the id map.

The phase is derived once at compilation and carried lazily on
`CompiledProgram.slotProgram`, in the same place as `indexPositions` and
for the reason those lazily derived fields exist: a session is created per goal, and the
compiled type-checker is 901 procedures (856 KB of serialized VM), so
lowering per session would rewrite the program before a short goal had
done any work. `SessionInput` gains `slotProgram` in place of its
procedure table, and query-time lifted lambdas are lowered with
`lowerProcedure` before they are merged into the session's procedure
map. `YCHR.Internal.Runtime.Monad`'s `ProcMap` is now
`Map Name SlotProc`, and `YCHR.Internal.Runtime.Interpreter.bindParams`
takes the callee's arity rather than its parameter-name list.

Measured on this machine by interleaving the benchmark binary against
one built from the parent commit, three rounds a side (the same setup
`dev-docs/PROJECT.md` describes; each side's own spread is under 2.5%):
every benchmark is faster and none is slower. `typecheck/pairs_library`
372.8 ms → 324.0 ms median, **−13.1%**; `leq_closure` 17.89 → 16.16 ms
(−9.7%); `fib` 1.103 → 0.981 ms (−11.1%); `graph_test` 124.2 → 108.2 µs
(−12.9%); `sum_list_test` 33.86 → 29.41 µs (−13.1%); the four search
benchmarks −5% to −6%; `guard` −3.9% and `leq` −0.8%. The fine profile
(`ychr check typechecker/*.chr +RTS -p`, `-fprof-auto`) goes from 25.33 s
and 20.93 GB to 18.16 s and 19.30 GB, with `Text` comparison down from
9.3% of individual time to 4.7%, `bindParams` 4.0% → 1.8%, `insertVal`
3.8% → 1.8%, and `Map`'s `balanceL`/`balanceR` gone from the report.

No change to the emitted VM, its serialization or its format version, and
no change to the Scheme backend or its runtime: the phase is a private
view the Haskell interpreter owns. This is the one compiler-to-runtime
import edge in the tree — `YCHR.Internal.Compile.Pipeline` imports the
phase to derive it — and the phase module is a leaf (data types and
total pure functions over the VM types, with no monad, `IORef` or IO), so
the edge carries no runtime machinery. Breaking: `CompiledProgram` and
`SessionInput` no longer carry `procIndex`; the slot phase replaces it.
See [the design notes](dev-docs/PROJECT.md#haskell-interpreter-performance)
and [the invariants](dev-docs/INVARIANTS.md).

The Haskell runtime now implements the paper's *Indexing* optimization
(§5.3). The compiler was already emitting the `Foreach` index conditions
its guard equalities imply — `leq(X, Y), leq(Y, Z) ==> leq(X, Z)` iterates
`leq` with `arg 1 == X`, and so on — but the runtime answered each of them
by scanning the whole type bucket. It now keeps a per-argument index for
exactly the `(constraint type, argument position)` pairs some `Foreach`
condition names, derived from the program by the new
`YCHR.Internal.VM.Index.indexablePositions`, and answers such a lookup
from a key bucket plus the position's non-ground fallback set.

The index may only narrow the iterator, never lose a candidate: the
per-candidate condition check (`checkConditions`) is still the decision
procedure. A suspension is filed under a ground key only when the indexed
argument was fully ground when it was stored — a suspension stored with an
unbound argument goes to the fallback set, which every lookup for that
position scans — and candidate lists stay in store order, so rule-firing
order is unchanged. Key equality is deliberately never finer than
ask-equality (`equal`), which is why `-0.0` and `0.0` share a key and
every NaN shares one. A lookup whose condition value is not fully ground
at loop entry, or whose expression could raise, falls back to today's
scan, unchanged: an index cannot hold a key that a later binding would
move.

Indexing is also on demand, so the change is win-or-neutral rather than a
small tax on small stores. A type is not indexed until its bucket reaches
`YCHR.Internal.Runtime.Index.indexThreshold`, at which point the whole
existing bucket is filed in one pass; a lookup for a type that is not
indexed yet, or whose candidate set would not be smaller than the bucket,
is exactly the scan it was before. Two store-side costs made this
necessary on the benchmark suite rather than merely prudent: an entry is
filed per store whether or not anything looks it up — the cost that fell
on `graph_test`, +13% with the index from the first store — and deriving
the lookup key per loop entry is wasted when the type has no index.

Measured on this machine by interleaving the benchmark binary against one
built from the parent commit, three rounds a side (the same setup
`dev-docs/PROJECT.md` describes; run-to-run spread is a few percent):
`leq_closure`, the store-heavy transitive closure whose `leq` bucket
reaches the hundreds, falls from a 38.2 ms median (39.1, 38.2, 37.3 ms) to
19.0 ms (18.9, 19.0, 19.1 ms) — **−50%**. Everything else moves within the
spread: `typecheck/pairs_library` 387.0 ms → 387.0 ms (its type arguments
are mostly not ground when stored, so the index has little to prune),
`graph_test` 125.2 → 127.1 µs, `leq` 7.19 → 7.04 µs, `fib` 1.135 → 1.135 ms,
`sum_list_test` 36.4 → 34.3 µs, and the four search benchmarks by 0–3%.

No change to the emitted VM, its serialization or its format version: the
index is a runtime-only implementation of the `Foreach` interface, and
`docs/reference/vm.md` is untouched. The compiler does change in one
respect — see the `CompiledProgram` field below — but only by exposing a
derived fact about the program it was already producing. The Scheme
runtime keeps scanning, as it does for
`inert-types`. New modules `YCHR.Internal.Runtime.Index` (the keys and the
index state) and `YCHR.Internal.VM.Index` (which positions a program looks
up through an index condition, over the IR, so the compiler can compute
it); `YCHR.Internal.Runtime.Store` gains `indexedPositionsFor` and
`candidateSuspensions`, and `YCHR.Internal.Runtime.Var` gains `groundKey`
and `addObserverAndKey` (one traversal per stored argument now registers
the observers *and* computes an indexed argument's key). `SessionEnv` gains
`storeIndex` and `indexPositions`, `initSessionEnv` takes the indexable
positions next to the inert types, `StoreSnapshot` carries the index so a
search restores it with the store, and
`YCHR.Internal.Runtime.Search`'s private `StoreIndex` newtype — a store
slot — is renamed `StoreSlot` to free the name. `CompiledProgram` and
`SessionInput` gain a lazily computed `indexPositions` field, in the same
place as the interpreter's procedure table: deriving the set walks every
procedure of the program, prelude included, and a session is created per
goal, so recomputing it per session costs a short goal several percent.
See
[the design notes](dev-docs/PROJECT.md#constraint-store-implementation).

Breaking: the serialized VM program now carries a VM format version.
`serialize` writes `(version 1)` as the first child of `vm-program`, and
`deserialize` accepts only that version: a unit declaring any other
`version`, or none at all — version 0, the pre-versioning format — is
rejected with an error naming the version it found. The version is
checked before the program body, so a dump from an unknown format fails
as a version mismatch rather than as whatever unknown construct it would
have hit first. This makes a stale `.vm` dump fail loudly instead of
being half-read, and matches the rule that each YCHR release supports
exactly one VM version. `YCHR.Internal.VM.SExpr` exports the new
`vmVersion` constant; the `callables` and `inert-types` entries remain
optional on read within a supported version. See
[the VM reference](docs/reference/vm.md#top-level-structure).

Breaking: `'$call'` no longer compiles to a per-arity `call_N` dispatcher
procedure. A dynamic call — `'$call'(F, A1, …, An)`, and so the prelude's
`call/N` family and every first-class function value — now compiles to
the new `ApplyClosure` VM construct, which the runtime resolves in one
lookup through a new *callables* dispatch table on the VM `Program`,
mirroring the *evaluables* table the `is` deep-evaluator already
consults. The table maps a closure's `(functor, identity field, declared
arity)` to the `func_*` procedure that implements it: `"/"` plus the
flattened source name (`module:name`) plus the recorded arity for a
function reference, `__closure` plus the lifted lambda's identifier plus
the arity it is applied at for a lambda closure. Per-`'$call'` cost no
longer grows with the number of functions and lifted lambdas the program
(including every imported library) defines. Semantics are unchanged,
including both failure modes — an unbound closure is still an
instantiation error a rule guard can catch and retry, and a non-callable
or a wrong-arity application still raises `call: no matching closure` —
and `'$call'` still accepts one to ten arguments (`YCHR-16022`), a limit
that is now a surface-language choice rather than an implementation
artifact. `YCHR.Internal.Compile.genCallFunDispatches`, `callFunProcName`,
`PKCallDispatch` and the `(call-dispatch …)` serialization tag are gone;
`Compile.buildCallables` replaces them. `Program` gains a `callables`
field, serialized after `evaluables` and optional on read like
`inert-types`, and `ValExpr` gains `ApplyClosure`. Measured on this
machine by interleaving the benchmark binary against one built from the
parent commit, `typecheck/pairs_library` drops from a 178.4 ms median to
155.0 ms (−13%; a second five-round comparison gives 183.2 ms to
157.1 ms, −14%; the new binary is faster in all ten pairs), and the two
most `'$call'`-heavy micro-benchmarks move with it: `sum_list_test` by
48% and `lambda_test` by 33%.

Runtime API changes that go with it: `YCHR.Internal.Runtime.Monad.initSessionEnv`
takes the callables registry, `SessionEnv` gains a `callables` field,
`YCHR.Internal.Runtime.Session.withCHRExtra` / `withCHRExtraTraced` take
an extra callables argument, and `YCHR.Run.PreparedQuery` gains an
`extraCallables` field — all because a query's lifted lambdas now
contribute table entries instead of regenerated dispatch procedures. The
Scheme runtime gains `register-callable!` and `%apply-closure`, and its
session record gains an immutable `callables` field (a breaking change
for direct `make-session` callers). `ychr gen-driver` emits
`%apply-closure` for a `'$call'` in a goal instead of a `call_N`
identifier, and encodes a goal-side function reference with the
flattened `module:name` identity the table is keyed on, correcting an
encoding that could never have matched. See
[the VM reference](docs/reference/vm.md#closure-application).

The `ychr` CLI accepts `--no-check` on `run`, `compile`, `gen-driver`
and `repl`. It skips the optional type checker entirely — the
whole-program check and the per-goal / per-query check — so a program
with type errors still runs, compiles or generates a driver, and no
`2x1xx` type warnings are reported. Type errors then surface as runtime
errors, if at all. Compilation errors (parse, collect, rename, resolve,
desugar, compile) still fail, and `--Werror` still treats the remaining
compile and rename warnings as fatal. `ychr check` keeps checking
unconditionally and does not accept the flag.

The library gains `YCHR.Run.prepareQueryUnchecked` — `prepareQuery`
without the type check, the function behind the REPL's `--no-check`
path, and the missing companion to the existing checker-free
`runGoalConstraint` / `resolveQueryGoals`. `YCHR.Internal.Repl.runRepl`
now takes its checker as `Maybe SessionInput`, with `Nothing` meaning
"do not check" (the CLI passes `Nothing` under `--no-check`); its other
arguments are unchanged. See
[the type system reference](docs/reference/type-system.md) and
[the REPL reference](docs/reference/repl.md).

Breaking: the `ychr` library no longer embeds anything at compile time,
and the two resources it used to bake in are now explicit arguments.
The bundled standard library is a `StdLib` — a newtype over the parsed
`libraries/*.chr` modules in `YCHR.Internal.StdLib`, produced by
`parseStdLib` (whose return type changed from `Map Text Module`) — and
every public entry point that compiles takes it first: `compileFiles`,
`compileModules`, `compileParsedModules`, `YCHR.Convert.runQuery` /
`runQueryWith` / `runQueryWithHostCallRegistry`, `YCHR.DSL.runDSL` /
`runDSLWithHostCallRegistry`. The compiled type-checker is a
`SessionInput` — built by `YCHR.Internal.TypeCheck.Compiled`'s
`compileTypeCheckerModules`, which now takes the `StdLib`, and no longer
a `typeCheckerProgram` CAF — and every public entry point that
type-checks takes it first: `typeCheckProgram`, `typeCheckGoals`,
`prepareQuery`, `runPreparedGoal`, `runProgramWithGoal`,
`runProgramWithQuery`. The `GoalDSL` runners and `runQueryCompiled*`
never type-check and keep their signatures.
`YCHR.Internal.StdLib.stdlib` and
`YCHR.Internal.TypeCheck.Compiled.typeCheckerProgram` are gone; the
`ychr` executable, tests, benchmark and `stlc` example build the values
they need from the Template Haskell embedding in the new shared `embed/`
source directory (`YCHR.Embedded`), so `library ychr` no longer depends
on `template-haskell`. See
[the embedding guide](docs/how-to/embed-a-chr-module.md#5-supplying-the-resources).

The `ychr` executable now builds and runs under MicroHs, where the last
Template Haskell holdout on its path has a run-time twin. `YCHR.Embedded`
gained `loadResources :: IO (Either Text Resources)`, implemented two ways
and switched by `hs-source-dirs` in `ychr.cabal`: GHC keeps the splice and
returns the compile-time values, while MicroHs compiles the new
`src/mhs/YCHR/Embedded.hs`, which re-exports the loader in the new library
module `YCHR.Internal.Resources`. That loader reads `libraries/*.chr` and
`typechecker/*.chr` under `$YCHR_LIB_DIR`, or the current directory when
the variable is unset or empty, so a MicroHs-built `ychr` must run from a
YCHR source tree or be pointed at one. The CLI loads its resources once,
after parsing its command line (so `--help` needs no source tree), and
threads them through its subcommands; the GHC binary still consults no
directory at run time. Under MicroHs the commands work, but help and
usage screens still trip an unrelated MicroHs bug in
`Data.Text.replicate` (dev-docs/MICROHS_GAPS.md, gap 9). See
[the embedding guide](docs/how-to/embed-a-chr-module.md#5-supplying-the-resources).

Fix: a build with `profiling: true` in `cabal.project.local` now links.
The four components that compile the `embed/` splices declare
`other-extensions: TemplateHaskell` (through the new `th-embed` common
stanza in `ychr.cabal`). Cabal never reads `LANGUAGE` pragmas; it reads
`other-extensions` to decide which build ways a component needs, and that
is what makes it also build those components the way GHC's splice
interpreter can load them. Without it the profiled build died with
`cannot find object file ... .dyn_o while linking an interpreted
expression` ([haskell/cabal#5961](https://github.com/haskell/cabal/issues/5961)).
Unlike `default-extensions` the declaration is not passed to GHC, so it
does not enable `TemplateHaskell` in modules that do not already opt into
it.

Breaking: the wildcard is gone from the runtime. `YCHR.Run.Value` no
longer has a `VWildcard` constructor, the VM `Literal` type no longer
has `WildcardLit`, the serialized `.vm` format no longer accepts a
`wildcard` atom, and the Scheme runtime no longer exports `*wildcard*`
or `wildcard?`. `read_term_from_string("_")` now produces a fresh
logical variable instead of that non-binding value, and so does
`YCHR.Convert.resultToValue` applied to a `Wildcard` term. The change is
safe to make because nothing legitimate produced one: `_` is an
anonymous variable (see the fix below), and a value that matches
everything while binding nothing has no place in an evaluated position.

Fix: an anonymous `_` written outside a rule head or equation pattern is
now a fresh logical variable, one per occurrence, instead of the
non-binding wildcard value. A constraint told with it is registered as
an observer and reactivated when the variable is later bound, so
`m @ go(X) <=> f(X), X = 1.` with `r @ f(N) <=> N == 1 | out(ok).` now
tells `out(ok)` for `go(_)` exactly as it does for `go(_X)` and
`go(Y)`; it previously left `f` stranded and asleep. The lowered form is
`new-var`/`(make-var %s)` — see the
[language reference](docs/reference/language.md#tell-side-evaluation)
and the [VM reference](docs/reference/vm.md#literals).

Fix: `ychr repl` no longer aborts when the history file is unusable. If
the XDG data directory cannot be created, or the history file is not
writable or not readable (or is a directory), the REPL starts with
history disabled and reports `REPL history not available` on stderr
(`--quiet` suppresses it). See the
[REPL reference](docs/reference/repl.md#history).

Fix: `ychr gen-driver` compiles a `host:` call in a goal argument to the
same runtime procedure the compiled library uses. It previously emitted
a `host__<name>` identifier that no Scheme module defines, so a driver
generated from a goal such as `go(host:'+'(1, 2), R)` failed under Guile
with `Unbound variable: host__+`; it now emits `(%add (deref 1)
(deref 2))` and threads the session for `copy_term`, matching the
compiled-library path.

New: first-class application now covers arities 1 through 10. The
wired-in dynamic call primitive `'$call'` previously dispatched only
arities 1 and 2; the compiler now emits `call_1` … `call_10`
dispatchers, and the prelude's typed family grows to match, adding
`call/4` … `call/11` (one overload per arity, so `'$call'` no longer
has to be reached for directly).

- The prelude is imported in full by every module, so a module that
  declares its own `call/4` … `call/11` now collides with the prelude
  (`YCHR-20001`), exactly as any other prelude name would.
- A `'$call'` outside the supported range is rejected during
  resolution with `YCHR-16022` instead of lowering to a `call_N`
  procedure the compiler never emits. That covers both ends: a callee
  applied to no arguments (or a bare `'$call'`) is no longer silently
  treated as a data term, and a call wider than ten arguments is no
  longer deferred to a runtime miss. This covers programs, queries and
  generated drivers, since all of them translate surface `'$call'`
  through the same resolver.
- Lambdas no longer contribute dead dispatch branches. A closure can
  only be invoked at the arity its source lambda declared, so
  `genLambdaBranch` emits one branch for that arity instead of one per
  arity up to the lifted function's total (captures included) arity.
  This keeps the extra dispatchers from multiplying the size of
  lambda-heavy VM programs.
- A `call_N` dispatcher no longer re-tests the closure shape and arity
  in every function-reference branch. Every function reference has the
  form `'/'(Name, Arity)`, so the branches shared those two tests and
  differed only in `Name`; they are now hoisted into one guard around
  the whole function-reference block, and the name is extracted once,
  leaving a single comparison per branch. Over five interleaved
  `cabal bench` rounds `typecheck/pairs_library` is 185 ms against a
  252 ms baseline, with the gains concentrated in the `'$call'`-heavy
  programs (`sum_list_test` 34.0 µs → 26.6 µs, `lambda_test`
  10.2 µs → 8.3 µs, `search_deep` 69.0 ms → 51.7 ms). The scan over
  same-arity function names is still linear; keying the dispatch on
  `(Name, Arity)` remains the asymptotic fix (see the roadmap in
  `dev-docs/PROJECT.md`).
- See the [language reference](docs/reference/language.md).

New: refinement-predicate declarations. A closed `:- function` with the
signature `name(any) -> bool` may carry a `refining` clause naming the
type a successful call proves of its argument:

```prolog
:- function is_list(any) -> bool refining list(A).
```

A guard calling such a function on a bare variable then contributes the
declared type as guard-derived evidence, exactly as the prelude's
`integer/1` did before. This replaces the hard-coded list of four
prelude type predicates, and nothing in the type checker keys off a
function name any more. See the
[type system reference](docs/reference/type-system.md).

- The prelude's `integer/1`, `float/1`, `string/1` and `boolean/1` now
  carry the clause; `atom/1`, `var/1`, `nonvar/1` and `ground/1`
  deliberately do not.
- The refined type must be a base type or a type constructor applied to
  distinct type variables. Evidence pins only the outermost
  constructor, so `refining list(int)` could only mean `refining
  list(A)` and is rejected rather than silently widened.
- Two new error codes. `YCHR-16021` covers a clause on a declaration
  that cannot carry one (open function, class, untyped, wrong arity,
  argument not `any`, return not `bool`) and a refined type that is not
  a valid refinement. `YCHR-15020` rejects one on a
  `:- chr_constraint`.
- `library(lists)` exports `is_list/1`, refining `list(A)`, and
  `library(maybe)` exports `is_maybe/1`, refining `maybe(A)`. Both take
  `any`, so unlike `is_just/1` they answer over values of any type; an
  argument that is not (yet) one of theirs, an unbound variable
  included, is `false` rather than an error. A module that imports one
  of those libraries and declares a function of the same name now has
  an ambiguous name; rename one of the two.
- `refining` is now an operator word, `xfx` at priority 1140 — the same
  row as `requiring`, so the two cannot be combined on one signature.
  Bare `refining` atoms are unaffected, in patterns and in terms alike.
  The one source change this forces is a *typed* constraint
  declaration at arity 2 named `refining`: write it as the untyped
  `:- chr_constraint refining/2` instead.

New: opt-in search, `library(search)`. Explore alternative bindings and
undo the ones that do not work out. Nothing here affects a program that
does not import it, and there are no new VM instructions; the Haskell
runtime is the only backend that implements it. See the
[search specification](docs/reference/search.md).

- The primitive is `alt/1`, an ordinary CHR constraint with no rules.
  Telling it leaves it in the store; at quiescence the driver takes the
  oldest live one and tries its goals in list order, undoing the branch
  between attempts. An alternative is a *goal*, not a value, so a
  choice is between computations.
- The disjunction operator `;` is surface syntax for an `alt`, `xfy`
  at priority 1100, and is available in a rule body once the module
  imports `library(search)`. Each disjunct is lifted into its own
  constraint, the way a lambda is lifted. Choice is still made at
  quiescence, so in `p, (a ; b), q` the goal `q` is told before a
  branch is picked.
- `choose(X, Alts)` labels a variable and is one library rule over
  `alt/1` and `try_unify/2`, not a runtime primitive.
- `between(Low, High, X)` labels a variable over the closed integer
  interval `[Low, High]`, ascending, one value at a time: each step
  offers the current integer and the next one, so nothing proportional
  to the size of the interval is built and `find_n/3` over a huge
  interval returns promptly. `Low > High` is the empty interval, so the
  branch fails as `choose(X, [])` does; a bound `X` is a membership
  test. The declared `int` bounds reject a non-integer call site
  statically, and an unbound bound is a runtime error when the
  constraint is told, not a silent delay.
  See [`libraries/search.chr`](libraries/search.chr).
- Solutions are fetched with `solve/1` (first solution, bindings
  kept), `findall/2` (all of them, everything undone) or
  `fold_solutions/4`, a fold over the solution sequence with early
  exit. `forall/3` and `find_n/3` are derived over the fold; `find_n`
  terminates on an infinite space, where `findall` would not.
- The collector is spelled `findall/2`, not `find_all/2`, matching
  Prolog's `findall/3`; the `host:findall` call behind it is renamed
  with it. The rest of the module keeps its names.
- `fail/0` abandons a branch, and `try_unify/2` is Prolog's `=`:
  unify, or fail rather than raise.
- Three new error codes: `YCHR-20021` (`;` without importing
  `library(search)`), `YCHR-20022` (`;` outside a rule body — in a
  guard, an `is` right-hand side or a function body) and `YCHR-30006`
  (`;` at the top level of a query).
- A `quote/1` argument in a *tell* position may now introduce a fresh
  variable, as an `=` operand may. An unbound name in an `is`
  right-hand side or a call argument is still `YCHR-40002`.
- The type checker's resolution of overloaded class-function
  signatures now runs on this library — one `solve/1` per equation
  over a `;` chain of attempts — instead of one throwaway
  `run_chr_session/1` fork per candidate signature. Verdicts are
  unchanged. One difference in kind: a runtime error inside an
  attempt now aborts the check and surfaces as that error, rather
  than reading as one more signature that did not fit.

VM program header: a new optional `inert-types` entry lists the
constraint types whose activation runs no occurrence procedure
(no occurrences, or only passive ones). A runtime may skip registering
such a constraint as an observer of the variables in its arguments;
honoring the entry changes no result, only the reactivation traffic.
The Haskell runtime honors it, the Scheme backend ignores it. A
program serialized before the entry existed still reads, declaring no
inert type. See the [VM specification](docs/reference/vm.md).

- This, together with an enqueue-time liveness filter on observers
  and a per-branch cursor in the search driver, makes a search path
  linear in its depth where it was quadratic: a path of ten thousand
  choice points went from about 15 s to under 0.2 s.
- `run_chr_session/1` is now the same driver: `solve/1` made total.
  Same fork, same commit on the first solution, with a runtime error
  in the goal reported as `false` instead of propagating — its one
  distinct job, and the language's only error catcher. Two changes in
  behaviour: a `false` result is now fully rolled back, where the
  sub-session's bindings used to be left in place, and a choice point
  the goal tells is explored instead of sitting inert. A misspelled or
  unexported goal constraint is still a loud caller error, not a
  `false`.

Soundness fix: `GuardEqual` evidence (the fact a shared head variable
contributes) no longer treats value equality as full type equality. A
value determines its type's outermost constructor nominally but not
the constructor's parameters (`[]` inhabits `list(T)` for every `T`),
so at a rigid type variable the evidence now pins a base type or
nullary constructor application exactly, pins a parametric application
or function type only at *fresh rigid* parameters (the `GuardMatch`
discipline), and derives nothing at the parameter positions of a
shared constructor — no pins, no merges, and no
inaccessible-branch warning. Whole-type rigid-to-rigid merges (the
multi-head transitivity idiom) are unchanged. Found by the
type-soundness property test; see
`docs/reference/type-system.md` §Guard-Derived Type Evidence.

- Programs that exploited the hole now fail to check (typically
  `YCHR-60001`): a fully-typed program could previously bind a `bool`
  into an `int`-declared position through a constraint polymorphic in
  a type parameter.
- Some `YCHR-20104` warnings no longer fire, because the rules they
  marked dead can in fact fire: a parameter-only mismatch between two
  positions sharing a variable (`box(int)` vs `box(bool)` — live via
  `empty`), and the self-referential equality `T` \~ `list(T)`, which
  now pins `T := list(B)` (live via `[]`) instead of warning.

Breaking: a data-constructor name may no longer pun on a function
name. Previously the two were told apart by syntactic position —
pattern positions took the constructor, evaluating positions took the
function — so the same text meant different things in different parts
of one rule, silently.

- Declaring a constructor and a function with the same name in one
  module is now `YCHR-16020` (`ConstructorFunctionCollision`). Both
  spell as `mod:name`, so qualifying could not disambiguate.
- A *bare* reference to a name visible as a constructor from one
  module and as a function from another is now `YCHR-20020`
  (`ConstructorFunctionAmbiguity`). Qualified references
  (`node:leaf(grow:leaf(N))`) keep working and are the intended fix.
- Arity is not part of either comparison: `foo/0` the constructor
  collides with `foo/1` the function.
- `fun name/arity` references and `quote(...)` contents are
  unaffected — neither is a place where the two namespaces compete,
  and neither is a constraint name: a constraint may still share a
  name with a data constructor.

Every module imports the prelude in full, so a constructor may not be
referred to bare under a name the prelude declares as a function.
Accordingly, the STLC example's object-language variable node is now
`evar/1` rather than `var/1`.

Type-checker fixes aligning the implementation with the
[type-system specification](docs/reference/type-system.md):

- `any` never binds a type variable. A variable is typed `any` only
  when its declaration positions say so, judged over all sources at
  once — multi-source head typing no longer depends on head order,
  and `any` no longer leaks through shared variables.
- `R is e` types its RHS by evaluation (previously `is` was typed
  identically to `=`) and meets the result with the LHS through the
  ordinary meet table. It has no special power over `any`: an
  `any`-typed LHS is checked against and stays `any`, in rule bodies
  and function bodies alike.
- The operands of `=` are typed structurally, matching the runtime's
  structural unification: an evaluable-headed compound under `=` is
  a symbolic term typed `any`, not a function call. `Sum = 1 + 1` no
  longer types `Sum` as `int` (the runtime binds a symbolic
  compound); use `is` for the arithmetic — and the type.
- Equation bodies of untyped functions are now type-checked, exactly
  like their all-`any` spelled-out form. Programs with ill-typed
  bodies hiding behind untyped declarations may now be rejected
  (YCHR-60006) where they previously failed only at runtime.
- A polymorphic declaration's own type variables are now opaque inside
  its implementation — in a function's equations, and in a rule whose
  head mentions a polymorphic constraint (freshly per head occurrence,
  since the store may hold any mix of instances). Code that silently
  assumed one instantiation is now rejected: calling an overloaded
  operation at your own type variable needs a `requiring` clause, and
  two head occurrences of `leq(T, T)` no longer assume the same `T`
  unless a shared variable says so.
- Guard-derived type evidence: a guard whose success entails a typing
  fact — a type predicate (`integer(X)`), a constructor pattern, a
  repeated or literal head argument — contributes that fact to the
  positions that run after it. Evidence can only accept more programs;
  it enables operations at a type variable the guard has pinned, and
  is inert at `any` and at unconstrained variables.
- New warning **YCHR-20104** (inaccessible branch): a rule or equation
  whose guard contradicts a known type can never fire. Like the other
  `2x1xx` warnings it is promoted to an error by `--Werror`, and it is
  suppressed for a rule or equation that already reports an error.
- Overload resolution and `requiring` discharge are now residual: they
  stay pending and retry as inference adds information, instead of
  committing on first sight. A resolution still ambiguous when checking
  ends succeeds silently, as the specification requires. Each equation
  of a `:- class` is checked against every declared signature and needs
  to fit at least one.
- Declaration validation, with new codes: `YCHR-15018` (a type
  parameter that is not a type variable — previously dropped silently,
  changing the type's arity), `YCHR-15019` (a repeated type parameter),
  `YCHR-20016` (redeclaring a reserved type name such as `int`),
  `YCHR-20017` (a duplicate type declaration), `YCHR-20018` (a type
  declaration shadowing an imported one), and `YCHR-60013` (a
  constructor field applying a type constructor at the wrong arity).
- Arity-overloaded constraints and functions are keyed by name *and*
  arity throughout the checker; a `c/1` declaration no longer shadows
  `c/2`, which previously lost both `any` stamping and use-site
  checking for the shadowed arity.
- Lambda parameters shadow same-named enclosing variables, matching
  what the lambda lifter does at runtime.
- `Warning` (from `YCHR.Run`) gained a `TypeCheckWarnings` constructor.
  Code pattern-matching exhaustively on `Warning` needs a new case.

- A declared `any` nested inside a type now merges across a shared
  variable the way a top-level one does. With `p(list(any))` and
  `q(list(int))`, the rule `p(X), q(X) <=> ...` types `X` as
  `list(int)` — previously only `q(X), p(X)` did, and the other order
  silently kept `list(any)`, accepting whatever the body did with it.
  Programs relying on the accepting order may now report a type error.
  A position every declaration source leaves `any` still stays
  dynamic.
- A type that contains itself no longer hangs the compiler. Programs
  like `p(bx(W)) <=> W = bx(W)`, or the goal `p([X|X])`, made the
  checker bind a type variable to a type containing it; the resulting
  cyclic term wedged the next traversal. Such a fact now binds nothing
  and the program is accepted, as before.

Rule guards now tolerate under-instantiation. A guard that cannot be
decided — because an unbound logical variable reached a point that
demanded its value — evaluates to false instead of aborting the query:
the rule does not fire, and when the variable is bound later, ordinary
constraint reactivation retries the occurrence. This is on for every
rule guard, with no new surface syntax. See
[§Soft guard failure](docs/reference/language.md#soft-guard-failure).

- The catch is at the rule-guard boundary and nowhere else. An `is`
  right-hand side, a rule body and a top-level goal still fail hard,
  and an instantiation failure inside a function's equation guard
  propagates out of the function rather than falling through to the
  next equation.
- Runtime errors now carry a kind internally, which is what tells the
  two apart. Failures diagnosed as insufficient instantiation are
  worded "… is not sufficiently instantiated (unbound variable)".
  The strict host primitives — `+ - * / div mod rem`, `< > =< >=`,
  `int_to_float`, `float_to_int`, the `string_*` operations, `write`,
  `writeln`, `compound_to_list`, `list_to_compound` — report that
  wording where an unbound argument previously produced a type-shaped
  message. Primitives total on unbound values (`==`, `unifiable`, the
  type predicates, `term_variables`, `copy_term`) are unaffected, and
  no call that succeeded before fails now.
- A host function whose argument marshalling reports `UnboundValue` is
  classified the same way, so a guard calling one delays too. Decoding
  the argument as `Term` opts out.
- A guard whose value is an unbound variable delays (the guard position
  demands a boolean); one that evaluates to a *bound* non-boolean is
  still the hard error "guard did not evaluate to a boolean".
- The boundness-guard idiom (`integer(N), N > 0 | …`) documented under
  [§No mode checking](docs/reference/type-system.md) is now a matter of
  style rather than a requirement — the unguarded rule gets the same
  schedule.
- New VM boolean form `bsoft-guard`; backends must implement it. Both
  backends do, and agree on every golden case: the Scheme runtime tags
  its strict primitives' failures the same way, and lowers `bfrom-val`
  through a boolean check rather than letting Scheme truthiness decide
  (an unbound variable is a record, hence truthy, and would have read
  as *true*).

Two Scheme-backend conformance fixes found while classifying the above,
both cases where the backend accepted what the Haskell runtime rejects:

- `list_to_compound` now rejects an improper tail and a non-atom head,
  not just an empty list. `list_to_compound([f, x | T])` quietly
  returned `f(x)`, and `list_to_compound([1, 2])` built a term whose
  functor was a number — which then escaped as a raw wrong-type
  condition from the pretty-printer rather than as a CHR error.
- `write` and `writeln` now require a string, as their prelude
  signatures already declare and as the Haskell runtime already
  enforced. Previously any bound value was displayed.

Stdlib additions, both implemented on both backends:

- `library(meta)` gains `name_base/1`, the local part of a name atom
  (`mod:foo` → `foo`, an unqualified name unchanged). Two names have
  the same base exactly when their unqualified spellings agree, which
  is how a program can recognize a name without knowing which module
  declared it. A non-atom argument is a runtime error; an *unbound*
  one is an instantiation failure, so a rule guard calling it delays
  rather than aborting. See [`libraries/meta.chr`](libraries/meta.chr).
- The ordering operators `<`, `>`, `=<` and `>=` gain a
  `(string, string) -> bool` signature alongside their `int` and
  `float` ones, so strings compare with the ordinary operators rather
  than a separate function. The order is lexicographic by code point:
  case-sensitive, following no locale's collation rules. There is
  still no mixed-type comparison — `1 < "a"` matches no signature
  (`YCHR-60006`). Because `max/2` and `min/2` are declared
  `requiring '>='(T, T) -> bool` / `'=<'(T, T) -> bool`, they now work
  on strings too; the prelude reference's claim that they were
  limited to the two numeric types is corrected accordingly. See
  [`libraries/prelude.chr`](libraries/prelude.chr).
- `library(chr)` is a new bundled empty module: it declares and exports
  nothing, because in YCHR CHR is the language itself, so Prolog's
  `library(chr)` has no runtime to contribute. It exists so that a
  Prolog module carrying `:- use_module(library(chr)).` compiles
  unchanged, as long as the rest of the module is Prolog-compatible.
  See [`libraries/chr.chr`](libraries/chr.chr).
- `library(lists)` gains `range/2`: `R is range(From, To)` is the
  closed integer interval `[From, From + 1, ..., To]` — the one-element
  list `[From]` when the bounds are equal, and `[]` when `From > To`.
  See [`libraries/lists.chr`](libraries/lists.chr).

New: the REPL gains a `:time GOAL` meta-command. It runs `GOAL` like any
other one-shot query but prints `Time: <seconds>s` (CPU time, microsecond
resolution) before the bindings. The number covers query execution,
including the fresh session a one-shot query builds, and not the query's
parsing and type-checking, so a query rejected before execution prints no
timing line; a runtime error prints the timing line first. It is
available at the outer prompt only, not inside a live session. See the
[REPL reference](docs/reference/repl.md#time).

Library API:

- `YCHR.Run` gains `resolveQueryGoals` and the `ResolvedQuery` record
  it returns: everything `prepareQuery` does — parse, rename, resolve,
  desugar, lambda-lift — short of type-checking, plus the program the
  resulting goals are to be checked against. `prepareQuery` is now
  defined in terms of it. Use it when you want the goals themselves,
  or want to type-check them yourself, rather than take
  `prepareQuery`'s all-or-nothing `TypeErrors`. Like the rest of the
  staged query pipeline it is outside the version policy.

Runtime:

- Unification now transfers a bound variable's observers onto the
  variables that binding made reachable, so a constraint waiting on
  `X` still wakes when `X` is bound to a term and *that* term's
  variable is bound later. Affects the Haskell runtime; the Scheme
  runtime still registers observers at store time only.

- `is` now evaluates a term built from a `host:` call. A `host:` call
  in data position carries the vmName `host__F` as its functor, which
  the host-call registry (keyed by the bare name `F`) did not match, so
  `T = host:'+'(1, 1), R is T.` reported `is: functor is not evaluable:
  host__+/2` on both backends. Both deep evaluators now dispatch a
  compound's functor in the same three tiers — the evaluables table, the
  host-call registry under the raw functor, then under the bare name of a
  `host:` term — and diagnose a non-evaluable functor with its decoded
  name (`host:-/1`, `m:pair/2`, `pair/2`) rather than the encoded
  vmName. Because the decoded `host__F` shape is matched structurally,
  an unqualified atom that merely reads `host:F` is not promoted to a
  host call. `write/1` and `writeln/1` join the Scheme
  prelude host-call table and both now return the unit atom, so a bound
  `host:writeln("x")` prints once and yields `'()'` on either backend.
  The deep evaluator also stops dispatching a call's arguments before
  checking the call itself: the arguments of a declared call are
  evaluated, while a constructor argument stays data, so
  `T = member(1, [0, 1, 2]), R is T.` (with `library(lists)`) evaluates
  instead of failing on the list's cons cell.
  See [the `is` operator](docs/reference/language.md#the-is-operator).

- The Scheme backend's `write_term_to_string/1` (from `library(meta)`)
  is implemented, so `R is write_term_to_string(T)` now returns the
  surface rendering of `T` instead of raising `not implemented`. The
  new `%write-term-to-string` is the counterpart of the interpreter's
  `prettyValue` — it calls the shared `pretty-term` — so the two
  backends agree on atom quoting, `(…)` around negative numbers, list
  syntax (including the ` | ` before an improper tail) and
  `true`/`false`. Flonum rendering still follows each host's own float
  format, a pre-existing printer divergence recorded in
  [dev-docs/SCHEME_BACKEND_GAPS.md](dev-docs/SCHEME_BACKEND_GAPS.md).
  The declaration is
  `(any) -> string`, so nothing is classified: an unbound variable is a
  success that renders as `_`, and no session is threaded
  (`Scheme.sessionHostCalls` deliberately does not grow the name). The
  name also joins the Scheme prelude host-call table at arity 1, so a
  `host:write_term_to_string` *term* is deep-evaluable under `is` like
  `host:read_term_from_string`. The new
  `test/golden/write_term_test/` directory runs on both backends, and
  `scheme/test/test-runtime.scm` pins the primitive and its `deep-eval`
  route directly. See
  [the Scheme backend gaps](dev-docs/SCHEME_BACKEND_GAPS.md).

- The Scheme backend's `print/1` (from `library(meta)`) now renders its
  argument through the surface pretty-printer instead of raw `display`,
  one line per argument, and returns the unit atom, matching the
  interpreter's `print` host call; `print` also joins the Scheme
  prelude host-call table so a `host:print` term reaches it under `is`.
  The `meta` primitives that still have no Scheme implementation
  (`print_store`, `write_term_to_string`, `write_store_to_list`,
  `run_chr_session`) are now bound runtime stubs rather than bare
  identifiers, so a module importing `library(meta)` loads on a strict
  R6RS implementation such as Chez and the gap is reported only when the
  function is called. `library(search)` still needs the same treatment.
  See [the Scheme backend gaps](dev-docs/SCHEME_BACKEND_GAPS.md).

- The Scheme backend's pretty-printer now quotes atoms exactly as the
  interpreter's does, so bindings, `print/1` output, `%unify` failure
  messages and `write`/`writeln` results agree on both backends instead
  of dropping the surrounding quotes. `pretty-term` ports
  `needsQuoting`/`renderAtom`: a bare lowercase identifier of letters,
  digits and underscores stays bare unless it collides with a word
  operator or contains `__`, and anything else — an atom with a space or
  a non-ASCII character, an uppercase lead, a symbolic atom, the unit
  atom `()` — prints single-quoted with `''` for an embedded quote.
  The module and base halves of a qualified name are quoted
  independently (`mymodule:'£foo'`, never `'mymodule:£foo'`), and the
  predicate uses `char-general-category` so the `Nl`/`No` characters
  that Haskell's `isAlphaNum` accepts (`a²`, `aⅧ`) stay bare. Diagnostics
  that name a functor keep the unquoted decoded form (`host:-/1`).
  This closes the last quoting divergences in the Scheme golden
  harness: the three `unicode_atoms_strings` cases and
  `qualified_unicode_ctor/pound_foo` now run on both backends, and the
  new `test/golden/atom_quoting/` directory pins the edge cases.
  See [the Scheme backend gaps](dev-docs/SCHEME_BACKEND_GAPS.md).

- The Scheme backend's `read_term_from_string/1` (from
  `library(meta)`) is implemented, so the whole
  `test/golden/read_term_test/` directory runs on both backends. The new
  `(ychr read)` library ports the reference reader
  (`YCHR.Internal.PExpr`'s Pratt parser driven by `Parser.builtinOps`,
  converted the way `termToValue` does): a named variable is one fresh
  logical variable shared between its occurrences, `_` is fresh per
  occurrence, `true`/`false` (and the `prelude:` forms) are native
  booleans, a 0-arity name is an atom, and a `module:name` keeps the
  reference's colon spelling rather than the compiler's mangled form.
  Because reading allocates variables, the call now takes the session
  (`Scheme.sessionHostCalls` grew the name), and it is registered in the
  Scheme prelude host-call table at arity 1 so a
  `host:read_term_from_string` term is deep-evaluable too.
  `read_term_test` left `HASKELL_ONLY`. See
  [the Scheme backend gaps](dev-docs/SCHEME_BACKEND_GAPS.md).

Benchmarks:

The Scheme backend has a benchmark suite of its own. `make bench` now runs
the criterion interpreter benchmarks and then the Scheme suite;
`make bench-scheme-chez` runs the same suite under Chez Scheme, and
`make bench-scheme-all` runs both. The harness measures in process — each
timed iteration creates a fresh session and runs one workload (a goal, or
for the first case session creation alone), mirroring what
`runGoalConstraint` measures, and excluding compilation, process startup and
library loading — because wrapping an interpreter invocation would put 2 ms
(Chez) to 10 ms (Guile) of startup in front of cases as small as 10 µs. One
shared R6RS library (`bench/scheme/bench/harness.sls`) holds the programs, the
sampling policy and the reporting; `run-guile.scm` and `run-chez.scm` are the
only implementation-specific files, each supplying its own clock. Iteration
counts are adaptive (a wall-clock budget with minimum and maximum bounds)
because Chez is two to three orders of magnitude faster than Guile on these
workloads: `fib(20)` has a 1.98 ms median there against 729 ms under Guile,
and `leq_closure` 2.07 ms against 256 ms. Seven cases cover session creation,
guard evaluation, partner search, rule recursion, store growth with
propagation history and reactivation, list/`is` evaluation, and `'$call'`
dispatch. Four reuse golden programs, two are scaled benchmark-only programs,
and one (`session`) is a synthetic baseline; every case checks its result —
including the store size the transitive closure must leave behind — so a
benchmark cannot silently stop doing work. See
[dev-docs/BENCHMARKS.md](dev-docs/BENCHMARKS.md).

## 0.1.0.0 -- 2026-08-02

First release. See the
[README](https://github.com/lortabac/ychr#readme) for an overview and
[`docs/`](https://github.com/lortabac/ychr/tree/master/docs) for the
documentation.
