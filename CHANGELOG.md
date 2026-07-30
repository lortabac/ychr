# Revision history for ychr

## 0.1.0.0 -- 2026-07-30

First release.

YCHR is a Constraint Handling Rules compiler. It parses standard CHR
(Prolog-compatible syntax, extended with Erlang-style user-defined
functions and an optional gradual type system), lowers it to a small
abstract VM, and either interprets that VM in Haskell or translates it to
Scheme. It ships as a Haskell library for embedding CHR in a Haskell
program, and as the `ychr` command-line compiler and REPL.

### Public API

* `YCHR` is the umbrella entry point: a single `import YCHR` for the
  common compile-and-query path (`compileFiles` / `compileModules`,
  `CompiledProgram`, `runQueryCompiled` and variants, the
  `ToTerm` / `FromTerm` bridge and its combinators, and the host-function
  registration helpers). `YCHR.DSL` (build programs as Haskell values) and
  `YCHR.Convert.Generic` (GHC-only `Generic` derivation) are opt-in
  companion imports.

* The supported public API is `YCHR`, `YCHR.DSL`, `YCHR.Convert`,
  `YCHR.Run`, `YCHR.Types`, and GHC-only `YCHR.Convert.Generic`.
  Everything else now lives under the `YCHR.Internal.*` namespace. Those
  modules stay exposed so their Haddocks remain browsable, but they are
  implementation details and are not covered by the package version
  policy.

* `displayError` / `displayWarning` render an `Error` or `Warning` in the
  same `file:line:col: YCHR-NNNNN` format the CLI uses. Previously the
  only option from outside the package was `show`, which dumps the
  internal diagnostic representation.

* `deref`, `equal`, and `newVar` are re-exported from `YCHR`. A
  `hostFnValues` handler receives raw `Value`s and previously had no way
  to dereference a logical variable without importing an internal module.
  There is deliberately no `Eq Value` instance: a derived one would
  compare variables by reference and disagree with CHR's `==`, which is
  what `equal` implements.

* `Term` now derives `Ord`, so it can key a `Map` or inhabit a `Set`.

* A unification failure or an unregistered host function raised from a
  *query* now surfaces as `Error`'s `RuntimeError` constructor, with a
  `YCHR-60001` code and a call stack, matching what the same failure
  already produced from a rule body. Both previously escaped as a bare
  `ErrorCall`, breaking the promise that callers can match a single
  exception type.

* `runQuery`, `runQueryWith`, and `runQueryWithHostCallRegistry` are no
  longer re-exported from the `YCHR` umbrella. They take `[Module]`,
  which only `YCHR.DSL` provides, so they were uncallable from
  `import YCHR` alone. They remain available from `YCHR.Convert`, which is
  where the DSL query path is documented.

### Standard library

* `not/1` in the prelude: boolean negation, usable in guards. YCHR has
  no `\=`, `\==`, or `=\=` operator, so structural inequality is written
  as an explicit negation — `not(X == Y)`, or `not(unifiable(X, Y))` for
  the not-unifiable sense. It rejects non-booleans rather than treating
  every non-`false` value as true.

* `library(lists)` now carries type signatures, so list code is checked
  instead of passing through as `any`. `head/1`, `tail/1`, and `nth/2`
  stay untyped on purpose: they are partial, the language cannot yet
  express a failing equation, and a signature would make every importing
  module emit a non-exhaustiveness warning.

* `libraries/lists.chr`, `strings.chr`, and `meta.chr` are documented in
  `docs/reference/prelude.md`, which previously said to read the source.

### Language

* **Breaking:** tell-side constraint arguments — in rule bodies and
  top-level goals — are now evaluated expressions, like every other
  expression position in the language. `foo(1 + 2)` evaluates `1 + 2` to
  `3` before the tell; `foo(plus(2, 3))` calls the `plus/2` function. The
  opt-out for passing a symbolic data term is the existing `term(...)`
  quoting form. Heads and equation patterns are unchanged (they still
  match on data shapes). An argument expression that mentions an unbound
  logical variable runtime-errors at tell time. See
  `docs/reference/language.md#tell-side-evaluation`.

* `runProgramWithGoal{,DSL}` and `runPreparedGoal` return just the
  per-query variable bindings (`Map Text Term`); the previously returned
  tell-procedure `Value` was always discarded by callers.

* The single-goal parser picks up the program's user-declared operators
  (matching the multi-goal parser), so operators like `+` work in
  goal-argument position from the CLI.

### Backends

* The Scheme library exports `func_*` procedures in addition to `tell_*`,
  so generated drivers can call user-defined functions appearing in goal
  arguments.

* Compiling to Scheme emits code that imports the YCHR Scheme runtime.
  That runtime is not distributed with this package, so `-t scheme`
  currently requires a source checkout. See
  `docs/how-to/scheme-repl.md`.

### Packaging

* Supports GHC 9.6 through 9.12. Built and tested against 9.6.6, 9.12.2,
  and 9.12.4.

* The `stlc-typechecker` example driver is behind a `examples` cabal flag,
  off by default, so `cabal install ychr` installs only `ychr`.

* The source distribution now carries the golden-test corpus and the
  bundled `examples/*.chr`, so the shipped test suite runs from an
  unpacked tarball.
