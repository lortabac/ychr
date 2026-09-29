# Benchmarks

YCHR ships two benchmark suites. They measure different things and are not
comparable with each other; each is the authority for its own backend.

- **`ychr-bench`** — the Haskell interpreter. Criterion, in
  `bench/Main.hs`; run with `make bench-haskell`.
- **Scheme benchmarks** — generated Scheme code and the Scheme runtime.
  The in-process R6RS harness in [`bench/scheme/`](../bench/scheme/); run
  with `make bench-scheme` (Guile 3).

`make bench` runs the criterion suite and then the Guile Scheme suite. The
Chez scheme suite is opt-in with `make bench-scheme-chez`, or both with
`make bench-scheme-all`.

## The Haskell interpreter suite

`bench/Main.hs` loads each program and its goal from a `test/golden/<name>/`
directory once at startup, then measures only `runGoalConstraint` — VM
execution plus runtime initialisation, excluding parsing, desugaring and
CHR-to-VM compilation. Criterion owns the sampling policy and the statistics.
See `dev-docs/PROJECT.md` for how those numbers have been used to accept and
reject interpreter optimisations.

## The Scheme suite

### What it measures

Each measured iteration creates a **fresh session** and tells one goal,
mirroring what `bench/Main.hs` measures: `runGoalConstraint` rebuilds the
session on every call, so session initialisation is part of both suites'
numbers. What the Scheme suite excludes:

- CHR-to-Scheme compilation (done once by `make bench-scheme`, before the
  harness starts);
- interpreter process startup and loading of the generated libraries.

Timing is done **inside the Scheme process**. Wrapping an interpreter
invocation would put 2 ms (Chez) to 10 ms (Guile) of process startup in front
of the smallest cases, so `criterion`, `hyperfine` and `pytest-benchmark` are
all the wrong shape here.

### Sampling policy

Iteration counts are **adaptive**, not fixed: Chez Scheme is two to three
orders of magnitude faster than Guile on these workloads (see the table), so
a count tuned for one is either a blink or minutes of work on the other. Each
case runs `warmup` untimed iterations, then keeps running timed iterations
until *both* at least `min-iters` have run and at least `budget-ms` of wall
time has accumulated, stopping at `max-iters` regardless.

| knob | default | `--quick` |
|------|---------|-----------|
| `budget-ms` | 150 | 40 |
| `min-iters` | 3 | 1 |
| `max-iters` | 200000 | 2000 |
| `warmup` | 2 | 1 |

The table reports `n`, `min`, `median`, `mean` and `max` in milliseconds.
**Min and median are the headline**; the mean is skewed by garbage-collection
and time-slice outliers, which is why `max` is printed alongside it (on one
development run, `session` had a 0.06 ms median and a 2.38 ms max).

Arguments are passed through `SCHEME_BENCH_ARGS`:

```sh
make bench-scheme SCHEME_BENCH_ARGS="--quick"
make bench-scheme SCHEME_BENCH_ARGS="--only fib --only leq_closure"
make bench-scheme SCHEME_BENCH_ARGS="--help"
```

An `--only NAME` that names no case is an error, as is an unrecognized or
malformed argument (`--only` with no value, a typo'd flag); the bare `--`
separator that Chez passes through is ignored. One failing case does not stop
the others: every case runs under `guard`, and the launcher exits non-zero if
any case raised or failed its result check.

### Cases

Four cases reuse golden programs exactly as `bench/Main.hs` does, two are
benchmark-only programs under `bench/scheme/`, and `session` is a synthetic
baseline that tells no goal. Every goal uses integers and fresh variables
only, so no runtime list or atom has to be encoded into Scheme by hand.

| case | goal | exercises | Guile ms | Chez ms |
|------|------|-----------|----------|---------|
| `session` | — | session creation | 0.09 | 0.01 |
| `guard` | `guard:clamp(3,5,R)` | guards, arithmetic | 0.07 | 0.01 |
| `graph` | `graph_test:run(R1,R2,R3)` | partner search, removal | 0.56 | 0.01 |
| `fib` | `fib:fib(20,R)` | recursion, trail | 729 | 1.98 |
| `leq_closure` | `leqc:run(20)` | store growth, history, reactivation | 256 | 2.07 |
| `list_sum` | `bench_list:go(500,R)` | lists, `is` deep eval | 58 | 0.08 |
| `maplist` | `bench_maplist:go(500,R)` | `'$call'` dispatch | 152 | 0.14 |

`session` is the cost every other case pays a *library-specific* part of: a
library that registers many evaluables and callables costs more to open than
`bench_fib` does, so subtracting this row from another case is only a rough
indication.

The medians are one default run on the development machine (Guile 3.0.9,
Chez Scheme 10.3.0). They are machine- and implementation-specific and are
**not** golden-tested; only the result checks are asserted, and every case has
one: `session` must return a session, `guard` 5, `fib(20)` 6765, `list_sum`
124750, `maplist` 41541750, `graph` the three expected `found`/`none` results,
and `leq_closure` the 190 live `leq` constraints the 20-node closure must
leave. A case that has silently stopped doing its work fails its check rather
than posting a suspiciously good time. Case sizes are tuned for the slower
implementation — the same size is reused on Chez, where the budget simply buys
many more iterations.

### Adding a case

Three places, in order:

1. Add the program under [`bench/scheme/`](../bench/scheme/) as a `.chr` file,
   or reuse an existing golden program whose goal takes its scale as an
   argument.
2. Add `library-name:source-path` to `SCHEME_BENCH_CASES` in the
   [`Makefile`](../Makefile). The library name is what `ychr compile -n` is
   given, and is imported as `(ychr generated <library-name>)`.
3. Add a `make-bench-case` row in
   [`bench/scheme/bench/harness.sls`](../bench/scheme/bench/harness.sls): the
   case name, the goal text shown in the table, a thunk that creates a session
   and runs the workload, and a check predicate over that thunk's result (`#f`
   only for a baseline that has no result to check).

Keep the generated library's name distinct from any R6RS or implementation
core binding: a generated library's program-info binding is named after the
library, and a library exporting `guard`, for instance, fails to load in Guile
("re-exporting local variable: guard"). The `bench_` prefix on every entry in
`SCHEME_BENCH_CASES` is what keeps that from happening, and the harness imports
each library with `only`, so generated short aliases cannot collide either.

## Writing a portable harness

The harness is one shared R6RS library plus one thin launcher per
implementation; the launcher is the only file that knows which interpreter is
running, because it supplies the clock.

- `bench/scheme/bench/harness.sls` — library `(bench harness)`, exported as
  `run-all`. It imports the generated libraries and takes `argv`, a `now`
  procedure and `ticks-per-second`.
- `bench/scheme/run-guile.scm` — `get-internal-real-time` with
  `internal-time-units-per-second` (Guile core bindings, 1e9 ticks/s). This
  is a real-time, not a monotonic, counter; a wall-clock step during a run
  could produce a negative sample. In practice it is the only
  high-resolution clock Guile exposes, and a stepping clock mid-benchmark is
  far rarer than the GC outliers the min/median reporting already absorbs.
- `bench/scheme/run-chez.scm` — `(current-time 'time-monotonic)` with
  `time-second`/`time-nanosecond` from `(chezscheme)`, converted to integer
  nanoseconds. Monotonic avoids wall-clock jumps.

The following are load-bearing and were established by running both
implementations; deviate from them and one of the two breaks.

- The shared library imports exactly:

  ```scheme
  (rnrs base) (rnrs exceptions) (rnrs conditions) (rnrs control)
  (rnrs records syntactic) (rnrs io simple) (rnrs sorting) (rnrs lists)
  ```

  `do` needs `(rnrs control)`, `define-record-type` needs
  `(rnrs records syntactic)`, `condition-message` needs `(rnrs conditions)`.
  Importing bare `(rnrs)` instead works on both but emits several "overrides
  core binding" warnings on Guile.
- Use `div`, not `quotient`: `quotient` is unbound in Chez's `(rnrs)`. Use
  `inexact`, not `exact->inexact`: also unbound there.
- The case record type is named `bench-case`, not `case`, which would shadow
  the `case` syntax.
- Chez's clock accessors are imported with `only`; importing `(chezscheme)`
  alongside `(rnrs)` fails with a multiple-definitions error.
- Chez passes a bare `--` separator through to `command-line`; the argument
  parser skips that one token, so the same `SCHEME_BENCH_ARGS` works under
  both launchers.
- Do not pass `--compile-imported-libraries` to Chez: it writes `.so` files
  next to `scheme/**/*.sls`, dirtying the tree, and would measure
  compiled-library loading rather than runtime. The default (load `.sls`
  source) is what these numbers are from.

## Caveats

- The Scheme suite is a developer tool, not a regression gate: the golden test
  suite is what checks correctness on the Scheme backend. The result checks
  here catch a benchmark that has silently stopped doing its work.
- Guile is the supported implementation for the test suite and CI, which is
  why `make bench` runs the Guile suite only. Chez is a comparison run.
- The absolute numbers are machine-specific. For a change-vs-change
  comparison, interleave rounds of the two builds on one machine, as
  `dev-docs/PROJECT.md` describes for the Haskell suite.
