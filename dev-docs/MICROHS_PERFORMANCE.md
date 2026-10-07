# MicroHs Performance

`dev-docs/MICROHS_GAPS.md` records what stops YCHR from *building* under
MicroHs. This document records what stops it from running *fast* there, with
the measurements behind each claim and the options for fixing it. It began as
a diagnosis only: options A, C, D and E are still just that. Option B has
since been implemented — its section below records what was built and what it
measured.

Everything below was measured on 2026-10-05 against YCHR `d031947` (branch
`mhs-optimization`) and MicroHs `f65d3c65`, on an AMD Ryzen AI 9 HX 370. The
binary under test is the one `mcabal build` produces,
`dist-mcabal/bin/mhs/ychr`; the GHC build in `dist-newstyle` is the baseline.
Times are wall clock; most figures are single runs, and the ones used to judge
an A/B (the `-flto` comparison of §7E) are medians of interleaved rounds.

## 1. How the numbers were taken

No source was changed. Three instruments were used, all built into the
MicroHs runtime and reachable from the command line:

- `+RTS -v -RTS` prints the runtime's counters at exit: cells allocated,
  reductions, GC count, total time, GC time split into mark and scan, and
  maximum live cells. This is the primary source for every counter quoted
  below.
- `+RTS -T -RTS` dumps the **tick table**: MicroHs can instrument a program so
  that entering a top-level definition's body increments a counter, and this
  prints the counts. The instrumented binary is built by passing `-T` through
  `mcabal --options=-T build`.
- `+RTS -H<size> -RTS` sets the heap size in cells (the default is
  `HEAP_CELLS = 50 000 000`, i.e. 800 MB at 16 bytes/cell), which is how the
  GC measurements below vary the collector's frequency.

One caveat governs the tick profile: only the modules compiled with `-T` are
instrumented, and that is the YCHR library and executable, not the prebuilt
`base`/`containers`/`text` packages. Every entry in the table of §5 is
therefore the count of *YCHR function entries*; the container work those
functions then do is invisible, so the container-heavy rows understate their
real cost.

## 2. Headline numbers

| command | GHC | MicroHs | ratio |
|---|---:|---:|---:|
| `run --no-check` leq (tiny) | 0.026 s | 0.704 s | 27× |
| `run --no-check` `fib(18)` | 0.035 s | 2.693 s | 77× |
| `run --no-check` leq_closure `run(20)` | 0.034 s | 1.588 s | 47× |
| `run --no-check` search_label | 0.033 s | 0.930 s | 28× |
| `run --no-check` sum_list_test | 0.015 s | 0.745 s | 50× |
| `compile --no-check -t vm typechecker/*.chr` | 0.119 s | 4.962 s | 42× |
| `check test/golden/leq/leq.chr` | 0.166 s | 7.937 s | 48× |
| `check test/golden/pairs_library/pairs_library.chr` | 0.261 s | 17.606 s | 67× |
| `check typechecker/*.chr` | 2.291 s | 299.4 s | 131× |

The fixed per-process cost is ≈0.7 s, or ≈5.2 s for the commands that compile
the type-checker (§3). For the short commands that never do, the *marginal*
ratios are worse than the table suggests: `fib(18)` is ≈100×, leq_closure
≈55×.

The important context is that this is not mostly a YCHR defect. MicroHs's own
`tests/Nfib.hs` records `mhs` at 8.07 M nfib/s against `ghc` at 535 M nfib/s,
about 66×; the combinator runtime's intrinsic floor is around that. YCHR's
worst case, `check` at 131×, is roughly twice it — though that comparison
crosses two different workloads, so treat it as an indication rather than a
measurement. The extra factor is YCHR-shaped; see §6.

## 3. Where the time goes

### Counters

The `time` column is the runtime's own run time: it starts at `start_exec` and
so excludes loading and parsing the combinator file, which is why it is a
little below the wall clock of §2.

| workload | reductions | cells allocated | time | GC time |
|---|---:|---:|---:|---:|
| `repl --quiet` (startup only, EOF) | 73.4 M | 89.9 M | 0.81 s | n/m |
| `compile leq` | 72.6 M | 88.7 M | 0.71 s | 2.1 % |
| `compile typechecker/*.chr` | 564 M | 666 M | 5.26 s | 7.6 % |
| `check leq` | 805 M | 933 M | 7.91 s | 10.9 % |
| `check pairs_library` | 1 583 M | 1 775 M | 17.35 s | 14.8 % |
| `check typechecker/*.chr` | **18 627 M** | **20 375 M** | **299.1 s** | **35.7 %** |

The big run allocates 20.4 G nodes, about 326 GB at 16 bytes per node; GHC
allocates 12.7 GB for the same job. Steady-state rates are ~90–107 M
reductions/s and ~1.5–2.0 GB/s of allocation while the collector is out of the
way.

### Phase budget

`check typechecker/*.chr` — the 131× case — splits as follows. The first two
rows are per-process work that both builds pay at run time, only ~40× faster
under GHC (that is the front-end ratio of §2); the third is ordinary front-end
work over the input; the fourth is the interpreter.

| phase | MicroHs | share |
|---|---:|---:|
| process start + parse `libraries/*.chr` (34 KB, 943 lines) | ~0.7 s | 0.2 % |
| compile the 4 909-line typechecker CHR program at run time | ~4.5 s | 1.5 % |
| parse/rename/resolve/compile the input (4 909 lines) | ~5 s | 1.7 % |
| **execute the CHR typechecker over the input** | **~289 s** | **96.6 %** |

The same budget explains the short commands. `check leq` (7.9 s) is the 0.7 s
startup, the ~4.5 s typechecker compile, and ~2.7 s of actually checking.
`check pairs_library` (17.6 s) is the same 5.2 s of fixed cost plus ~12.3 s of
checking.

Both builds pay these two costs at run time; GHC does not precompute them:

- `YCHR.Internal.Resources.loadResourcesAt` parses `libraries/*.chr` eagerly on
  every invocation (`Resources.hs`). The GHC provider reaches the same
  `parseStdLib` call from `embed/YCHR/Embedded.hs`, over source text spliced
  into the binary and forced with the `stdlib` CAF.
- `Resources.typeCheckerProgram` is a lazy field built by
  `compileTypeCheckerModules`, so the first type-checking command in a process
  compiles all of `typechecker/*.chr` from source. The GHC provider does the
  same to `TypeCheck.embeddedTypeCheckerSources`. `run` without `--no-check`
  forces it too.

What GHC's embedder avoids is the directory lookup and the file I/O, which are
negligible; what it does not avoid is the parse and the compile. The 5.2 s of
fixed cost here is that work at MicroHs speed. Under GHC the whole checker path
— compiling it and then running it over `leq` — is 0.14 s, the difference
between `check leq` (0.166 s) and `run --no-check leq` (0.026 s).

The ~4.5 s figure is derived, not directly timed: `compile typechecker/*.chr
--no-check` costs 564 M reductions, of which 73 M is the startup parse, and the
checker's own compilation is that front-end minus serialization.

### Reductions per source byte

As an order-of-magnitude figure, the front-end runs a bit over 2 000 reductions
per source byte. The 564 M of `compile typechecker/*.chr` over 232 KB, less the
73 M startup parse, is 491 M over 232 KB; that residual also contains the
s-expression serialization `-t vm` performs, so the parse-and-compile rate on
its own is somewhat lower. Either way it is the ratio that makes a 4 909-line
input cost ~5 s.

## 4. GC, and the heap-size knob

The runtime uses a fixed-size mark-sweep heap: `HEAP_CELLS` cells allocated
once at startup, a free-cell bitmap, and a collection when free cells run
short. The GC count is therefore approximately `allocated / (heap − live)`, and
the total collector cost grows with it. Raising the heap is a pure scheduling
change — the same 20.4 G cells are allocated and the same 18.6 G reductions are
performed in every row below:

| heap | GCs | GC time | wall |
|---|---:|---:|---:|
| default (50 M cells / 800 MB) | 440 | 106.7 s (35.7 %) | 299.1 s |
| `+RTS -H200M` (3.2 GB) | 106 | 37.0 s (16.4 %) | 225.6 s |
| `+RTS -H400M` (6.4 GB) | 54 | 24.3 s (11.6 %) | **209.5 s (−30 %)** |
| `+RTS -H100M` (1.6 GB) | — | — | **aborts: `ERR: ARR_WRITE`** |

The same knob on `check pairs_library` (default 17.6 s): `-H100M` 15.99 s,
`-H200M` 15.70 s, `-H400M` 15.60 s, with GC falling from 15.1 % to 9.4 %, 6.4 %
and 4.7 %.

The `-H100M` row is not a typo and not a size that is simply too small: every
attempt at that heap died with `ERR: ARR_WRITE` (`T_ARR_WRITE` found its index
past the array end), two of them captured verbatim, at slightly different
points, while the default, 200 M and 400 M heaps all completed. This looks like
a heap-layout- or GC-timing-sensitive bug in the MicroHs runtime or the
generated code rather than anything in YCHR, but it is unverified. It is the
reason the heap recommendation below is not a one-line default change.

## 5. Function profile

Tick build, `check pairs_library`, 15.8 M YCHR function entries. Shares are of
that total, and they understate container work for the reason in §1.

```
11.0%  Runtime.Interpreter.evalValExpr
10.9%  Runtime.Interpreter.get$.Env.envValues      <- record selector
 8.5%  Runtime.Interpreter.execStmts
 7.1%  Runtime.Interpreter.execStmt
 5.7%  Runtime.Var.deref
 4.7%  Runtime.Interpreter.insertVal
 4.1%  Runtime.Monad.get$.SessionEnv.traceHandler  <- tracing is OFF
 3.8%  Interpreter.Slots.get$.SlotProc.slotProcKind
 3.4%  Runtime.Interpreter.evalBoolExpr
 2.8%  Runtime.Interpreter.emitTrace
 2.4%  Runtime.Interpreter.modifyEnv
 2.3%  Runtime.Interpreter.evalCallArg
 1.3%  VM.Types.get$.Name.unName                   <- Text compare for map keys
```

Two structural facts fall out of it.

**Per-procedure-call overhead is about eleven function entries beyond the
body.** `callProc` itself, then `lookupProc`, `bindParams`, `traceEntry`,
`withSavedCallStack`, `withFreshEnv`, `bumpDepthFor`, `withTraceDepth`,
`traceExit`, and the `slotProcBody`/`slotProcArity` projections — 199 487 calls
× 11 ≈ 2.2 M entries, ~14 % of the total, before the body does anything.
`lookupProc` is a `Map Name SlotProc` lookup, so each call also risks a `Text`
comparison there (`Name.unName`, 205 k entries, is on that path among others).

**Record selectors are real function calls.** `Env.envValues` alone is the
second entry at 10.9 %: it is one projection per `insertVal` plus every `SVar`
read of the local `IntMap`. MicroHs emits a `get$.` function per field,
`NoFieldSelectors` is ignored (`MICROHS_GAPS.md` gap 2), and `{-# INLINE #-}`
is ignored too — the lexer honours only `SOURCE` and `LINE` — so nothing is
inlined or unboxed.

The `traceHandler` and `emitTrace` rows are the trace subsystem paying per
call and per event while tracing is off: the handler is read 645 k times and an
event action is constructed at each of 440 k `emitTrace` calls.

The front-end profile looks different and much healthier:
`SExpr.printSExpr` (122 k entries, the VM s-expression serializer) and
`Data.Text.Shim.concatMap` (38 k, implemented as `T.concat (map f (T.unpack t))`)
lead, followed by the lexer and parser records. The startup-only profile is
essentially all parser and rename records.

## 6. Root causes

1. **Combinator graph reduction has no inlining or unboxing.** MicroHs ignores
   `INLINE`, `UNPACK` and `SPECIALIZE`. Every small monadic helper and record
   projection YCHR's runtime is written in terms of stays a real call with real
   allocation. This is the ~66× floor of §2.
2. **YCHR's hot path is unusually call-dense.** `Chr` is
   `ReaderT SessionEnv IO`, `InterpM` is `ReaderT (IORef Env) Chr`, and the
   per-call and per-binding paths go through `Map`/`IntMap`/`Text` and a trace
   hook that is checked even when disabled. That is the extra factor over
   MicroHs's own baseline.
3. **A per-process front-end bill that both builds pay, at 40× the price.**
   The stdlib parse (~0.7 s, 73 M reductions) runs on every invocation and the
   typechecker CHR compilation (~4.5 s) on every type-checking command. GHC pays
   the same work — its embedder splices source text, not parsed values — at
   roughly the 0.14 s that separates `check leq` from `run --no-check leq`;
   under MicroHs it is 5.2 s of the 7.9 s that `check leq` takes. **Removed on
   the MicroHs side by option B** (§7B): both now happen at build time.
4. **Allocation-driven collection**: the big run allocates 20.4 G nodes (about
   326 GB) and spends 36 % of its time in the collector at the default heap
   (§4).
5. **Case dispatch on large sums.** `SlotStmt` has 16 constructors and
   `SlotBoolExpr` 14, both over MicroHs's `scottLimit = 6`
   (`MicroHs/src/MicroHs/EncodeData.hs`), so a match on them uses the `TAGn`
   encoding: an extra tag node per construction and an O(log k) comparison
   tree per match, rather than a jump table.

## 7. Options

Ordered by expected impact per unit of work. A–C are YCHR-side; D is a
front-end detail; E records a measured dead end.

### A. Give the runtime a bigger heap

Zero code. Measured: `check typechecker/*.chr` 299.1 s → 209.5 s (−30 %) and
`check pairs_library` 17.6 s → 15.6 s (−11 %) at `+RTS -H400M`. To make it the
default rather than an argument, bake a larger `HEAP_CELLS` into the MicroHs
build: the runtime's `HEAP_CELLS` is guarded by `#if !defined(HEAP_CELLS)`, so
a custom `mhs.conf` target with `ccflags = "-O3 -DHEAP_CELLS=400000000"` does
it.

Two constraints. The cost is real RSS (6.4 GB at 400 M cells), so this is a
desktop/server setting and the WASM target needs a much smaller value. And it
must be validated against the `-H100M` `ERR: ARR_WRITE` abort of §4, which is
the reason this is not simply "raise the default and move on".

### B. Precompute the per-process resources — implemented

Both builds used to parse the stdlib and compile the type-checker on every
process (§3). That work is gone from the MicroHs path. `make resources` runs
`ychr-codegen` (`codegen/Main.hs`), which decodes `libraries/*.chr` and
`typechecker/*.chr` with `parseStdLib` and `compileTypeCheckerModules` and
writes two Haskell modules under `generated/`:

- `YCHR.Embedded.Generated.StdLib`, carrying the parsed `StdLib`;
- `YCHR.Embedded.Generated.TypeCheck`, carrying the type-checker's VM
  `Program`, its two export tables and its operator table, wrapped in
  `Session.mkSessionInput` so that the slot phase and the indexable positions
  are rebuilt from the program at load time. Serializing those two derived
  fields as well would add about 1.3 MB of generated source; carrying the
  indexable positions explicitly was tried and moved no counter, so they stay
  derived. The operator table is not derivable from the VM program, so it is
  emitted as a `PExpr.mkOpTable` literal over `opTableEntries` — a few dozen
  entries.

The modules are plain literal data — constructor applications, no Template
Haskell — so MicroHs compiles them without a staged-compilation facility. The
emitter (`embed/YCHR/Embedded/Generate/`) is GHC-only: it walks the AST with
`GHC.Generics`, renders each node as Haskell source (`Text` and `String` as
string literals under `OverloadedStrings`, containers through `fromList`,
everything else positionally), and then flattens the tree into many small
top-level bindings. That last step is what makes the module compilable at all:
the type-checker's program is about 1.5 MB of `Show` output, and one expression
that size is not something MicroHs will accept. Splitting is by list length
and by rendered size (`--chunk`, `--max-binding-bytes`), and a binding that is
still over budget once lifted has its structured arguments lifted in turn, so
that what remains is a head and a few names: with the defaults, the longest
binding body in either module is 8 191 characters. The one node that can
exceed the budget is one whose bulk is a literal — a constructor application
or tuple holding a long string — which cannot be split without giving the
lifted literal a type.
The two modules total 1.7 MB, are gitignored, and are listed in the
executable's `other-modules` and `autogen-modules`; only `generated/README.md`
is committed, because Cabal rejects an `hs-source-dirs` entry that names a
missing directory even in a conditional for another compiler.

`mcabal build` must follow `make resources` (or `make mhs-build`); a GHC build
never looks at the directory and keeps its Template Haskell splice. The
MicroHs executable consequently ignores `YCHR_LIB_DIR`: its resources are
whatever it was built with.

Reductions first, because they are the stable figure:

| workload | §3 baseline | now |
|---|---:|---:|
| `repl --quiet` (startup only, EOF) | 73.4 M | **7.5 M** |
| `run --no-check` `leq` | — | 3.5 M |
| `check leq` | 805 M | **367 M** |
| `check pairs_library` | 1 583 M | **1 143 M** |
| `compile --no-check -t vm typechecker/*.chr` | 564 M | **498 M** |

and wall clock (medians of three runs; the baseline column is §2/§3):

| command | baseline | now |
|---|---:|---:|
| `repl --quiet` startup | 0.81 s | **0.14 s** |
| `run --no-check -g … leq` | 0.704 s | **0.08 s** |
| `check leq` | 7.94 s | **4.07 s** |
| `check pairs_library` | 17.61 s | **13.43 s** |
| `compile --no-check -t vm typechecker/*.chr` | 4.96 s | 4.77 s |

The startup row is the one option B set out to remove, and it is gone: 73.4 M
reductions of parsing became 7.5 M of materializing the literal standard
library, which is why the short commands that never type-check are now
dominated by process start. Its baseline is the one figure in the table taken
from §3's runtime clock rather than §2's wall clock; for that command the
runtime reports 0.09–0.12 s today, so the like-for-like comparison is 0.81 s →
0.1 s and the 0.15 s above is process start plus that.

`check` improved by about 440 M reductions — 55 % of its fixed cost — on both
workloads, but not to the ~2.7 s predicted here. That prediction assumed the
fixed cost was startup + compile + a small session setup; it is not. `check` on
an *empty* module still costs 346 M reductions, so the fixed cost decomposes as
startup (7.5 M) + materializing the precomputed checker (~120 M) + the session
setup and checker start-up that running the checker has always cost (~220 M,
which is option C's territory, not B's). Against that, the baseline's ~491 M
compilation is a four-fold saving on the compilation alone, which is what
option B can claim: on this workload 784 M of fixed work became 346 M.

The `compile -t vm` row is the one workload that never compiled the
type-checker; it saves only the 66 M startup parse, and its wall clock is flat
within the run-to-run spread (the same command has measured between 4.65 s and
5.36 s here, `check leq` between 4.04 s and 4.58 s, and `repl` between 0.09 s
and 0.21 s — about ±10 % either way). A generated module large enough to hit
MicroHs's own compile-time limits was the risk named above: `mcabal build`
compiles the whole package, generated modules included, in about five minutes
at ~1 GB peak RSS — acceptable for a build step, and the flattening is the
knob if that changes.

The same change is on GHC's path too, but only as a cost: its `check leq`
spends part of its 0.166 s on the same parse and compile, while compiling a
1.7 MB literal-data module into four components on five CI compilers would be
paid at build time. GHC therefore keeps its Template Haskell splice, and
adopting the generated data there stays open, to be decided on a measurement.

### C. Interpreter hot path

This is the only lever on the 96 % that §3 attributes to the interpreter. Each
item names its evidence in §5.

1. **Resolve call targets at compile time.** `PROJECT.md`'s "Haskell Interpreter
   Performance" item 3 is still open; under GHC the interning experiment that
   would have fed it was measured as not worth it. Under MicroHs the arithmetic
   is different: `lookupProc` is 199 487 `Map Name` lookups with `Text`
   comparisons in this profile. Give `CallExpr` a procedure index and index host
   calls once at session init.
2. **Array-based locals.** The slot phase already numbers every local from one
   per-procedure counter. Let `SlotProc` carry its slot count and back `Env`
   with a single mutable array written in place, instead of two `IntMap`s
   rebuilt at every `insertVal`/`insertId` (`Env.envValues` + `insertVal` are
   ~16 % of entries here). A flat association list for small arities is a
   cheaper first cut.
3. **Flatten the monad.** Collapse the double `ReaderT` into one newtype over
   `SessionEnv -> IORef Env -> IO a` (or explicit state passing) and stop
   calling `ask` from helpers.
4. **Trace fast path.** Read "tracing is on" once per call into a `Bool`, skip
   constructing the event action when it is off, and do not touch
   `traceHandler` per event. `traceEntry`, `traceExit`, `withTraceDepth`,
   `emitTrace` and the handler projection together are ~11 % of entries for a
   subsystem that is disabled.
5. **`bindParams`**: drop the `length` + `zip [0..]` pair of traversals; walk
   the argument list once with a counter.
6. Merge `pushFrame` and `withSavedCallStack`, and materialise the call stack
   only on the error path.

Items 1–3 also help the GHC runtime, which is the benchmark of record; 4–6 are
mostly MicroHs-facing. Any of them needs `make bench` and a `make test` pass
before it can be judged.

### D. Front-end and `Data.Text` churn

Secondary, but cheap. `SExpr.printSExpr` builds its output through
`T.intercalate` and `Data.Text.Shim.concatMap`, and the shim's `concatMap` is
`T.concat (map f (T.unpack t))` — an `unpack`/`pack` round trip per element.
Implement the shim's hot conversions without the list round trip, or avoid
`concatMap` in the serializer. This is the serializer, so it shortens `compile
-t vm/scheme`, not `check`.

### E. Do not reach for `-flto -march=native` first

The `unix_x86` target that already exists in `mhs.conf`
(`-O3 -flto -march=native`) is measurably *slower*: `check pairs_library`
17.6 → 19.8 s, `check leq` 7.94 → 9.11 s, `compile typechecker/*.chr`
4.97 → 5.77 s, consistent across interleaved rounds. The measurement bundles
`-flto` and `-march=native`; if native flags are pursued, test
`-march=native` alone.

## 8. Open questions

- Is the `-H100M` `ERR: ARR_WRITE` abort (§4) a runtime bug or specific to this
  workload and heap size? It is the only thing standing between A and a default
  change, and it is worth a minimal reproducer regardless.
- ~~Can `mcabal` be made to run a pre-build step for B, or does the generated
  module have to be produced out of band by `make`?~~ No pre-build hook is
  visible in `mcabal`, and none was needed: the modules are produced out of
  band by `make resources`, and `autogen-modules` keeps `cabal check` and
  `cabal sdist` happy when they are absent. See B below.
- How much of C is worth doing? The profile says where the entries go, but
  entries are not reductions and the container calls inside those entries are
  uninstrumented; C needs an A/B per item, not a combined one.

## 9. Reproducing

```sh
# Install the pinned MicroHs toolchain and package set, then build: the
# resources are decoded by a separate build step, so `make resources` (or
# `make mhs-build`, which chains the two) has to run before `mcabal
# build`. No YCHR_LIB_DIR is involved: the resources are baked in.
make mhs-install
make resources
mcabal build

# Counters and the GC split.
./dist-mcabal/bin/mhs/ychr check typechecker/*.chr +RTS -v -RTS

# The heap experiment.
./dist-mcabal/bin/mhs/ychr check typechecker/*.chr +RTS -H400M -v -RTS

# Tick profile: build an instrumented binary in a scratch copy, then
# run any command with +RTS -T -RTS. The copy needs the generated
# modules too — copy them, or run `make resources` inside it.
mkdir -p .perf-scratch/ychr-tick
cp -a app embed libraries typechecker src ychr.cabal cabal.project \
  .perf-scratch/ychr-tick/
cp -a generated .perf-scratch/ychr-tick/
(cd .perf-scratch/ychr-tick && mcabal --options=-T build)
.perf-scratch/ychr-tick/dist-mcabal/bin/mhs/ychr check \
  test/golden/pairs_library/pairs_library.chr +RTS -T -RTS \
  | grep -E '^[A-Za-z]' | sort -k2 -nr | head -25
```
