# MicroHs Performance

`dev-docs/MICROHS_GAPS.md` records what stops YCHR from *building* under
MicroHs. This document records what stops it from running *fast* there, with
the measurements behind each claim and the options for fixing it. It began as
a diagnosis only: options A, D and E are still just that. Option B, the
`CallExpr` half of C.1, C.2 and the procedure-table half of C.8 have since
been implemented — their sections record what was built and what it measured
— and C.7 has been implemented twice and dropped both times, the second time
on the item 8 baseline: §7C.7 records both attempts, the measurements that
settled them, and why a `Data.Array` dispatch does not change the verdict.

Everything below was measured on 2026-10-05 against YCHR `d031947` (branch
`mhs-optimization`) and MicroHs `f65d3c65`, on an AMD Ryzen AI 9 HX 370. The
binary under test is the one `mcabal build` produces,
`dist-mcabal/bin/mhs/ychr`; the GHC build in `dist-newstyle` is the baseline.
Times are wall clock; most figures are single runs, and the ones used to judge
an A/B (the `-flto` comparison of §7E) are medians of interleaved rounds.
§7C.1's measurements were taken later, on 2026-10-08 on the same machine,
against `5e2d5a6`; they interleave three rounds a side and use the runtime's
counters, which are deterministic. §7C.8's were taken on 2026-10-09 against
`716f4b6`, with the same interleaved GHC rounds and the same deterministic
MicroHs counters. §7C.7's second attempt was measured on 2026-10-09 against
`8618597`, the item 8 baseline; unlike the runs above it was taken on a machine
with other work on it, and the per-round spreads it reports are correspondingly
wider.

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
   `ReaderT SessionEnv IO`, `InterpM` was `ReaderT (IORef Env) Chr` when this
   profile was taken (C.2 has since made it `ReaderT Env Chr`, §7C.2), and the
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

1. **Resolve call targets at compile time. — the `CallExpr` half implemented.**

   `PROJECT.md`'s "Haskell Interpreter Performance" item 3 is half closed:
   the procedure half is done, the host-call half is not (see the end of this
   item). Under GHC the interning experiment that would have fed it was measured
   as not worth it, but under MicroHs the arithmetic is different: `lookupProc`
   is 199 487 `Map Name` lookups with `Text` comparisons in this profile. The
   change lives entirely in the interpreter's own slot phase, so the VM IR, its
   serialization and the Scheme backend are untouched: `SCallExpr` carries a
   `CallTarget`, and `lowerProgram` resolves it to the callee's position in the
   program's procedure list (`ProcIx`). The interpreter reads the callee from
   `SessionEnv.procEntries` without a `Name`-keyed lookup. Query-time lifted
   lambdas are resolved by `Slots.addProcedures` against the union of the
   compiled names and their own, at the one point (`Session.withCHRExtra`) that
   extends the table. `interpret` and a hand-built `Program` keep the old
   name-based path, and a call target the program does not declare keeps its
   name and the interpreter's `unknown procedure` error; compiler output never
   produces one, and `YCHR.Internal.VM.Closure` now asserts that before a
   program is built (see `dev-docs/INVARIANTS.md`).

   **The table this item built was a `Map Int`, not an `IntMap`, and that is
   the first measured lesson of this item** (item 8 later replaced it with the
   array its own table picks; the lesson and the measurements stand). The first
   cut used `IntMap`, on the usual GHC intuition, and made MicroHs **15 %
   slower** on `check` — the opposite of
   every GHC measurement. A micro-benchmark isolated it: 2 000 000 lookups of
   pre-existing keys in a table of @n@ entries, with the key list forced
   identically in every run, so the difference is the lookup alone (`+RTS -v`):

   | table | reductions/lookup, n = 50 | reductions/lookup, n = 1000 |
   |---|---:|---:|
   | `Data.IntMap.Strict Int` | 716 | 1 186 |
   | `Data.Map.Strict Int` | 130 | 207 |
   | `Data.Map.Strict Text` | 172 | 285 |
   | `Data.Array Int` (boxed) | 89 | 89 |

   Two things follow. An `IntMap` lookup costs about 4 to 6 times a `Map Int`
   one under MicroHs, because MicroHs does not inline the `Data.Bits` work an
   `IntMap` search is built from. And a `Map` with `Text` keys costs only about
   1.4 times a `Map Int`: the comparison itself is a short loop, and re-keying a
   `Text` table to an `Int` one is a modest win by itself. What *is* a large win
   is a boxed `Data.Array`, at a constant ~89 reductions per lookup whatever
   `n` is, and building it is one `O(n)` pass rather than `n` insertions. Boxed
   arrays are lazy in their elements on both hosts, so an array can also carry
   unevaluated values (measured on MicroHs: building a 1 000-element array of
   thunks and reading one element costs ~79 000 reductions, forcing all of them
   ~27 100 000). Under GHC the ordering is the same —
   `Array` and `IntMap` allocate nothing per lookup, `Map` about 16 bytes,
   and a `Text`-keyed `Map` is the slowest in wall time — so `Array` is the one
   structure this item would pick for either host.

   This is worth knowing beyond this item: the interpreter's local environment
   (`Env`'s two `IntMap`s at the time, item 2, and §5's `envValues` and
   `insertVal` rows) was the largest remaining user of `IntMap` on the hot path,
   and it was exactly the container the table above says to replace. It was not
   changed here — that was a separate experiment with its own A/B, and it needed
   a slot count on `SlotProc` before an array could be sized. That experiment is
   item 2 below, and it has since been built and measured there.

   Measured on the change as a whole (this item plus the closure check; the GHC
   figures below are criterion, three interleaved rounds a side, medians of the
   per-round means):

   | workload | before | after | change |
   |---|---:|---:|---:|
   | GHC `typecheck/pairs_library` | 137.0 ms | 134.1 ms | −2.1 % |
   | GHC `leq_closure` | 6.850 ms | 6.450 ms | **−5.8 %** |
   | GHC `fib` | 387.6 µs | 365.3 µs | −5.7 % |
   | GHC `lambda_test` | 5.277 µs | 5.050 µs | −4.3 % |
   | GHC `leq` | 2.689 µs | 2.594 µs | −3.5 % |
   | GHC `sum_list_test` | 11.84 µs | 11.47 µs | −3.1 % |
   | GHC allocation, `check typechecker/*.chr` | 12.6251 GB | 12.6378 GB | +0.10 % |
   | MicroHs `check pairs_library` reductions | 1 162 711 319 | 1 150 992 368 | −1.01 % |
   | MicroHs `check leq` reductions | 372 727 056 | 369 807 962 | −0.78 % |
   | MicroHs `run --no-check` `leq` reductions | 3 454 598 | 3 587 576 | +3.9 % |
   | MicroHs `compile -t vm typechecker/*.chr` reductions | 503 036 831 | 506 765 590 | +0.74 % |
   | MicroHs `repl --quiet` reductions | 7 505 918 | 8 518 065 | +13.5 % |

   Two of the GHC micro-benchmarks are flat or noisy within their own spread
   (`guard` +1.6 %, `search_deep` flips sign between round orderings), and the
   GHC allocation figure is a small increase: the `Map Int` table allocates a
   little more than the `Map Name` one it replaces, and the interpreter more
   than earns it back in time. Attribution of the MicroHs regressions is
   measured, not guessed: a build with the closure walk removed puts
   `check pairs_library` at 1 150 108 340 reductions (**−1.08 %**, all of this
   item) and `repl --quiet` back at baseline, so `compile` and `repl` are the
   closure check's cost — 3.7 M and 1.0 M reductions, one walk over the
   program, and the price of closing `INVARIANTS.md`'s top suggested target.
   `run --no-check` is the one workload where this item itself costs more than
   it saves (+0.6 %): the program is small enough that lowering it dominates
   the few calls it makes.

   Not attempted here: indexing the host-call registry and keying the
   `evaluables`/`callables` tables by index rather than by `Name`. The first is
   item 7 below, which has since been built twice — most recently on the item 8
   `Data.Array` — and dropped on measurement both times; the
   second is the smaller, still-unclaimed remainder — one `Map` lookup per `is`
   and `'$call'` dispatch today, and `PROJECT.md` item 3's scope names them.
2. **Array-based locals. — implemented.** The slot phase already numbered every
   local from one per-procedure counter; the change gives `SlotProc` the
   counter's final value (`slotProcSlots`) and backs the interpreter's per-call
   environment with one mutable `IOArray Int Cell` written in place, instead of
   two `IntMap`s rebuilt at every `insertVal`/`insertId` (`Env.envValues` +
   `insertVal` are ~16 % of entries here). A `Cell` is a value, a suspension
   id, or empty; an empty cell is the slot a reference with no binder in scope
   reads, which is what keeps the interpreter's "unbound variable" error rather
   than a wrong value.

   The array is sized once per call, so `SlotProc` had to carry the count the
   walk ends at (`slotProcArity` is only a lower bound). The new field is lazy,
   like `slotProcBody`: the two are projections of one shared walk, so forcing a
   `SlotProc` for its name, index, arity or kind runs nothing, and the
   interpreter forces the count at call time, through the same thunk that
   supplies the body, so the walk still happens once. (A resolved call target is
   built as a thunk and holds nothing but a callee's index, so nothing in the
   phase needs a callee's body while another body is walking; the name-keyed
   `slotProcedures` map is strict in its values, so without the laziness forcing
   it would run every body's walk.) The reads and writes are
   `unsafeRead`/`unsafeWrite` from `Data.Array.Base`, bounded by the count the
   same walk produced: `SlotProc` is exported without its constructor, so only
   the phase can build one, and the count, the arity and every body slot come
   out of one walk. `bindParams` still checks the arity before it writes, so a
   call that disagrees with its callee cannot write past the array; the field
   exports keep the record readable everywhere it was before, so nothing outside
   `Slots` notices.

   Two things fall out of the array being mutable. The per-call `IORef Env`
   layer goes away: `withFreshEnv` is a `runReaderT` and the `BSoftGuard` catch
   sees the same array, so "bindings survive the catch" is unchanged with one
   less indirection per access. And the MicroHs runtime's `array alloc` counter
   does not move at all — 63 601 on `check leq` and 195 319 on `check
   pairs_library`, both unchanged to the digit — because MicroHs represents an
   `IORef` as a one-element array, so the per-call `IORef` this replaces and the
   per-call environment array are one array either way. What changes is the
   array's size and everything inside the accesses.

   Measured on 2026-10-09 against `8618597` on the same machine, as item 8 was:
   GHC figures are criterion, three interleaved rounds a side, medians of the
   per-round means (the percentages use the unrounded medians, so they need not
   recompute from the rounded figures below); MicroHs figures are `+RTS -v`
   reductions, which are deterministic (a second run repeats every figure
   exactly), with both binaries invoked through one symlink path because the
   counter includes a little startup work on the argument string, and the same
   inputs:

   | workload | before | after | change |
   |---|---:|---:|---:|
   | GHC `typecheck/pairs_library` | 118.99 ms | 115.45 ms | **−2.98 %** |
   | GHC `guard` | 3.381 µs | 3.339 µs | −1.25 % |
   | GHC `leq` | 2.677 µs | 2.640 µs | −1.39 % |
   | GHC `leq_closure` | 6.459 ms | 6.471 ms | +0.18 % |
   | GHC `fib` | 318.9 µs | 320.0 µs | +0.35 % |
   | GHC `sum_list_test` | 11.457 µs | 11.695 µs | +2.07 % |
   | GHC `graph_test` | 38.77 µs | 39.71 µs | +2.44 % |
   | GHC `lambda_test` | 4.865 µs | 4.960 µs | +1.95 % |
   | GHC `search_label` | 1.644 ms | 1.644 ms | +0.03 % |
   | GHC `search_label_alt` | 1.592 ms | 1.624 ms | +2.04 % |
   | GHC `search_generate` | 25.62 ms | 25.59 ms | −0.13 % |
   | GHC `search_deep` | 42.40 ms | 42.11 ms | −0.68 % |
   | GHC allocation, `check typechecker/*.chr` | 11.6239 GB | 11.2130 GB | −411 MB (−3.54 %) |
   | MicroHs `check leq` reductions | 352 501 266 | 228 504 960 | **−35.18 %** |
   | MicroHs `check pairs_library` reductions | 1 080 123 726 | 685 027 255 | **−36.58 %** |
   | MicroHs `run --no-check` leq reductions | 3 768 588 | 3 772 967 | +0.12 % |
   | MicroHs `run --no-check` fib(10) reductions | 7 523 580 | 6 579 734 | −12.55 % |
   | MicroHs `compile -t vm typechecker/*.chr` reductions | 507 044 800 | 507 044 749 | −0.00001 % |
   | MicroHs `repl --quiet` reductions | 8 805 690 | 8 805 690 | 0.00 % |
   | MicroHs `check leq` runtime | 4.06 s | 2.57–2.60 s | **≈ −36 %** |
   | MicroHs `check pairs_library` runtime | 13.19–13.20 s | 7.93–7.99 s | **≈ −40 %** |

   The MicroHs side is the verdict, and it is not close: the two `check`
   workloads lose a third of their reductions, `run fib(10)` loses an eighth,
   and their wall clock follows the reduction count (the ranges are two rounds
   a side). The arms that make no compiled call are flat — `repl --quiet` is
   bit-identical, `compile` moves by 51 reductions in a 507 M run, which is the
   lazy slot count doing its job. The one MicroHs arm that moves up is `run
   --no-check leq`, by 0.12 % (4 379 reductions in 3.77 M), a run whose
   interpreter work is a few calls over a program with almost no locals.

   On GHC the headline benchmark improves — `typecheck/pairs_library` −3.0 %,
   with its own before-side rounds at 118.1, 119.0 and 130.4 ms against after
   rounds at 114.2, 115.4 and 151.4 ms, so the medians separate and even the
   best round either side favours the change — and the allocation figure on
   `check typechecker/*.chr` falls 411 MB, which is the `IntMap` nodes the
   environment is no longer rebuilt from. The regressions are all in the
   call-and-bind microbenchmarks: up to +2.4 % (`graph_test` 38.8 µs,
   `sum_list_test` 11.5 µs, `search_label_alt` 1.6 ms, `lambda_test` 4.9 µs),
   and they are the price of allocating and filling an environment array per
   call, which the shortest procedures have few accesses to amortise. A repeat
   three-round comparison of the same change put `typecheck/pairs_library` at
   −2.68 % (118.49 → 115.32 ms), `sum_list_test` at +4.2 % and `graph_test` at
   +3.4 %: the win and the few-percent cost are the same across runs, and the
   small arms' exact figures are the benchmarks' own spread. `sum_list_test` was
   one of the three workloads this item named for its A/B, and it is the one
   named arm the change does not help (in the repeat its after rounds are 11.53,
   11.98 and 12.73 µs, so the median is lifted by an outlier while the lowest
   round sits inside the before range); `leq_closure` is flat here and +1.7 % in
   the repeat, inside the spread each run shows; `typecheck/pairs_library`
   carries the item.

   Not attempted here: the flat association list for small arities that this
   item suggested as a cheaper first cut. The per-call array fill is exactly
   what the GHC microbenchmarks pay for, so an arity-sized association list (or
   a shared empty environment for a procedure with no locals) is the shape a
   follow-up A/B would test, on the same three workloads. Also untouched: C.3's
   monad flattening and C.5's `bindParams` traversal — `bindParams` keeps its
   `zip [0 ..]` shape so that its own change stays a separate measurement.
3. **Flatten the monad.** Collapse the double `ReaderT` into one newtype over
   `SessionEnv -> Env -> IO a` (or explicit state passing) and stop calling
   `ask` from helpers.
4. **Trace fast path.** Read "tracing is on" once per call into a `Bool`, skip
   constructing the event action when it is off, and do not touch
   `traceHandler` per event. `traceEntry`, `traceExit`, `withTraceDepth`,
   `emitTrace` and the handler projection together are ~11 % of entries for a
   subsystem that is disabled.
5. **`bindParams`**: drop the `length` + `zip [0..]` pair of traversals; walk
   the argument list once with a counter.
6. Merge `pushFrame` and `withSavedCallStack`, and materialise the call stack
   only on the error path.

7. **Index host calls, and make compiled host dispatch symmetric with compiled
   procedure calls. — implemented twice, measured, and dropped.** Item 1 did the
   procedure half of this; the host half was still one `Map` lookup per call,
   `lookupHostCall` (1.83 M calls per run on the type-checker profile in
   `PROJECT.md` item 3). The registry is a runtime argument of `interpret`, and
   different callers hand in different ones (`defaultHostCallRegistry`, the
   search driver's, a host-built extension), so an index cannot be assigned at
   lowering time against the registry — but it can be assigned at lowering time
   against the *program*, and resolved against the registry once per session.

   The change was built exactly as follows, measured on 2026-10-09 against
   `716f4b6`, and reverted; the numbers that settled it are below.

   - Enumerate the host-call names a program's bodies mention, in order of
     first appearance, with a total walk over `Program` (one arm per VM
     constructor, no catch-all — `YCHR.Internal.VM.Closure` walks the same AST
     and is the model). The VM IR stays the serialization ABI, so the
     enumeration lives in the interpreter's own phase: `SlotProgram` gained the
     name list next to `slotProcEntries`.
   - `SlotValExpr.SHostCall` took a `HostIx` instead of a `Name` (the VM's
     `HostCall` and its serialization are untouched, as item 1 left them);
     `Slots.lowerProgram` and `Slots.addProcedures` assigned the index and
     extended the name list for query-time lambdas.
   - At session init the dispatch table was built from the program's name list
     and the registry the caller passed:
     `hostCallTable :: Array Int (Name, Maybe HostCallFn)`. Boxed arrays are
     lazy in their elements on both hosts (item 8), so each element is a
     `Map.lookup name registry` thunk: forced the first time that index is
     called, memoised for the rest of the session, never forced if the program
     never reaches it. The stored name keeps the unknown-host-call message.
   - `invokeHostCallAt :: HostIx -> [Value] -> Chr Value` read the table; the
     name-keyed `HostCallRegistry` stayed in `SessionEnv`, because `is`'s deep
     evaluator (`invokeByKey`, `valueKeyIsEvaluable`) resolves a functor name
     built at run time, and `YCHR.Run`'s query path looks up by name. Only the
     compiled `HostCall` sites moved to indices.
   - The closure check was to cover the host-name list too: the enumeration
     produced the list the lowering resolved against, so "an index past the end
     of the program's list" was unreachable from `lowerProgram` — a divergence
     between the two walks was an internal error — while an index naming no
     registry entry stayed the interpreter's runtime "unknown host call" (the
     registry is the caller's).

   **Two costs outweigh the per-call saving.** The first is the enumeration
   itself: it is a full walk of the VM AST, paid the first time a program makes
   a compiled host call, and for the precompiled type checker — whose
   `slotProgram` is a CAF — it lands once, on `check`. That is the same order
   as item 1's closure walk, which §7C.1 records at 3.7 M reductions on
   `typechecker/*.chr`. On MicroHs `check leq` goes 356 383 170 → 359 521 122
   reductions (+0.88 %) and `check pairs_library` 1 091 211 048 → 1 096 825 215
   (+0.51 %); those deltas are the walk, the second cost below and the dispatch
   saving combined. (§7C.1's figures are from `5e2d5a6`; these are from
   `716f4b6`, which includes the inlining change, so the two runs are not
   directly comparable.) The second is the table: it is O(host names) *per
   session*, and `initSessionEnv` rebuilds it for every goal, so the short GHC
   benchmarks — one session an iteration — see it. On `make bench` (criterion,
   three interleaved rounds a side):

   | workload | before | after | change |
   |---|---:|---:|---:|
   | `typecheck/pairs_library` | 119.67 ms | 117.84 ms | −1.5 % |
   | `fib` | 321.1 µs | 317.7 µs | −1.0 % |
   | `leq_closure` | 6.449 ms | 6.423 ms | −0.4 % |
   | `leq` | 2.626 µs | 2.597 µs | −1.1 % |
   | `guard` | 3.350 µs | 3.480 µs | **+3.9 %** |
   | `sum_list_test` | 11.49 µs | 11.99 µs | **+4.4 %** |
   | GHC allocation, `guard` + `sum_list_test` | 6.43 GB | 6.64 GB | +3.3 %, 2.1 kB a session |

   The two clean moves outside an interleaved spread are `guard` and
   `sum_list_test`, and both are regressions — the class that killed
   `PROJECT.md` item 1's host-call interning. `typecheck/pairs_library`'s
   −1.5 % is not a clean win: its feature rounds (114.7, 117.8 and 119.2 ms)
   overlap the baseline's (118.7, 119.7 and 120.0 ms), so it is inside the
   combined spread, and `fib`, `leq` and `leq_closure` are inside their own.
   The per-call arithmetic says why the saving cannot pay for the two costs
   above: measured under MicroHs on the same machine with a standalone program
   (2 000 000 lookups over a 32-entry table, keys forced identically), a
   `Map`-with-`Text` lookup costs 166 reductions and the deferred array element
   — `(!)` plus the pair and the `Maybe` — 119, so the dispatch change is worth
   ~47 reductions a call, while one 32-entry table build is ~107 reductions and
   the change as a whole allocates ~2.1 kB a session. `lookupHostCall` was 0.4
   points of `compare` in item 3's profile, so there was never much to win.

   Two things still distinguish this from `PROJECT.md` item 1's discarded
   host-call interning, which cost a fixed ~9 µs a session and regressed every
   short benchmark: the table was built by size, not by scanning the registry
   once per key, and the `Text` lookups were deferred and memoised rather than
   done eagerly at session init. Neither removes the enumeration walk nor the
   per-session table, which is where this attempt died. The laziness itself
   worked: `repl --quiet` (8 805 690 reductions) and `compile --no-check -t vm
   typechecker/*.chr` were unchanged to the digit, because neither forces the
   slot program on a path that runs a compiled host call, and MicroHs `run
   --no-check leq` moved +497 reductions (+0.01 %).

   Evidence: item 8's table — each call this removes is one `Map`-with-`Text`
   lookup, 172 reductions at a ~50-entry table under MicroHs, or the per-session
   array index (89) once the table exists. The count is workload-dependent:
   1.83 M on the type-checker profile, but `invokeHostCall` does not appear in
   §5's `check pairs_library` top 25, so the work was measured on `check
   pairs_library` and `compile`/`check typechecker/*.chr` under MicroHs and
   `typecheck/pairs_library`, `fib`, `sum_list_test`, `leq_closure` under GHC.
   Decision rule as item 1: keep for a move outside the interleaved spread with
   no session-init regression. It fails both halves, so the change was dropped
   and `PROJECT.md` item 3's `HostCall` half stays open; item 8's container
   choice is untouched by this result.

   **Second attempt: on the item 8 array table (2026-10-09, `8618597`).** Item 8
   has since put the procedure table behind a boxed `Data.Array` and brought
   `Data.Array` into the build on its own account, so the dispatch half was
   rebuilt on top of it, with the two costs the first attempt measured attacked
   directly.

   - The index space is unchanged — `SlotValExpr.SHostCall` carries a `HostIx`,
     the position of its name in `SlotProgram.slotHostCallNames` — but the
     element is bare. The first attempt's table was
     `Array Int (Name, Maybe HostCallFn)`, whose element measures 119
     reductions against 166 for the `Map`-with-`Text` lookup; the second
     attempt's is `Array Int (Maybe HostCallFn)`, with the names in the
     program's own shared array and the name read back only on the failure and
     trace paths. A dispatch is then one `(!)` and a `Maybe` case, whose
     floor is the bare array's 89.
   - The enumeration is fused into the closure walk the compiler already makes:
     `VM.Closure.programTargetsAndHostCalls` returns the dangling call targets
     and the host-call names in one traversal, and the precompiled
     type-checker's generated module emits the names as a literal, so nothing
     walks the 901-procedure program at MicroHs load time.

   GHC is criterion, three interleaved rounds a side, medians of the per-round
   means. The machine was not quiet for this change — per-round spreads ran
   1.4 to 14 % — so the rows that decide are read as the three base/after
   pairs. `typecheck/pairs_library` is faster in all three (115.0, 115.4 and
   120.4 ms against 120.4, 118.8 and 126.5 ms), `lambda_test` is slower in all
   three (4.99, 5.03 and 5.35 µs against 4.80, 4.87 and 5.01 µs), and `guard`
   is slower in two of the three (3.48, 3.36 and 3.66 µs against 3.31, 3.39 and
   3.29 µs). The other rows move by less than the range spanned by their six
   interleaved rounds (`sum_list_test` is inside its after-side spread but above
   its before-side one).

   | workload | before | after | change |
   |---|---:|---:|---:|
   | `typecheck/pairs_library` | 120.39 ms | 115.43 ms | **−4.1 %** |
   | `search_label_alt` | 1.620 ms | 1.569 ms | **−3.2 %** |
   | `sum_list_test` | 11.39 µs | 11.03 µs | **−3.1 %** |
   | `search_deep` | 42.33 ms | 41.30 ms | −2.4 % |
   | `search_label` | 1.651 ms | 1.614 ms | −2.3 % |
   | `leq` | 2.647 µs | 2.598 µs | −1.9 % |
   | `search_generate` | 25.25 ms | 24.94 ms | −1.2 % |
   | `leq_closure` | 6.439 ms | 6.363 ms | −1.2 % |
   | `fib` | 317.97 µs | 314.48 µs | −1.1 % |
   | `graph_test` | 39.46 µs | 39.36 µs | −0.3 % |
   | `lambda_test` | 4.87 µs | 5.03 µs | **+3.2 %** |
   | `guard` | 3.310 µs | 3.477 µs | **+5.0 %** |

   and MicroHs `+RTS -v` reductions (deterministic; two interleaved runs
   identical to the digit, so these are single runs a side):

   | workload | before | after | change |
   |---|---:|---:|---:|
   | `repl --quiet` | 8 805 690 | 9 190 290 | **+4.4 %** |
   | `check leq` | 352 464 694 | 355 449 511 | **+0.85 %** |
   | `check pairs_library` | 1 080 123 748 | 1 087 761 387 | **+0.71 %** |
   | `compile --no-check -t vm typechecker/*.chr` | 507 045 549 | 509 796 890 | +0.54 % |

   The GHC table is the trade-off in one place: the change is worth up to
   about 4 % on the call-heavy benchmarks that moved (`typecheck/pairs_library`,
   `sum_list_test` and the `search_*` arms; `graph_test` is flat), and costs 3
   to 5 % on the two benchmarks whose whole cost is opening a session and
   running one goal.
   The table is on the order of 4 kB a session — an estimate from the build,
   not an allocation measurement: 32 host-call names for a program the size of
   `guard`, whose prelude supplies almost all of them, and `listArray` over them
   allocates the array, a thunk per cell and a few list cells per name — against
   a 3 µs session. A second variant was built to separate the table's *size*
   from its *existence*: a mutable `IOArray Int (Maybe HostCallFn)` filled from
   the registry on first dispatch, which cuts the per-session allocation to a
   few hundred bytes (again an estimate) but puts an `IO` read on the per-call
   path. It did not turn the picture around — it improved only the proxy,
   `typecheck/pairs_library` −3.1 % with `search_generate` flat at −0.3 %, while
   `guard` +2.6 %, `lambda_test` +2.9 %, `graph_test` +4.6 %, `leq` +2.1 % and
   the remaining micro-benchmarks +0.3 % to +2.4 %. The session cost is therefore
   not simply the table's construction: any per-session table indexing 32 names
   is visible on a 3 µs session, and the memo that avoids one gives back the
   per-call win it exists for. (That variant was measured on GHC only.)

   MicroHs settles it on its own: every arm regresses. The *compile* arms show
   the fused walk's cost by itself — it runs on every compile, even one that
   never dispatches a compiled host call, where the first attempt's lazy
   enumeration left `repl --quiet` and `compile` untouched to the digit — and
   the *check* arms add the per-session table to it. Together they outweigh the
   47 to 77 reductions a call saves (§7C.1's array element, item 8's bare array)
   at the call counts a `check` reaches — unmeasured for these runs, but well
   short of the 1.83 M of the type-checker profile in `PROJECT.md` item 3. That
   is the same arithmetic the first attempt failed on, and it does not move.

   Decision rule as item 1, and the same answer as the first attempt: this fails
   the GHC session-init half (`guard`, `lambda_test`) and it fails MicroHs
   outright, so it was reverted and `PROJECT.md` item 3's `HostCall` half stays
   open. The item is no longer parked: two attempts — the first with a deferred
   `Map` lookup in each array element, the second with a bare element on item
   8's `Data.Array` — agree that indexing host calls does not pay under MicroHs,
   and that the GHC side can only pay by accepting a per-session regression the
   short benchmarks exist to catch. The `evaluables`/`callables` keys behind
   `is` and `'$call'` remain the smaller, still-unclaimed remainder of item 3.

8. **Back dense `Int`-keyed tables with `Data.Array`. — the procedure table
   implemented.** Item 1's container table is the evidence; the row to act on
   is the array's. In summary, per 2 000 000 lookups of pre-existing keys with
   the key list forced identically in every arm (so the figure is the lookup
   alone):

   | table | MicroHs reductions/lookup n = 50 | n = 1000 | GHC bytes/2 M | GHC wall n = 1000 |
   |---|---:|---:|---:|---:|
   | `Data.IntMap.Strict Int` | 716 | 1 186 | ~0.3 M | 0.02 s |
   | `Data.Map.Strict Int` | 130 | 207 | 32 M | 0.03 s |
   | `Data.Map.Strict Text` | 172 | 285 | 33 M | 0.12 s |
   | `Data.Array Int` (boxed) | 89 | 89 | ~0 | 0.01 s |

   An array is the fastest on **both** hosts and flat in `n`, so unlike the
   `IntMap`/`Map Int` choice it does not make the two builds disagree. `array`
   is available to both: GHC boot-provides it, and MicroHs bundles `Data.Array`
   (`array-mhs` is already in `tools/mhs-packages.txt`). It is now in the
   package's `build-depends` under the name `array`, which both builds accept:
   MicroCabal's `mhsPatchDepends` rewrites that name to `array-mhs` for the
   MicroHs backend, so no `impl(mhs)` conditional is needed. A standalone `mhs`
   program using `Data.Array` compiles today, which is how the numbers above
   were taken.

   The immediate change is one field, because its keys are already exactly
   `0 .. n - 1`:

   - `SlotProgram.slotProcEntries :: Array Int SlotProc`. `lowerProgram` builds
     it with `listArray`, over the same procedure thunks the name-keyed map
     holds; `Interpreter.callProcAt` reads it with `(!)`; `Slots.addProcedures`
     rebuilds it as `elems` of the base array followed by the extras' entries —
     extras arrive only for queries that lift lambdas, so the `O(n)` rebuild is
     on a cold path, and the no-extras case returns the program unchanged as it
     does today. Its `base` index is `snd (bounds arr) + 1` rather than the
     `Map.lookupMax` the map needed to stay correct if a program's keys were
     ever sparse, and an empty program's bounds are `(0, -1)`.
   - `SessionEnv.procEntries` is the array; nothing else moved.
     `slotProcedures` (name-keyed) stays a `Map`. The field is still lazy, so a
     run that makes no compiled call (`repl --quiet` startup, a compile-only
     invocation) never forces it, and the array's elements stay thunks.
   - `callProcAt`'s index read keeps its "stale procedure index" report behind
     an `inRange (bounds arr)` check: the array read alone would be an
     uninformative out-of-range error. The bounds come from the same
     `SlotProgram` the AST was lowered from, so the check can only be false for
     a stale index.

   Measured as item 1. GHC figures are criterion means, three interleaved rounds
   a side, medians of the per-round means (the percentages use the unrounded
   medians, so they need not recompute from the rounded figures shown); MicroHs
   figures are `+RTS -v`
   reductions, one run a side (the counters are deterministic — a second round
   repeats every figure exactly), with both binaries invoked through the same
   symlink path because the counter includes a little startup work on the
   argument string, so two binaries called under different paths differ in
   figures that have nothing to do with the change; allocation is
   `check typechecker/*.chr` under `+RTS -s`:

   | workload | before | after | change |
   |---|---:|---:|---:|
   | GHC `typecheck/pairs_library` | 119.90 ms | 117.97 ms | −1.61 % |
   | GHC `fib` | 319.0 µs | 311.3 µs | −2.41 % |
   | GHC `leq_closure` | 6.550 ms | 6.495 ms | −0.85 % |
   | GHC `search_label` | 1.668 ms | 1.617 ms | −3.07 % |
   | GHC `search_label_alt` | 1.622 ms | 1.565 ms | −3.48 % |
   | GHC `search_generate` | 25.51 ms | 24.83 ms | −2.68 % |
   | GHC `search_deep` | 42.85 ms | 42.59 ms | −0.62 % |
   | GHC `graph_test` | 40.8 µs | 38.9 µs | −4.68 % |
   | GHC allocation, `check typechecker/*.chr` | 11.6239 GB | 11.5938 GB | −30 MB (−0.26 %) |
   | MicroHs `check pairs_library` reductions | 1 091 211 048 | 1 080 123 725 | −1.02 % |
   | MicroHs `check leq` reductions | 356 383 161 | 352 501 266 | −1.09 % |
   | MicroHs `run --no-check` leq reductions | 3 781 323 | 3 768 588 | −0.34 % |
   | MicroHs `run --no-check` fib(10) reductions | 7 542 098 | 7 523 580 | −0.25 % |
   | MicroHs `compile -t vm typechecker/*.chr` reductions | 507 057 498 | 507 057 353 | −145 (−0.00003 %) |
   | MicroHs `repl --quiet` reductions | 8 805 690 | 8 805 690 | 0.00 % |

   The wins are where the table is read: `check pairs_library` and `check leq`
   each lose about 1 % of their reductions, the compiled-call-heavy GHC
   benchmarks (`fib`, `search_label`, `search_label_alt`, `search_generate`)
   move down −2.4 % to −3.5 %, and `graph_test` is cleanly separated at
   −4.7 %. `leq_closure` (−0.9 %) and `search_deep` (−0.6 %) overlap their own
   spread, as do the four sub-20 µs benchmarks (`guard`, `leq`, `sum_list_test`,
   `lambda_test`). The arms that make no compiled call or almost none are flat:
   `repl --quiet` is bit-identical and `compile` moves by 145 reductions in a
   507 M run, which is the lazy field doing its job. Allocation drops 30 MB per
   `check typechecker/*.chr`, the map's per-lookup allocation disappearing. No
   workload regresses outside its spread, and `make test` passes unchanged:
   this is a container change and no observable behaviour moves.

   Not attempted here: the larger version, item 2's array-backed locals — built
   and measured since, in item 2 below. This measurement is what argued for it:
   `envValues` and `insertVal` are ~16 % of the profiled entries, and `IntMap`
   is the container this table says is worst under MicroHs. It needed one
   addition first: an array must be sized before the body runs, and slots are
   handed out as the walk meets binders, so `SlotProc` must carry the number of
   slots the body uses (the slot phase counts them; only the arity was carried
   then). Slots are dense from `0`, but a slot may be value-bound or id-bound,
   so the environment array needs one entry per slot with enough shape to hold
   either — `Maybe Value` / `Maybe SuspensionId`, or one array of a sum type,
   rather than the two `IntMap`s. Item 2 took the array of a sum type. The
   environment is read and written per variable access rather than per call, so
   its A/B was the one that decided, and it wanted `sum_list_test`,
   `leq_closure` and the type-checker workload.

Items 1–3 and 7–8 also help the GHC runtime, which is the benchmark of record;
4–6 are mostly MicroHs-facing. Any of them needs `make bench` and a `make test`
pass before it can be judged.

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
  uninstrumented; C needs an A/B per item, not a combined one. C.1's
  micro-benchmark (§7C.1) is a worked example of settling one: it turned a
  15 % regression into a 1 % win by measuring the container, not the entry
  count.
- ~~Is `IntMap` the right structure for the interpreter's local environment?~~
  No: item 2 replaced both `IntMap`s with one boxed mutable array, and the
  measurement there is what settles it. The container measurements that pointed
  at an array are in §7C.1 and item 8; item 8 named what an array-backed `Env`
  needed first (a slot count on `SlotProc`) and how to judge it, and item 2 was
  run separately from the procedure-table change, as this question asked.

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

The container numbers of §7C.1 and item 8 come from a standalone program, not
from the `ychr` binary, because the question is the container and not the
interpreter. Save this as `containers.hs`; every mode forces the same
2 000 000-key `Text` list first (`ik` is that baseline), so a mode's difference
from `ik` is its lookup cost:

```haskell
{-# LANGUAGE OverloadedStrings #-}
module Main where

import qualified Data.Array as A
import qualified Data.IntMap.Strict as IM
import qualified Data.List as L
import qualified Data.Map.Strict as M
import qualified Data.Text as T
import System.Environment (getArgs)

forceKeys :: [T.Text] -> Integer
forceKeys = L.foldl' (\acc t -> acc + fromIntegral (T.length t)) 0

main :: IO ()
main = do
  args <- getArgs
  let mode = case args of (m : _) -> m; [] -> "ik"
      n = case args of (_ : s : _) -> read s; _ -> 1000
      ks = [(i * 7919) `mod` n | i <- [0 .. 2000000]]
      tks = map (T.pack . show) ks
      im = IM.fromList [(i, i) | i <- [0 .. n - 1]]
      mi = M.fromList [(i, i) | i <- [0 .. n - 1]]
      mt = M.fromList [(T.pack (show i), i) | i <- [0 .. n - 1]]
      ar = A.listArray (0, n - 1) [i | i <- [0 .. n - 1]]
      base = forceKeys tks
      r = case mode of
        "ik" -> base
        "im" -> base + fromIntegral (sum [v | k <- ks, Just v <- [IM.lookup k im]])
        "mi" -> base + fromIntegral (sum [v | k <- ks, Just v <- [M.lookup k mi]])
        "mt" -> base + fromIntegral (sum [v | k <- tks, Just v <- [M.lookup k mt]])
        "ar" -> base + fromIntegral (sum [ar A.! k | k <- ks])
        _ -> 0
  print r
```

```sh
mhs -o containers-mhs containers.hs
for n in 50 1000; do for m in ik im mi mt ar; do
  ./containers-mhs $m $n +RTS -v -RTS | grep -E 'reductions'
done; done

ghc -O2 -rtsopts containers.hs -o containers-ghc
for m in ik im mi mt ar; do ./containers-ghc $m 1000 +RTS -s; done

# The per-lookup figure is (a mode's reductions - ik's) / 2 000 000;
# the GHC figure is the difference in "bytes allocated" over ik, same
# division. Note the baseline: a benchmark arm that builds its own
# Text keys and one that reuses existing ones differ by far more than
# the lookup they are meant to compare — the first cut of this table
# got Map Text vs Map Int backwards by measuring construction.
```

