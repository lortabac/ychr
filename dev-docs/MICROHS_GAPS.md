# MicroHs Gaps

This document lists the features missing from MicroHs (the
`mhs`/`mcabal` toolchain at `/home/lorenzo/Development/MicroHs/`)
that prevent YCHR from building under `mcabal build`. The GHC build
(`cabal build`) is unaffected.

The ideal resolution is to fix each gap upstream in MicroHs. For
those where an upstream fix is not feasible (or until one lands),
each entry also records a YCHR-side workaround. The workarounds are
explicitly second-best: if patching the YCHR code accumulates enough
verbosity or special-casing to hurt readability, we may decide to drop
MicroHs compatibility rather than carry the debt indefinitely.

Each entry has a concrete reproducer, an upstream fix sketch, and a
local workaround. For the format, see `SCHEME_BACKEND_GAPS.md` —
terse, fix-shaped, removable when closed.

## Status

Re-verified against upstream MicroHs `c98846b1` (2026-11-05,
`mhs` 0.16.12.0). Seven gaps are open; six have closed and been removed
from this document (see below the table). The local workarounds for
gaps 1, 5, 6, 8 and 10 are applied (gap 5 is the resources provider
described below, which since `dev-docs/MICROHS_PERFORMANCE.md` option B
decodes its two resources at build time rather than at run time; gap 8
is one no-op modifier; gap 10 is one helper taking its argument as
`Text` rather than as a record). Gap 11 has no YCHR-side workaround: it
is a difference in how coarsely file-open errors are reported, not a
crash. The reproducers for gaps 1, 2, 6, 10 and 11 were rerun at
`c98846b1` and still fail; gap 8 depends on the optparse-applicative
pin, which did not move. At this revision a type error reads
`type mismatch` / `expected:` / `actual:` rather than the
`Cannot satisfy constraint: X ~ Y` quoted in the older entries. The pin
is `c98846b1` and not upstream's head `4b1b88e6`, which fails to
bootstrap (`src/MicroHs/Parse.hs:886`: `undefined value: rights`).
No Template Haskell remains in `library ychr`, and the `ychr` executable
has a MicroHs twin of the compile-time embedder, so `mcabal build` now
completes: it builds `library ychr` and `exe:ychr`, and the binary runs
on `libraries/*.chr` and `typechecker/*.chr` decoded at build time by
`make resources` — no run-time lookup, and `YCHR_LIB_DIR` no longer
affects it. `mcabal build` does not build the test
suite, the benchmark or the `stlc` example (they need
`tasty`/`hedgehog`/`criterion`, which the MicroHs package set lacks, and
the `examples` flag defaults off), so those remain GHC-only. CI compiles
the MicroHs target on every push and pull request — the `microhs` job,
which runs no tests — from the environment `make mhs-install` installs:
MicroHs `c98846b1`, the prettyprinter and optparse-applicative commits
pinned in `tools/mhs-install.sh`, and the package versions in
`tools/mhs-packages.txt`. Keep those pins in sync with this paragraph.
Gap 8 was found on the way to that point and is recorded below.

| # | Gap | State |
|---|---|---|
| 1 | `OverloadedRecordDot` rejects an already-bound field name | open — workaround applied to `src/` (see below) |
| 2 | `NoFieldSelectors` silently ignored | open |
| 5 | No `TemplateHaskell` support | open upstream — workaround applied: no TH in `library ychr`; the MicroHs `ychr` compiles resources decoded at build time by `make resources` (see below) |
| 6 | `mapAccumL` is list-only | open — no site left in `src/` (see below) |
| 8 | `optparse-applicative`'s `fullDesc` is missing from the MicroHs package | open — workaround applied to `app/Main.hs` (see below) |
| 10 | A local binding inferred as `HasField`-polymorphic is not generalized | open — workaround applied to `src/YCHR/Internal/Resolve.hs` (see below) |
| 11 | File-opening errors carry no description | open upstream — no YCHR-side workaround (see below) |

Record update after a field selection (`e.fld { f = … }`, formerly
gap 3) parses since upstream `c17e43de` (#566). The selectors hoisted
into local bindings in `Desugar.hs` and `Desugar/Disjunction.hs` are
inlined again.

`Data.List.elem` and `notElem` (formerly gap 7, a number reused after
the `try` gap below closed) are `infix 4` since
upstream `8f108ebd` (#564). The parentheses in `Display.hs`'s
`ConstructorFunctionAmbiguity` message are gone.

`Data.Either.partitionEithers` (formerly gap 5) is now exported by
MicroHs (`lib/Data/Either.hs:51`) and used directly by
`src/YCHR/Internal/Parser.hs`; that entry is gone.

`Control.Exception.try` (formerly gap 7) now orders its type variables
the way `base` does (`MicroHs/lib/Control/Exception.hs:106`, upstream
`0a1c3095`); `Control.Exception.Shim` is deleted and its importers
reverted.

The missing `Data.Text` functions (formerly gap 4) are in MicroHs since
`d3566ca6` ("Make Data.Text more complete"): `breakOn`, `breakOnEnd`,
`concatMap`, `last`, and also `splitAt`, `span` and `break`, all
matching `text` on the cases the old shim test pinned. `Data.Text.Shim`
and `YCHR.TextShimTest` are deleted, the importers use `Data.Text`
again, and `VM.SExpr.qualifiedNameOfTellProc` uses `T.breakOn` instead
of a hand-written split over `String`.

`Data.Text.replicate` with a zero count (formerly gap 9) returns `""`
now (`lib/Data/Text.hs:214`), so the MicroHs `ychr` renders `--help`
and usage-error screens.

Each entry below opens with a **Re-verified** note recording what
changed, if anything, since it was written.


## 1. `OverloadedRecordDot` rejects a field name that is already bound

> **Re-verified against MicroHs `3322c60a` and `mhs` 0.16.6.0.** Still open,
> and considerably broader than this entry first recorded: the trigger is
> *any* field name that also resolves to a non-selector binding, not just
> `head`. See "Breadth" below.
>
> The workaround below is applied to `src/`; what remains open is the
> MicroHs side (`isLabel`).

A blocker. `e.fld` is a field access only when `isLabel fld` says so
(`MicroHs/src/MicroHs/TypeCheck.hs:2180`):

```haskell
isLabel i = do
  env <- gets valueTable
  case stLookup "" i env of
    Left _ -> return True
    Right (Entry (EVar g) t) ->
      return $ isInfixOf "get$." (unIdent g) || countArrows t == 0
```

`stLookup "" i` is an **unqualified** lookup, and `isLabel` reads `Left`
— which `stLookup` returns both for "undefined" and for "ambiguous" —
as "yes, a label". So a field is rejected exactly when its name alone
resolves to one non-selector binding: at least one arrow, and no `get$.`
in the name. `Prelude.head` is such a binding. The lookup finds
`Data.List.head` uniquely, `isLabel` returns `False`, and the
typechecker rewrites the `ESelect` to composition. `r.head` becomes
`r . head`, which surfaces as:

```
Cannot satisfy constraint: Rule ~ (_a6 -> _a7)
```

Reproduced on `mhs` 0.15.10.0 (MicroHs `3322c60a`):

```haskell
-- R.hs
{-# LANGUAGE DuplicateRecordFields, NoFieldSelectors #-}
module R where
data Rule = Rule { head :: Int, kept :: Int }

-- Main.hs
{-# LANGUAGE OverloadedRecordDot #-}
module Main where
import qualified R
main :: IO ()
main = print ((R.Rule 1 2).head)
```

| use site | result |
|---|---|
| `import R` (open) | compiles |
| `import qualified R` | fails (`Rule ~ (_a -> _b)`) |
| `import R (Rule(..))` | compiles |
| `import R (Rule)` (type only) | fails (`Rule ~ (_a -> _b)`) |
| `import Prelude hiding (head)` + qualified `R` | compiles |
| `.kept` (a name not in `Prelude`), any import style | compiles |

The open-import column works only by accident: the import puts the
record's label `head` in scope next to `Data.List.head`, so the lookup
is ambiguous between `Data.List.head` and `R.get$.Rule.head` — the same
`Left` `isLabel` mistakes for a label.

### Impact on YCHR

Confirmed directly. Compiling the library under `mhs` fails first at
`src/YCHR/Internal/Pretty.hs:123` (`r.head.node`) with

```
Cannot satisfy constraint: Head ~ ([_a7169] -> _a7170)
```

and the error walks from module to module as each site is worked around.
The documented `import Prelude hiding (head)` fix does resolve it there,
but it does **not** resolve every site — see below.

#### Breadth: it is not just `head`

Intersecting every record field name declared under `src/` with the
exports of MicroHs's libraries gives five colliding names:

| field | `.field` uses | files |
|---|---|---|
| `head`     | 23 | 10 |
| `guard`    | 23 | 9  |
| `functions`| 15 | 7  |
| `length`   | 6  | 4  |
| `index`    | 1  | 1  |

Roughly 68 use sites in total. Minimal reproducer for a non-`head` case
(same failure shape):

```haskell
-- P3.hs
{-# LANGUAGE DuplicateRecordFields, NoFieldSelectors #-}
module P3 where
data R = R { length :: Int, guard :: Int, index :: Int, functions :: Int }

-- Main.hs
{-# LANGUAGE OverloadedRecordDot #-}
module Main where
import qualified P3
f :: P3.R -> Int
f r = r.length + r.guard + r.index + r.functions
-- Cannot satisfy constraint: Int ~ ([_a16] -> _a9)
```

Two variants defeat the `hiding` workaround outright:

- **The colliding name is a local function, not an import.** In
  `src/YCHR/Internal/TypeCheck/Encode.hs`, the module defined its own
  `guard :: D.Guard -> Term` (renamed `guardTerm` by the workaround
  below), and `r.guard` (`:230`) failed with
  `Rule ~ (Term -> [Guard])`. There is nothing to `hide` — the name is in
  scope because the module defined it.
- **Both the field and the function are needed.** In
  `src/YCHR/Internal/Runtime/Monad.hs`, `TrailState` has a `length` field
  and the module also calls the list function; hiding the import is not an
  option. Qualifying the call (`List.length`) works, but it is a per-site
  rewrite.

The table above is an upper bound, not a site list: a name only breaks a
use site when it is uniquely in scope *there* as a non-selector value,
which the open-import accident can prevent. Sweeping `src/` module by
module against `mhs` 0.16.6.0 leaves three real collisions:

| collision | where | why |
|---|---|---|
| `head`     | 21 `.head` uses, 8 modules | `Prelude.head` is the unique non-selector binding: the declaring module is imported qualified, or with a list that omits `Rule`, so no field label competes |
| `length`   | `Runtime/Monad.hs:176` | the module imports `TrailState (..)`, putting the selector and the list function in scope together |
| `guard`    | `TypeCheck/Encode.hs:230` | the module defined its own top-level `guard` |

`functions` and `index` never collide: no unqualified binding of either
name is ever in scope at a `.functions`/`.index` use. Two further cases
compile untouched, through the open-import ambiguity described above:
`Rename.hs` (its `Parsed` import is open) and the `.length` use in
`Runtime/Trail.hs` (the open `TrailState (..)` import).

#### Chained selectors report a misleading downstream error

When a chain such as `r.head.removed` is involved, the first selector
resolving to `Prelude.head` pushes the failure onto the *second* field,
which then surfaces as a `HasField` error rather than the `~` error:

```
Cannot satisfy constraint: HasField "removed" (AnnP Head) [_a315]
```

This is the same gap, not a separate one. It is what
`src/YCHR/Internal/Compile/Occurrences.hs:107-108` and
`src/YCHR/Internal/Compile.hs:484` report once `head` has been hidden; the
chain still fails because the earlier link is misresolved. Expect to see
both error shapes while working through a build.

### Upstream fix sketch

Make `isLabel` decide from an explicit field-label table rather than
from an unqualified value lookup: register the label when the record is
declared, and treat ambiguity as a real ambiguity (or resolve it
against the expected type) instead of as a label. The `get$.`-prefix
heuristic on the resolved global name is what ties this to gap 2.

### Local workaround

Add `import Prelude hiding (head)` at the `.head` use sites (it also
hides the list function there). Importing the field's own module
**unqualified** (open) also works, but only through the accidental
ambiguity above, and it is not viable where `Parsed` and `Desugared`
are needed together (their `Rule`/`Head` types collide). Fields whose
name is not otherwise bound (e.g. `kept`) need nothing.

The same `hiding` line generalises to `length`, `guard`, `functions`
and `index` — but only where the collision is with an *import*. Where
the colliding name is a local definition (`Encode.guard`) or where both
meanings are needed in one module (`Monad.length`), the workaround does
not exist and each site needs a bespoke rewrite (qualify the function,
or bind the record through a non-colliding path). The earlier note that
"a module that open-imports one does not [fail]" still holds, but the
practical conclusion is the opposite of reassuring: the workaround is
per-site, not per-module, and does not compose.

### Local workaround (applied)

Applied to `src/`:

| edit | sites |
|---|---|
| `import Prelude hiding (head)` | `Compile.hs`, `Compile/Aggregate.hs`, `Compile/Occurrences.hs`, `Compile/Passive.hs`, `ConstraintUse.hs`, `Desugar.hs`, `Desugar/Disjunction.hs`, `Desugar/Inline.hs`, `Pretty.hs`, `Resolve.hs`, `TypeCheck/Encode.hs` |
| local `guard` renamed to `guardTerm` | `TypeCheck/Encode.hs` |
| `length` qualified as `List.length` | `Runtime/Monad.hs:176` |

Hiding the list function is safe in all eleven modules: none of them
calls it. `Rename.hs` and `Runtime/Trail.hs` are left alone (see "Breadth"
above).

Two error shapes the sweep produced that belong to this gap and are not
listed above:

- `undefined value: node` (or `removed`) — the *first* link of a chain
  misresolves, so the next selector is read as a value;
- `ambiguous value: length [Data.List.length, ...get$.TrailState.length]`
  — a bare call to the list function while a same-named selector is in
  scope; the message names both candidates.

Verified module by module with `mhs -fno-code` on a scratch copy of
`src/`: with the edits above, `Compile/Passive.hs`,
`Compile/Occurrences.hs`, `Compile.hs`, `Pretty.hs`, `Resolve.hs` and
`TypeCheck/Encode.hs` compile. `Desugar.hs` and
`Desugar/Disjunction.hs` cleared the gap-1 error and then stopped on
record-update-after-selector sites (`func.equations {node = …}`,
`ctx.bodyAnn {node = …}`), not on this gap; those compile as well now
(that gap is closed, see the Status section). `Runtime/Monad.hs` sits behind them through
`Compile.Pipeline`, so its call was checked with the equivalent
`TrailState` reproducer instead (`ambiguous value: length […]` without
the qualification, accepted with it). There was still no end-to-end
check at the time: the library stopped on the `elem` fixity gap before
the CLI was reached, and the `try` gap was worked around only after
this sweep. Both have since been closed, and `mcabal build` now builds
the CLI too (see the Status section).
The test component is out of reach as well (`tasty` and `hedgehog` are
not in the MicroHs package set), so
`test/YCHR/RoundtripTest.hs:159` — the same `.head` collision, on a
qualified `Parsed` — keeps it and is left as is.

### History

This entry previously diagnosed a cross-module collision of the
generated selectors and prescribed qualifying `mkGetName`
(`Deriving.hs:171`) with the module name. MicroHs already does that
later, via `extValETop` (`TypeCheck.hs:872`) — the emitted name is
`R.get$.Rule.head` — so that diagnosis no longer reproduces (nor does
the `HasField "kept" _a3940` error); only the `Rule ~ (_a -> _b)` error
above survives, from `isLabel`.


## 2. `NoFieldSelectors` is silently ignored

> **Re-verified.** Still open: a module declaring
> `{-# LANGUAGE NoFieldSelectors #-}` and `data R = R { head :: Int }`
> still accepts `R.head (R 1)`, so the selector is still generated.

`MicroHs/src/MicroHs/Deriving.hs` unconditionally emits the field
selector function for every record (`Sign [getName]` + `Fcn getName`).
There is no check for the `NoFieldSelectors` extension; the pragma is
silently dropped by the lexer (`Lex.hs`, `pragma`) and has no effect on
code generation.

This is what ties it to gap 1. Despite `NoFieldSelectors`, MicroHs
registers each field's own name (`head`) as a label for the generated
selector, and `isLabel`'s `get$.` heuristic exists to recognise exactly
that; GHC never introduces the name, so the unqualified lookup cannot
land on it. Suppressing the selector alone is not the fix, though: the
lookup would still find `Prelude.head`, which is why gap 1's fix
belongs in `isLabel`.

### Upstream fix sketch

Honour `NoFieldSelectors` in `expandField` — when enabled, skip the
`Sign [getName]` / `Fcn getName` pair and inline the case-match
directly into the `HasField` instance method. The label registration in
`addValueType` / `addField` (`TypeCheck.hs:1557-1563`) looks the
selector up and errors when it is absent, so that has to change with
it. This is not on its own a fix for gap 1 either: `isLabel` must stop
deciding from an unqualified value lookup, or `.head` has no reliable
way to resolve at all.

### Local workaround

None directly — this gap is observable only through gap 1, and its
workaround is the same.


## 5. No `TemplateHaskell` support

> **Re-verified, and now closed on the YCHR side.** Still open upstream —
> mhs has no staged compilation and never will (see "Root cause"). The
> `ychr` *library* uses no TH at all, and the `ychr` *executable* has a
> MicroHs twin of its compile-time embedder, so `mcabal build` completes.
> The twin no longer re-decodes the resources in every process: it
> compiles the modules `make resources` emits, so the MicroHs side has no
> run-time resource path either. TH is confined to the shared `embed/`
> source directory, which only the components that want a self-contained
> GHC binary compile: the `ychr` executable, the test suite, the
> benchmark and the `stlc` example.

MicroHs is a combinator-based compiler with no staged compilation.
The `TemplateHaskell` extension is not recognised; modules using it
cannot build under `mcabal`.

YCHR used TH inside the library to embed `libraries/*.chr` and the type
checker's `typechecker/*.chr` into the binary at compile time. That made
the GHC-built binary self-contained and cwd-independent — but it also
made `template-haskell` an unconditional dependency of `library ychr`, so
`mcabal` stopped during dependency resolution, before compiling
anything.

### Root cause

`MicroHs/src/MicroHs/Lex.hs` and `Parse.hs` have no quotation /
splice grammar; the compiler has no staged-evaluation phase.
Implementing TH would require a second compilation pass over
splice-producing modules and a runtime evaluator for `Q` actions —
effectively another compiler. Not realistic as an upstream fix; TH
is a non-goal for MicroHs by design.

### Upstream fix sketch

None viable.

### Local workaround (applied)

The embedding moved out of the library into the shared `embed/` source
directory, and the two resources it produces are explicit inputs of the
library's API:

| file | role |
|---|---|
| `embed/YCHR/Embedded/StdLib.hs` | splice of `libraries/*.chr`, moved from `YCHR.Internal.StdLib.TH` |
| `embed/YCHR/Embedded/TypeCheck.hs` | splice of `typechecker/*.chr`, moved from `YCHR.Internal.TypeCheck.TH` |
| `embed/YCHR/Embedded.hs` | applies both splices; exports `stdlib :: StdLib` and `typeCheckerProgram :: SessionInput` |

`embed/` is listed in the `hs-source-dirs` of `exe:ychr`,
`exe:stlc-typechecker`, `test:ychr-tests` and `bench:ychr-bench`; those
four components carry the `template-haskell` dependency (under
`if impl(ghc)`, so at least dependency resolution no longer sees it) and
list the three modules in `other-modules`. `library ychr` has neither
the dependency nor the modules: it takes the parsed standard library
(`StdLib`, built by `parseStdLib`) and the compiled type-checker
(`SessionInput`, built by `compileTypeCheckerModules`) as explicit
arguments — see
`docs/how-to/embed-a-chr-module.md#5-supplying-the-resources`.

The mhs side is the *provider* for those two values:
`src/mhs/YCHR/Embedded.hs` is the MicroHs twin of
`embed/YCHR/Embedded.hs`, switched in by the executable's
`hs-source-dirs` under `if impl(mhs)`. It reads nothing at run time: the
executable compiles the modules under `generated/`, which `make
resources` writes by decoding `libraries/*.chr` and `typechecker/*.chr`
with the library's own `parseStdLib` / `compileTypeCheckerModules`
(`dev-docs/MICROHS_PERFORMANCE.md`, option B; `generated/README.md`).

| file | role |
|---|---|
| `codegen/Main.hs` | generator entry point: writes `generated/`, `--check` reports staleness |
| `embed/YCHR/Embedded/Generate/` | the emitter — a `Code` tree, a `ToCode` class with `GHC.Generics` defaults, and the hoisting/assembly pass |
| `generated/YCHR/Embedded/Generated/StdLib.hs` | generated: `stdlib :: StdLib` |
| `generated/YCHR/Embedded/Generated/TypeCheck.hs` | generated: `typeCheckerProgram :: SessionInput` |
| `src/mhs/YCHR/Embedded.hs` | re-exports the two generated values as the executable's `YCHR.Embedded`, plus a `loadResources` that cannot fail |
| `embed/YCHR/Embedded.hs` | GHC twin: `loadResources` returns the compile-time-embedded `stdlib` / `typeCheckerProgram` |
| `src/YCHR/Internal/Resources.hs` | the on-disk loader (`readChrDir`, `loadResourcesAt`, the `YCHR_LIB_DIR` policy); no bundled provider calls it any more |

The executable imports only `YCHR.Embedded (loadResources)` and threads
the returned `Resources` through its subcommands, so `app/Main.hs` is one
source file for both compilers. Resources are obtained after the command
line is parsed, so `--help` and usage errors work without a source tree.
Both providers now hand back already-decoded values, so neither can fail;
`app/Main.hs` keeps its error branch because the loader's type admits a
failure.

The generated modules are listed in `other-modules` and `autogen-modules`
under `if impl(mhs)` — the latter so that `cabal check` and `cabal sdist`
pass on a checkout where `make resources` has not run — and they are
gitignored. Only `generated/README.md` is committed, because Cabal
rejects an `hs-source-dirs` entry that names a missing directory even
when it sits in a conditional for another compiler. `YCHR_LIB_DIR` no
longer affects the bundled executable; it is honoured only by an embedder
that calls `YCHR.Internal.Resources` itself.

Verified on this revision:

- `make resources` writes both modules (1.7 MB total) and is idempotent;
  `make resources-check` reports `generated resources are up to date`.
- `mcabal build` completes: it builds `library ychr` and `exe:ychr`, the
  latter compiling `generated/YCHR/Embedded/Generated/*.hs` as well. The
  executable is compiled with `-iapp -isrc/mhs -igenerated` (not
  `-iembed`), so `Language.Haskell.TH` is never reached.
- `dist-mcabal/bin/mhs/ychr run --show-bindings -g 'order:leq(X, X)'
  test/golden/leq/leq.chr` prints `X = _`, from the repo root and from any
  other directory, with or without `YCHR_LIB_DIR` set: the variable no
  longer has any effect. `repl`, `compile`, `gen-driver` and `check` work
  too. (`--help` and usage-error screens used to trip the
  `Data.Text.replicate` gap, since closed; it was unrelated to the
  resources.)
- GHC is unchanged: `cabal build all` (`-Werror`) and `make test` are
  green. `YCHR.ResourcesTest` still compares the modules the run-time
  loader parses with the ones the Template Haskell embedder baked in, and
  `YCHR.GenerateTest` covers the emitter (`renderCode`, `toCode`, the
  hoisting pass, and a full emission of both modules from the embedded
  resources). `mhs -fno-code -isrc YCHR.Internal.StdLib` still prints "No
  code generated".
- The executable's TH modules are GHC-only: their `template-haskell`
  dependency sits under `if impl(ghc)`, so nothing in the mhs dependency
  graph pulls TH in. The generator is likewise GHC-only
  (`if impl(mhs) buildable: False`), and the library gains no dependency:
  the emitter lives in `embed/`, not `src/`.
- Measured effect, and the reason the fixed cost is only half gone, are in
  `MICROHS_PERFORMANCE.md`, option B.


## 6. `Data.List.mapAccumL` and friends are list-only, not `Foldable`

> **Re-verified.** Still open upstream; the workaround is now applied to
> `src/`. It is a single site, and the round trip is free: `NonEmpty a`
> is `a :| [a]`, and `NE.toList` / `NE.fromList` are lazy O(1) views.
> `YCHR.Internal.Desugar`, the module that held the site, is checked
> directly rather than on a scratch copy; see "Local workaround
> (applied)".

Found while working past gaps 1–5; not previously recorded.

GHC's `Data.List.mapAccumL` is `Traversable`-polymorphic:

```haskell
mapAccumL :: Traversable t => (a -> b -> (a, c)) -> a -> t b -> (a, t c)
```

MicroHs's is monomorphic in lists
(`MicroHs/lib/Data/List.hs:648`):

```haskell
mapAccumL :: (acc -> x -> (acc, y)) -> acc -> [x] -> (acc, [y])
```

`Data.List.NonEmpty` *does* define a `Traversable` instance
(`lib/Data/List/NonEmpty.hs:161`) and exports `fromList` / `toList`, so
the type is usable — but anything routed through the list-only
`mapAccumL` fails, because `mhs` resolves it at `[]`:

```haskell
import qualified Data.List.NonEmpty as NE
import Data.List (mapAccumL)

f :: NE.NonEmpty Int -> (Int, NE.NonEmpty Int)
f bs = let (s, bs') = mapAccumL (\a x -> (a + x, x)) 0 bs
       in (s, NE.fromList bs')
-- Cannot satisfy constraint: NonEmpty ~ []
```

Reproduced at `src/YCHR/Internal/Desugar.hs:870-876`, where
`D.BodyOr` holds a `NE.NonEmpty` and the body is folded with
`mapAccumL`.

### Upstream fix sketch

Widen `mapAccumL` / `mapAccumR` to `Traversable t` (or host the
`NonEmpty` versions in `Data.List.NonEmpty`). The instance already
exists; only the signature and body of `Data.List`'s versions need to
change.

### Local workaround (applied)

No longer needed: the lambda lifter now runs in `State`, and
`liftBodyGoal`'s `D.BodyOr` arm uses `traverse` on the `NonEmpty`
directly, which MicroHs accepts. No `mapAccumL` is left in `src/`. The
rest of this section records the old workaround.

Applied to `src/YCHR/Internal/Desugar.hs`, `liftBodyGoal`'s `D.BodyOr`
arm — the only `mapAccumL` in the tree applied to a `NonEmpty`. Every
other call site already threads lists (`Desugar/Disjunction.hs:138`
converts with `NE.toList`); `mapAccumR` has the same list-only
signature upstream, but YCHR does not call it. The outer accumulation
converts to a list, and the result converts back:

```haskell
D.BodyOr branches ->
  let (st', branches') =
        mapAccumL
          (mapAccumL (liftBodyGoal modName scope))
          st
          (NE.toList branches)
   in (st', D.BodyOr (NE.fromList branches'))
```

The round trip is free: MicroHs's `NonEmpty a` is `a :| [a]`, with
`toList ~(a :| as) = a : as` and `fromList (a : as) = a :| as`
(`lib/Data/List/NonEmpty.hs:282-288`), so both directions are lazy O(1)
and no element is traversed an extra time. `NE.fromList` cannot fail
here: `disjuncts` always yields at least two branches
(`Desugar.hs:611-622`).

Verified:

- GHC: `make format` clean and `make test` green. Both forms typecheck
  under GHC, so the test suite cannot pin this gap; it only rules out a
  behaviour change.
- Isolated reproducer: a `Main` module using the `NonEmpty` form fails
  with `Cannot satisfy constraint: NonEmpty ~ []`; the same module with
  `NE.toList` compiles (`No code generated`).
- Direct check: `mhs -fno-code -isrc YCHR.Internal.Desugar` reports "No
  code generated" on the stock tree.
  The earlier "typechecks fully" claim for a scratch copy should have
  been scoped to this module: a whole-library check passes
  `Compile.Pipeline`, `Meta`, `VM` and `Backend.SchemeDriver` but stops
  on the `try` gap in `Runtime/Interpreter.hs` and the `elem` fixity gap
  in `Display.hs`, both of which predate this change and are unrelated to
  it (both have since been closed). Reverting only this change in a
  scratch copy brings the error back at the `D.BodyOr` arm
  (`Cannot satisfy constraint: NonEmpty ~ []`).

Invocation detail: the include path must be attached (`-i<dir>`, not
`-i <dir>`); the separate form is read as a module name and surfaces as
`undefined export: main`. With `-isrc`, a library module is checked
directly — `mhs -fno-code -isrc YCHR.Internal.Desugar` reports "No code
generated". The mhs-only overlay needs `-isrc/mhs` as well.

Cheap, but it means every `NonEmpty` crossing a `Traversable`-generic
helper needs an explicit conversion pair, and a mistake shows up as the
opaque `NonEmpty ~ []` rather than a missing-name error.


## 8. `optparse-applicative`'s `fullDesc` is missing from the MicroHs package

> **New; found while making the `ychr` executable build under MicroHs.**
> The workaround is applied to `app/Main.hs`; what remains open is the
> package the MicroHs package set ships.

`mcabal build` reaches the CLI once the earlier gaps are worked around, and then
stops on the first line of `app/Main.hs`'s `main`:

```
mhs: uncaught exception: error: "app/Main.hs": line 183, col 56:
  undefined value: fullDesc
```

`Options.Applicative` is in the MicroHs package set as
`optparse-applicative-0.19.0.0`, but the source behind it is a git
checkout of the branch that became 0.20 (`~/.mcabal/packages/…` is a
`.git` clone whose `CHANGELOG.md` already carries the 0.20.0.0 entry
"Remove `fullDesc` and `briefDesc` builder modifiers – they have not had
an effect since version 0.8", while its `.cabal` file still says
`version: 0.19.0.0`). The *released* 0.19.0.0 that GHC builds against
still exports both names, which is why the GHC build compiles unchanged.

### Upstream fix sketch

Point the package-set entry at the released 0.19.0.0 rather than a branch
checkout (or bump it once 0.20.0.0 is released). Both names are no-ops,
so either way the two sides agree.

### Local workaround (applied)

`app/Main.hs` writes the `ParserInfo` without the modifier:

```haskell
cmd <- execParser (info (commandParser <**> helper) (progDesc "CHR compiler"))
```

`fullDesc` is an effect-free `InfoMod`: the CHANGELOG above records that
it has had no effect since 0.8, and the next release removes it outright,
so dropping it is a no-op under GHC: the help output is unchanged.

Verified:

- Reproducer: `mhs -fno-code` on a module importing `fullDesc` from
  either `Options.Applicative` or `Options.Applicative.Builder` fails
  with `not exported: fullDesc`; the same module without it prints
  "No code generated". ([Hackage's 0.19.0.0
  `Options.Applicative.Builder`](https://hackage-content.haskell.org/package/optparse-applicative-0.19.0.0/docs/src/Options.Applicative.Builder.html)
  does list `fullDesc` and `briefDesc`, so this is the package set's
  checkout, not the release.)
- `mcabal build` gets past `app/Main.hs` once the modifier is gone.
- GHC: `cabal build all` (`-Werror`) and `make test` are green, so the
  dropped no-op changed no behaviour.


## 10. A local binding inferred as `HasField`-polymorphic is not generalized

> **Re-verified against `c98846b1`.** Still open. The reproducer used to
> show a *top-level* `origin`; that one compiles under MicroHs (also at
> `f65d3c65`). Only a local binding fails, which is the shape the
> `Resolve.hs` site has, so the reproducer below now uses `where`.

Under `OverloadedRecordDot`, a local helper that reads a field off its
argument is inferred with a `HasField "field" r a` constraint. GHC
generalizes the binding (it has arguments, so the monomorphism
restriction does not apply); MicroHs does not, so it monomorphizes the
helper at its first use and a second use at a different record type
fails to unify:

```haskell
{-# LANGUAGE DuplicateRecordFields, NoFieldSelectors, OverloadedRecordDot #-}
data A = A { name :: String }
data B = B { name :: String }

main :: IO ()
main = print (f (A "a") (B "b"))
  where
    origin m x = m ++ ":" ++ x.name
    f :: A -> B -> [String]
    f a b = [origin "m" a, origin "m" b]
-- mhs: type mismatch, expected: A, actual: B (at the second use)
-- GHC: compiles
```

### Upstream fix sketch

Generalize `where`/`let`-bound bindings over their inferred type-class
constraints, as top-level bindings already are.

### Local workaround

Pass the projected field value instead of the record, so the helper's
type is monomorphic. In `Resolve.checkBoundedDeclarations`:

```haskell
originForDecl m n = PExpr.Atom (m.name <> ":" <> n)
-- used as originForDecl m fd.name and originForDecl m cd.name
```


## 11. File-open errors carry no description

> **Re-verified against `c98846b1`.** The `openFile` half is still open.
> The `createDirectoryIfMissing` half is fixed upstream (`0e12b043`,
> #565): `ychr compile -d blocker/sub prog.chr`, with `blocker` a file,
> now prints `Error: cannot write blocker/sub: Not a directory` under
> both compilers.

MicroHs's `openFile`/`openBinaryFile` collapse every failure to
`NoSuchThing` with an empty description (`System/IO/Base.hs`:
`Nothing -> ioErr NoSuchThing "openFile" fn`, and `ioErr` always
passes `""` there — unlike `ioErrH`, which does set one for
handle-level ops like `hGetChar`). So a permission error reads like a
missing file:

```
$ chmod 000 noperm.chr
$ dist-mcabal/bin/mhs/ychr check noperm.chr
Cannot read file 'noperm.chr': Does not exist
# GHC: Cannot read file 'noperm.chr': Permission denied
```

A directory given as input reads back empty instead of failing, at
the C runtime's `getb`/`readb` primitives, below any Haskell-level
API choice.

### Upstream fix sketch

Have `openFile`/`openBinaryFile` build the right `IOErrorType` from
`errno`, with the OS's `strerror` text in `ioe_description`, the way
GHC's `errnoToIOError` does (MicroHs has it in `Foreign/C/Error.hs`).

### Local workaround

None. Only the reason text differs; YCHR-50005 still fires with exit 1.
Reason-text asserts are GHC-only.

Verified:

- The reproducer above, paired with the GHC build's output on the same
  input.


## Out of scope (not gaps, just noted)

- `Data.List.foldl'` is present in MicroHs but isn't re-exported from
  `Prelude`. Modules that use it currently rely on GHC ≥ 9.6
  re-exporting it. Adding an explicit `import Data.List (foldl')` to
  each affected module (`Compile.hs`, `Compile/Occurrences.hs`,
  `Desugar.hs`, `Runtime/Interpreter.hs`) works on both compilers and
  is a one-line per-file change. Not a MicroHs bug — but flagged here
  so it isn't mistaken for one when sweeping the diff.
