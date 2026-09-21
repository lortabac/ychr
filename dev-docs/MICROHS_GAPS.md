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

Re-verified against MicroHs `3322c60a` (the checkout's HEAD) and the
installed `mhs` 0.16.6.0. Eight gaps are recorded; one has closed and
been removed from this document. The local workarounds for gaps 1, 3, 4,
6 and 7 are applied (gaps 4 and 7 also touch the importers, tests
included), and gap 5's library-side workaround is applied too: no
Template Haskell remains in `library ychr` and no unconditional
`template-haskell` dependency remains in `ychr.cabal` (see gap 5). With
gaps 3 and 7 out of the way, `mcabal build` gets past dependency
resolution and compiles the library past `Runtime/Interpreter.hs:872`,
stopping on gap 8 in `Display.hs:888`; gaps 7 and 8 were found on the way
to that point and are recorded below.

| # | Gap | State |
|---|---|---|
| 1 | `OverloadedRecordDot` rejects an already-bound field name | open — workaround applied to `src/` (see below) |
| 2 | `NoFieldSelectors` silently ignored | open |
| 3 | Record update on a record-dot expression doesn't parse | open — workaround applied to `src/` (see below) |
| 4 | Missing `Data.Text` functions | open — workaround applied (`Data.Text.Shim`) |
| 5 | No `TemplateHaskell` support | open upstream — TH kept out of `library ychr`; the mhs-side resources provider is missing (see below) |
| 6 | `mapAccumL` is list-only | open — workaround applied to `src/` (see below) |
| 7 | `Control.Exception.try` orders its type variables differently from GHC | open — workaround applied (`Control.Exception.Shim`) |
| 8 | `Data.List` functions lack their fixity declarations | open — no workaround |

`Data.Either.partitionEithers` (formerly gap 5) is now exported by
MicroHs (`lib/Data/Either.hs:51`) and used directly by
`src/YCHR/Internal/Parser.hs`; that entry is gone.

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
| `import Prelude hiding (head)` | `Compile.hs`, `Compile/Occurrences.hs`, `Compile/Passive.hs`, `Desugar.hs`, `Desugar/Disjunction.hs`, `Pretty.hs`, `Resolve.hs`, `TypeCheck/Encode.hs` |
| local `guard` renamed to `guardTerm` | `TypeCheck/Encode.hs` |
| `length` qualified as `List.length` | `Runtime/Monad.hs:176` |

Hiding the list function is safe in all eight modules: none of them calls
it. `Rename.hs` and `Runtime/Trail.hs` are left alone (see "Breadth"
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
gap-3 sites (`func.equations {node = …}`, `ctx.bodyAnn {node = …}`),
not on this gap; those now compile as well, since gap 3's workaround
landed. `Runtime/Monad.hs` sits behind them through
`Compile.Pipeline`, so its call was checked with the equivalent
`TrailState` reproducer instead (`ambiguous value: length […]` without
the qualification, accepted with it). There is still no end-to-end
check: the library stops on gap 8 before the CLI is reached (gap 7 was
worked around after this sweep — see gap 7).
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


## 3. Record update on a record-dot expression doesn't parse

> **Re-verified.** Still open upstream; the workaround is now applied to
> `src/`. The doc recorded one site; there are four, all in the
> desugaring passes. With them hoisted, `mhs -fno-code -isrc
> YCHR.Internal.Desugar` and `…YCHR.Internal.Desugar.Disjunction` report
> `No code generated`.

The expression form `e.fld { f = ... }` (record update applied to the
result of a record-dot selector chain) fails with a parse error — the
line numbers are from before the workaround below:

```
mhs: uncaught exception: error: "src/YCHR/Internal/Desugar.hs": line 965, col 48:
  found:    {
  expected: . LQIdent ( UQIdent [ QualString literal _primitive @ (# \ case let if QualDo do mdo QSymOper ` :: ∷ , }
```

Trigger:

```haskell
func { D.equations = func.equations { node = eqs' } }
--                   ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
```

A `let` binding to name `func.equations` first works around it. GHC
accepts the inline form.

The same shape recurs three more times; the recorded site is the first
one `mhs` reaches, not the only one. Line numbers and updates below are
the current (post-workaround) code; each `…Ann` binding holds the
selector that used to be written inline:

| site | update |
|---|---|
| `src/YCHR/Internal/Desugar.hs:966` | `func {D.equations = eqsAnn {node = eqs'}}` |
| `src/YCHR/Internal/Desugar.hs:1034-1035` | `rule {D.guard = guardAnn {node = guards'}, D.body = bodyAnn {node = body'}}` |
| `src/YCHR/Internal/Desugar/Disjunction.hs:109` | `rule {D.body = bodyAnn {node = goals}}` |
| `src/YCHR/Internal/Desugar/Disjunction.hs:157,164-165` | `headAnn {node = ...}`, `bodyAnn {node = ...}` |

Note the trigger is not exactly "a selector chain": `ctx.headAnn { ... }`
is a single field of a local record and still fails, while a direct
record update like `rule { D.body = ... }` is fine. What fails is an
update applied to an expression reached through a `.` selector,
whatever the selector's depth.

### Upstream fix sketch

`MicroHs/src/MicroHs/Parse.hs` `pAExpr` runs `many pUpdate` then
`many pSelect`, so updates after selects aren't recognised. Allowing
`pUpdate` / `pSelect` to interleave (`many (Right <$> pUpdate <|>
Left <$> pSelect)`) would match GHC's behaviour.

### Local workaround (applied)

Applied to `src/` as a hoist of the selector into a local binding:

| site | hoist |
|---|---|
| `Desugar.hs` `liftFunction` | `eqsAnn = func.equations` |
| `Desugar.hs` `liftRule` | `guardAnn = rule.guard`, `bodyAnn = rule.body` |
| `Disjunction.hs` `lowerRule` | `bodyAnn = rule.body` |
| `Disjunction.hs` `liftBranch` | `headAnn = ctx.headAnn`, `bodyAnn = ctx.bodyAnn` |

```haskell
let eqsAnn = func.equations
    newEqs = eqsAnn { node = eqs' }
in func { D.equations = newEqs }
```

Parenthesizing the selector parses too — `(func.equations) { node = eqs' }`
is accepted by `mhs`, which puts the update inside `many pUpdate` after a
`pAExpr'` atom — but the hoist is preferred: the parentheses read as
redundant and would invite deletion, while the binding is
self-documenting. It also removes a repeated selector at every site. A
pattern sweep over `src/`, `app/`, `test/`, `bench/` and
`examples/` finds no other update-on-selector site; the modules behind
gap 7 were checked with gap 7's sites bypassed (that sweep predates the
gap-7 workaround).

Cheap and rare. Comfortable to keep even if MicroHs never grows the
parser fix.


## 4. Missing `Data.Text` functions

> **Re-verified, contents changed since this entry was written.**
> MicroHs's `Data.Text` has since gained `all`, `any` and `strip`, and
> YCHR has dropped the `unpack`-threading workarounds and now calls them
> directly. The remaining gaps are a *different* set: `breakOn`,
> `concatMap`, `breakOnEnd` and `last`.
>
> The shim workaround below is applied to `src/` and to one test module;
> what remains open is the MicroHs side.

`MicroHs/lib/Data/Text.hs` is still missing several functions exported
by the `text` package on Hackage. YCHR uses each of these in the listed
locations (line numbers current as of this revision):

| Missing  | YCHR call sites |
|----------|------------------|
| `breakOn`    | `src/YCHR/Internal/Runtime/Trace.hs:233`, `src/YCHR/Internal/Resolve.hs:1409`, `src/YCHR/Internal/Meta.hs:92` |
| `concatMap`  | `src/YCHR/Internal/Compile/Names.hs:112`, `src/YCHR/Internal/Compile/Names.hs:137`, `src/YCHR/Internal/SExpr.hs:71` |
| `breakOnEnd` | `test/YCHR/TypeSoundness/Observe.hs:180,183` |
| `last`       | `src/YCHR/Internal/Parser.hs:258` |

The first failure a build hits is `Text.last`
(`Parser.hs:258`, `Text.last trimmed`), reported as
`undefined value: Text.last`. `last` and `breakOnEnd` were not in the
original list; `all`, `any` and `strip` no longer belong in it.

MicroHs's `Data.Text` exports `head` but not its dual, and has
`breakOn`-adjacent machinery only through `splitOn`.

### Upstream fix sketch

Add these to the export list of `MicroHs/lib/Data/Text.hs` (and
implement them via `unpack` + `Data.List` if a streaming
implementation isn't worth it for `Data.Text`'s strict
`ByteString`-backed representation).

### Local workaround

Each call site rewrites to a `Data.List` equivalent threaded through
`T.unpack`, plus a re-pack on the way out where applicable:

- `T.concatMap f t`   → `T.concat (map f (T.unpack t))`
- `T.last t`          → `last (T.unpack t)`
- `T.breakOn sep t`   → `T.splitOn`, or a local `breakOnT` helper
- `T.breakOnEnd sep t`→ `breakOn (reverse sep) (reverse t)`, reversing
  both components back — reversing only the haystack is wrong, see below

Two points learned the hard way while applying these:

- `trailing`-style helpers must be **eta-expanded**. Writing
  `encodeText = T.concat (map encodeChar . T.unpack)` fails under `mhs`
  with a spurious `Text ~ [Text]`; `encodeText t = T.concat (map
  encodeChar (T.unpack t))` is accepted.
- The `concatMap` rewrite's result type depends on what `f` returns.
  `T.concatMap f` with `f :: Char -> Text` is `\t -> T.concat (map f
  (T.unpack t))`, not `T.singleton . f`.

These all evaluate equivalently on the input ranges YCHR actually
hits, and the perf hit is negligible at compiler-frontend scale.

### Local workaround (applied)

Applied as one shim module rather than a per-call-site rewrite:
`src/Data/Text/Shim.hs` (module `Data.Text.Shim`) offers the whole
`Data.Text` surface plus the four missing functions, implemented over
`Data.List`. Each importer treats it as a drop-in for `Data.Text`:

| edit | sites |
|---|---|
| `import Data.Text.Shim qualified as …` | `Compile/Names.hs`, `SExpr.hs`, `Parser.hs`, `Resolve.hs`, `Meta.hs`, `Runtime/Trace.hs`, `test/YCHR/TypeSoundness/Observe.hs` |

The shim deliberately replaces the native implementations under GHC too:
one implementation then serves both compilers, and the GHC test suite
(`YCHR.TextShimTest`) pins the shim to `Data.Text` over an exhaustive
small corpus, so it exercises the code `mhs` will run. Points learned
while writing it:

- `breakOnEnd` reverses the **pattern as well as the haystack**. A first
  cut that reversed only the haystack agreed with `Data.Text` on every
  single-character pattern and failed on `breakOnEnd "a:b" "a:b:c"`.
- The not-found results are asymmetric, as in `Data.Text`: `breakOn`
  gives `(src, "")`, `breakOnEnd` gives `("", src)`.
- The partial cases keep `Data.Text`'s behaviour, including *when* they
  throw: `breakOn` rejects an empty pattern at the tuple, while
  `breakOnEnd` rejects it only once a component is forced, hence the
  lazy pattern binding there. `last` rejects an empty text.
- Eta-expansion still applies: `reverseText` and `concatMap` are written
  with explicit arguments.
- Under GHC the module needs `import Prelude hiding (concatMap, last)`,
  or its export-list entries are ambiguous with `Prelude`'s. MicroHs
  silently ignores hidden names it does not export, so the same source
  works on both compilers.

Verified with `mhs -fno-code -isrc`: `Data.Text.Shim` itself plus
`SExpr.hs`, `Compile/Names.hs`, `Parser.hs`, `Resolve.hs` and
`Runtime/Trace.hs` compile (`No code generated`); before the shim, each
stopped on `undefined value: T.concatMap` / `Text.last` / `T.breakOn`.
`Meta.hs` and `Compile.Pipeline` now get past gaps 3 and 4 as well.
There is still no end-to-end check: the library stops on gap 8 in
`Display.hs` (gap 7 has since been worked around — see gap 7), and gap
5's resources provider is missing for the CLI.

Deleting `src/Data/Text/Shim.hs`, the importers' `Data.Text.Shim` import
lines, `test/YCHR/TextShimTest.hs` and its wiring (the shim's
`exposed-modules` entry and the test's `other-modules` entry in
`ychr.cabal`, plus the import and group entry in `test/Main.hs`)
restores plain `Data.Text` imports; that is the intended cleanup once
MicroHs exports the four functions.


## 5. No `TemplateHaskell` support

> **Re-verified.** Still open upstream — mhs has no staged compilation
> and never will (see "Root cause"). The YCHR side has changed since the
> original entry: the `ychr` *library* no longer uses TH at all (its
> workaround is applied, below). TH is confined to the shared `embed/`
> source directory, which only the components that want a self-contained
> GHC binary compile: the `ychr` executable, the test suite, the
> benchmark and the `stlc` example. What mhs still lacks is a provider
> for the two resources those components embed.

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

What remains for mhs is the *provider* for those two values: with no TH,
a component must read `libraries/` and `typechecker/` from disk and feed
`parseStdLib` / `compileTypeCheckerModules`, and the executable must
depend on that provider instead of on `embed/`. Until then mhs can build
the library but not the CLI.

Verified on this revision:

- `mcabal build` no longer aborts during dependency resolution. It
  resolves the package and starts on `library ychr`, stopping on gap 7 in
  `Runtime/Interpreter.hs:870` — with gap 3 applied, the first failure
  has moved on again, and it is a known, unrelated gap rather than
  `dependency not installed: template-haskell`. (Gap 7 has since been
  worked around; the library now stops on gap 8.)
- `mhs -fno-code -isrc YCHR.Internal.StdLib` prints "No code generated":
  the new `StdLib` newtype and `parseStdLib` are mhs-clean.
- The four embedding components are GHC-only: their `template-haskell`
  dependency sits under `if impl(ghc)`, so nothing in the mhs dependency
  graph pulls TH in. The library's own module list no longer mentions
  the former `YCHR.Internal.StdLib.TH` / `YCHR.Internal.TypeCheck.TH`.


## 6. `Data.List.mapAccumL` and friends are list-only, not `Foldable`

> **Re-verified.** Still open upstream; the workaround is now applied to
> `src/`. It is a single site, and the round trip is free: `NonEmpty a`
> is `a :| [a]`, and `NE.toList` / `NE.fromList` are lazy O(1) views.
> The tree now carries gap 3's hoists, so the module that holds the site
> — `YCHR.Internal.Desugar` — is checked directly rather than on a
> scratch copy; see "Local workaround (applied)".

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
  code generated" on the stock tree, since gap 3's hoists are now in it.
  The earlier "typechecks fully" claim for a scratch copy should have
  been scoped to this module: a whole-library check passes
  `Compile.Pipeline`, `Meta`, `VM` and `Backend.SchemeDriver` but stops
  on gaps 7 and 8 in `Runtime/Interpreter.hs` and `Display.hs`, both of
  which predate this change and are unrelated to it. Reverting only this
  change in a scratch copy brings the error back at the `D.BodyOr` arm
  (`Cannot satisfy constraint: NonEmpty ~ []`).

Invocation detail: the include path must be attached (`-i<dir>`, not
`-i <dir>`); the separate form is read as a module name and surfaces as
`undefined export: main`. With `-isrc`, a library module is checked
directly — `mhs -fno-code -isrc YCHR.Internal.Desugar` reports "No code
generated" (before gap 3's workaround it reported the parse error at
`Desugar.hs:965`). The mhs-only overlay needs `-isrc/mhs` as well.

Cheap, but it means every `NonEmpty` crossing a `Traversable`-generic
helper needs an explicit conversion pair, and a mistake shows up as the
opaque `NonEmpty ~ []` rather than a missing-name error.


## 7. `Control.Exception.try` orders its type variables differently from GHC

> **Re-verified.** Still open upstream; the workaround is now applied to
> `src/`, `app/` and `test/`. Found while working past gap 3; not
> previously recorded. It was the first failure a build reached:
> `mcabal build` stopped on it in `Runtime/Interpreter.hs:870`. With the
> shim below, the library compiles past it and the next failure is gap 8.

MicroHs declares (`MicroHs/lib/Control/Exception.hs:106`):

```haskell
try :: forall a e . Exception e => IO a -> IO (Either e a)
```

GHC 9.12's `base` binds the exception type first, so `try @SomeException`
means `e` there and `a` here. A visible type application therefore
selects the wrong variable:

```haskell
-- mhs: Cannot satisfy constraint: SomeException ~ ()
-- GHC 9.12: accepts (Right ())
try @SomeException (pure ())
```

No positional form is portable: `try @_ @SomeException` typechecks on
`mhs` and fails on GHC 9.12 with `SomeException ~ ()`.

Sites in the library (line numbers after the shim imports below):

| site | call |
|---|---|
| `src/YCHR/Internal/Runtime/Interpreter.hs:872` | `try @SomeException` |
| `src/YCHR/Run.hs:639` | `try @SomeException` |
| `src/YCHR/Internal/Repl.hs:129` | `try @IOException` |
| `src/YCHR/Internal/Repl.hs:219,227,247,255,359,375` | `try @SomeException` |
| `src/mhs/YCHR/Internal/LineInput.hs:39` | `try @IOException` |

The last one is the mhs-only line-input overlay, which had never compiled
under `mhs`; that is why the pattern went unnoticed there. The same shape
appears in `app/Main.hs:198,205,260,265` and in the tests
(`Runtime/StoreTest.hs`, `Runtime/InterpreterTest.hs`,
`TextShimTest.hs`, `ConvertTest.hs`, `TypeSoundnessTest.hs`,
`GoldenTest.hs`, `RunTest.hs`). All of them are converted: the shim makes
that an import swap, so leaving the out-of-reach files behind would only
keep the trap alive for a later sweep.

### Upstream fix sketch

Order `try`'s type variables the way GHC's `base` does (drop the
explicit `forall a e`, or write it `forall e a`). The point of the audit
below is how far the reordering has to reach; measured against `mhs`
0.16.6.0 it stops at `try`:

- `catch` (declared `forall e a` in `Control.Exception.Internal`) and
  the inferred `handle` / `tryJust` accept `@SomeException` as the
  exception variable on both compilers;
- `bracket`, `finally` and `onException` diverge for a second reason —
  MicroHs's *inferred* order for them is not GHC's, so GHC's
  `bracket @Int @Bool @Char` and `finally @Int @Char` are rejected by
  `mhs` — but YCHR never type-applies them;
- `throwIO` is declared `forall a e` in MicroHs against GHC's
  `forall e a`, and is never type-applied in YCHR either.

Nothing outside `try` needs work today; a site that starts type-applying
one of the others needs a wrapper with an explicit GHC-ordered `forall`
added to the shim.

### Local workaround (applied)

`src/Control/Exception/Shim.hs` re-exports `Control.Exception` with `try`
replaced by a version whose signature spells out GHC's order:

```haskell
try :: forall e a. Exception e => IO a -> IO (Either e a)
try = E.try
```

Both compilers honour the *declared* order for a visible type
application, so `try @SomeException` selects `e` under `mhs` as it does
under GHC. This is the shape `Data.Text.Shim` already uses for gap 4: a
module that mirrors the upstream surface, swapped in at the import line,
so the 29 call sites read exactly as before. The helper form sketched
earlier (`trySomeException = try`) would have meant editing all 29 and
adding a third twin for the tests' `RuntimeErrorThrown`; the shim is one
module plus an import swap per importer.

| edit | sites |
|---|---|
| `import Control.Exception` → `.Shim` | `Run.hs`, `Runtime/Interpreter.hs`, `Runtime/Search.hs`, `Internal/Repl.hs`, `src/mhs/YCHR/Internal/LineInput.hs`, `app/Main.hs`, and the test modules `Runtime/StoreTest.hs`, `Runtime/InterpreterTest.hs`, `TextShimTest.hs`, `ConvertTest.hs`, `TypeSoundnessTest.hs`, `GoldenTest.hs`, `RunTest.hs` — 13 files |
| `exposed-modules: Control.Exception.Shim` | `ychr.cabal`, in the provisional-shim stanza |

`Runtime/Search.hs` has no type application (it uses `try` bare); it is
swapped so that every `try` in the tree comes from the shim. The
`Text.Parsec.try` imports (`PExpr.hs`, `SExpr.hs`) are unrelated and
untouched.

Verified on this revision:

- GHC: `make format` clean, `cabal build all` (`-Werror`) and `make test`
  green. The call sites pin the shim against the obvious mistake: a
  `forall a e` signature would make `try @SomeException (prepareGoal …)`
  fail to compile, because the action is not `IO SomeException`. (Nothing
  on GHC catches the /absence/ of the explicit `forall` — inferred, GHC
  already picks `e` first; that half of the shim is MicroHs-only.)
- Reproducers: before, `mhs -fno-code -isrc -isrc/mhs
  YCHR.Internal.Runtime.Interpreter` failed at `Interpreter.hs:870` with
  `Cannot satisfy constraint: SomeException ~ Value`, and the same
  invocation on `YCHR.Internal.LineInput` failed at `LineInput.hs:37`
  with `Cannot satisfy constraint: Exception _a77`. After, the overlay
  reports "No code generated" — its first successful `mhs` check — and
  the interpreter module no longer fails on gap 7.
- Scratch reproducer: a module declaring `try :: forall e a. Exception e
  => IO a -> IO (Either e a)` compiles and runs under both `mhs` and GHC
  with `try @SomeException` and `try @IOException`, and both reject
  `try @Int` with `Cannot satisfy constraint: Exception Int` — i.e. the
  type application binds the exception variable on both.
- `mcabal build`: gets past `Runtime/Interpreter.hs:872` and stops on
  gap 8 in `Display.hs:888` (`Cannot satisfy constraint: Bool ~ [Text]`),
  as recorded in the Status section.

Delete the module (and revert the 13 imports) once MicroHs orders `try`
the way `base` does.


## 8. `Data.List` functions lack their fixity declarations

> **Re-verified.** Open. Found while working past gap 3; not previously
> recorded. It is the next failure after gap 7: with gap 7's workaround
> in place the library failure lands here, at `Display.hs:888`.

`MicroHs/lib/Data/List.hs` declares fixities only for `\\`, `!!` and
`!?` (lines 473, 486, 497). Everything else that `base` gives a fixity
declaration falls back to the Haskell default `infixl 9`, so a backticked
use binds tighter than it does under GHC:

```haskell
"prelude" `elem` conMods ++ funMods
-- mhs parses ("prelude" `elem` conMods) ++ funMods:
--   Cannot satisfy constraint: Bool ~ [Text]
-- GHC parses "prelude" `elem` (conMods ++ funMods)
```

The one site in the library is `src/YCHR/Internal/Display.hs:888`.
`elem` is not special here: `notElem`, `union`, `intersect`,
`isPrefixOf` and the rest are in the same position.

### Upstream fix sketch

Add the standard fixity declarations to `MicroHs/lib/Data/List.hs`
(`infix 4 \`elem\``, `infix 4 \`notElem\``, `infixl 5 \`union\``, …),
and check the `Prelude` re-exports.

### Local workaround

None applied. Parenthesize the operand whose precedence is being relied
on: `"prelude" \`elem\` (conMods ++ funMods)`. Verified with
`mhs -fno-code`; a whole-library check with the workarounds for gaps 3
and 7 in place and this one applied finds no second site, but `app/`,
`test/` and `bench/` are outside `mhs`'s reach, so the sweep is not
exhaustive.


## Out of scope (not gaps, just noted)

- `Data.List.foldl'` is present in MicroHs but isn't re-exported from
  `Prelude`. Modules that use it currently rely on GHC ≥ 9.6
  re-exporting it. Adding an explicit `import Data.List (foldl')` to
  each affected module (`Compile.hs`, `Compile/Occurrences.hs`,
  `Desugar.hs`, `Runtime/Interpreter.hs`) works on both compilers and
  is a one-line per-file change. Not a MicroHs bug — but flagged here
  so it isn't mistaken for one when sweeping the diff.
