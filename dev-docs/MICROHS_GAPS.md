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
installed `mhs` 0.16.6.0. Six gaps remain open; one has closed and been
removed from this document.

| # | Gap | State |
|---|---|---|
| 1 | `OverloadedRecordDot` rejects an already-bound field name | open — and broader than first recorded (five field names, ~68 sites) |
| 2 | `NoFieldSelectors` silently ignored | open |
| 3 | Record update on a record-dot expression doesn't parse | open — four sites |
| 4 | Missing `Data.Text` functions | open — contents changed: `breakOn`, `concatMap`, `breakOnEnd`, `last` |
| 5 | No `TemplateHaskell` support | open — no workaround |
| 6 | `mapAccumL` is list-only | open |

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
`src/YCHR/Internal/Pretty.hs:121` (`r.head.node`) with

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
  `src/YCHR/Internal/TypeCheck/Encode.hs`, the module defines its own
  `guard :: D.Guard -> Term` (`:285`), and `r.guard` (`:228`) fails with
  `Rule ~ (Term -> [Guard])`. There is nothing to `hide` — the name is in
  scope because the module defined it.
- **Both the field and the function are needed.** In
  `src/YCHR/Internal/Runtime/Monad.hs`, `TrailState` has a `length` field
  and the module also calls the list function; hiding the import is not an
  option. Qualifying the call (`List.length`) works, but it is a per-site
  rewrite.

#### Chained selectors report a misleading downstream error

When a chain such as `r.head.removed` is involved, the first selector
resolving to `Prelude.head` pushes the failure onto the *second* field,
which then surfaces as a `HasField` error rather than the `~` error:

```
Cannot satisfy constraint: HasField "removed" (AnnP Head) [_a315]
```

This is the same gap, not a separate one. It is what
`src/YCHR/Internal/Compile/Occurrences.hs:106-107` and
`src/YCHR/Internal/Compile.hs:483` report once `head` has been hidden; the
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

> **Re-verified.** Still open. The doc recorded one site; there are four.

The expression form `e.fld { f = ... }` (record update applied to the
result of a record-dot selector chain) fails with a parse error:

```
src/YCHR/Internal/Desugar.hs:642:48:
  found:    {
  expected: . LQIdent ( UQIdent [ literal _primitive @ ...
```

Trigger:

```haskell
func { D.equations = func.equations { node = eqs' } }
--                   ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
```

A `let` binding to name `func.equations` first works around it. GHC
accepts the inline form.

The same shape recurs three more times; the recorded site is the first
one `mhs` reaches, not the only one:

| site | expression |
|---|---|
| `src/YCHR/Internal/Desugar.hs:959` | `func { D.equations = func.equations { node = eqs' } }` |
| `src/YCHR/Internal/Desugar.hs:1025-1026` | `rule { D.guard = rule.guard { node = guards' }, ... }` |
| `src/YCHR/Internal/Desugar/Disjunction.hs:107` | `rule { D.body = rule.body { node = goals } }` |
| `src/YCHR/Internal/Desugar/Disjunction.hs:154-162` | `ctx.headAnn { node = ... }`, `ctx.bodyAnn { node = ... }` |

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

### Local workaround

Hoist the selector chain to a local `let` binding, then update that:

```haskell
let eqsAnn = func.equations
    newEqs = eqsAnn { node = eqs' }
in func { D.equations = newEqs }
```

Cheap and rare. Comfortable to keep even if MicroHs never grows the
parser fix.


## 4. Missing `Data.Text` functions

> **Re-verified, contents changed since this entry was written.**
> MicroHs's `Data.Text` has since gained `all`, `any` and `strip`, and
> YCHR has dropped the `unpack`-threading workarounds and now calls them
> directly. The remaining gaps are a *different* set: `breakOn`,
> `concatMap`, `breakOnEnd` and `last`.

`MicroHs/lib/Data/Text.hs` is still missing several functions exported
by the `text` package on Hackage. YCHR uses each of these in the listed
locations (line numbers current as of this revision):

| Missing  | YCHR call sites |
|----------|------------------|
| `breakOn`    | `src/YCHR/Internal/Runtime/Trace.hs:231`, `src/YCHR/Internal/Resolve.hs:1405`, `src/YCHR/Internal/Meta.hs:90` |
| `concatMap`  | `src/YCHR/Internal/Compile/Names.hs:110`, `src/YCHR/Internal/Compile/Names.hs:135`, `src/YCHR/Internal/SExpr.hs:69` |
| `breakOnEnd` | `test/YCHR/TypeSoundness/Observe.hs:178,181` |
| `last`       | `src/YCHR/Internal/Parser.hs:256` |

The first failure a build hits is `Text.last`
(`Parser.hs:256`, `Text.last trimmed`), reported as
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
- `T.breakOnEnd sep t`→ as `breakOn`, searching from the right

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


## 5. No `TemplateHaskell` support

> **Re-verified.** Still open, and it is the one gap with no workaround.
>
> Correcting a detail in the original entry: a `mcabal build` does not
> reach `StdLib.hs`. It aborts earlier, during dependency resolution:

```
mcabal: uncaught exception: error: "../MicroCabal/src/MicroCabal/Main.hs",389:7:
  dependency not installed: template-haskell
```

> `template-haskell` is absent from the installed package set, and no
> `-f-examples` / `flags: -examples` setting avoids it. Independently,
> TH syntax is a hard parse error, not merely an ignored pragma:
> `$( ... )` yields `found: $` / `expected: - LQIdent ...`.

MicroHs is a combinator-based compiler with no staged compilation.
The `TemplateHaskell` extension is not recognised; modules using it
cannot build under `mcabal`.

YCHR uses TH to embed `libraries/*.chr` and the type checker's
`typechecker/*.chr` into the binary at compile time
(`YCHR.Internal.StdLib.TH`, `YCHR.Internal.TypeCheck.TH`). This makes the GHC-built
binary self-contained and cwd-independent. Without TH, mhs has no
equivalent compile-time embedding path.

### Root cause

`MicroHs/src/MicroHs/Lex.hs` and `Parse.hs` have no quotation /
splice grammar; the compiler has no staged-evaluation phase.
Implementing TH would require a second compilation pass over
splice-producing modules and a runtime evaluator for `Q` actions —
effectively another compiler. Not realistic as an upstream fix; TH
is a non-goal for MicroHs by design.

### Upstream fix sketch

None viable.

### Local workaround

None. `mcabal build` fails during dependency resolution, before it
reaches `src/YCHR/Internal/StdLib.hs` or
`src/YCHR/Internal/TypeCheck/Compiled.hs` (those would fail next, on the
TH pragmas). Users must build with `cabal`/GHC.
This was a conscious trade-off taken when reverting from the runtime
loader (the change `2142c05` was originally motivated by) back to TH
embedding: the runtime loader had a known cwd-relative bug, and the
GHC-only fix is the cleanest available. If future work restores mhs
compat, the loaders will need a per-backend split (`src/ghc/` +
`src/mhs/`, mirroring the existing `YCHR.Internal.LineInput` pattern) — but
that machinery is intentionally not added preemptively.


## 6. `Data.List.mapAccumL` and friends are list-only, not `Foldable`

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

Reproduced at `src/YCHR/Internal/Desugar.hs:865-870`, where
`D.BodyOr` holds a `NE.NonEmpty` and the body is folded with
`mapAccumL`.

### Upstream fix sketch

Widen `mapAccumL` / `mapAccumR` to `Traversable t` (or host the
`NonEmpty` versions in `Data.List.NonEmpty`). The instance already
exists; only the signature and body of `Data.List`'s versions need to
change.

### Local workaround

Thread through the list representation, which is what the rest of YCHR
already does (`NE.toList` / `NE.fromList`):

```haskell
let (st', branches') =
      mapAccumL
        (mapAccumL (liftBodyGoal modName scope))
        st
        (NE.toList branches)
 in (st', D.BodyOr (NE.fromList branches'))
```

Cheap, but it means every `NonEmpty` crossing a `Traversable`-generic
helper needs an explicit conversion pair, and a mistake shows up as the
opaque `NonEmpty ~ []` rather than a missing-name error.


## Out of scope (not gaps, just noted)

- `Data.List.foldl'` is present in MicroHs but isn't re-exported from
  `Prelude`. Modules that use it currently rely on GHC ≥ 9.6
  re-exporting it. Adding an explicit `import Data.List (foldl')` to
  each affected module (`Compile.hs`, `Compile/Occurrences.hs`,
  `Desugar.hs`, `Runtime/Interpreter.hs`) works on both compilers and
  is a one-line per-file change. Not a MicroHs bug — but flagged here
  so it isn't mistaken for one when sweeping the diff.
