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


## 1. `OverloadedRecordDot` rejects a field name that is already bound

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

YCHR's `Parsed`, `Resolved` and `Desugared` all have a `head` field,
and several `Compile/*` modules import `YCHR.Internal.Desugared` /
`YCHR.Internal.Parsed` qualified. A `.head` use site in a module with
no open import of a `head`-defining module fails as above; a module
that open-imports one does not. Whether the full build trips has not
been confirmed end-to-end: reaching the affected modules needs `parsec`
installed under `mcabal`, and gap 6 blocks the build independently.

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

### History

This entry previously diagnosed a cross-module collision of the
generated selectors and prescribed qualifying `mkGetName`
(`Deriving.hs:171`) with the module name. MicroHs already does that
later, via `extValETop` (`TypeCheck.hs:872`) — the emitted name is
`R.get$.Rule.head` — so that diagnosis no longer reproduces (nor does
the `HasField "kept" _a3940` error); only the `Rule ~ (_a -> _b)` error
above survives, from `isLabel`.


## 2. `NoFieldSelectors` is silently ignored

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

`MicroHs/lib/Data/Text.hs` is missing several functions exported by
the `text` package on Hackage. YCHR uses each of these in the listed
locations:

| Missing  | YCHR call sites |
|----------|------------------|
| `all`       | `src/YCHR/Internal/PExpr.hs:275`, `src/YCHR/Internal/PExpr.hs:843`, `src/YCHR/Internal/Backend/Scheme.hs:618`, `src/YCHR/Internal/SExpr.hs:111,113` |
| `any`       | `src/YCHR/Internal/SExpr.hs:105` |
| `concatMap` | `src/YCHR/Internal/Compile/Names.hs:75`, `src/YCHR/Internal/SExpr.hs:69` |
| `strip`     | `src/YCHR/Internal/Repl.hs:213` |
| `breakOn`   | `src/YCHR/Internal/Meta.hs:54` |

### Upstream fix sketch

Add these to the export list of `MicroHs/lib/Data/Text.hs` (and
implement them via `unpack` + `Data.List` if a streaming
implementation isn't worth it for `Data.Text`'s strict
`ByteString`-backed representation).

### Local workaround

Each call site rewrites to a `Data.List` equivalent threaded through
`T.unpack`, plus a re-pack on the way out where applicable:

- `T.all p t`         → `all p (T.unpack t)`
- `T.any p t`         → `any p (T.unpack t)`
- `T.concatMap f t`   → `T.concat (map f (T.unpack t))`
- `T.strip t`         → `T.dropWhile isSpace (T.dropWhileEnd isSpace t)` (with `import Data.Char (isSpace)`)
- `T.breakOn sep t`   → rewrite with `T.splitOn`, or define a local helper

These all evaluate equivalently on the input ranges YCHR actually
hits, and the perf hit is negligible at compiler-frontend scale.


## 5. Missing `Data.Either.partitionEithers`

`MicroHs/lib/Data/Either.hs` does not export `partitionEithers`. The
function is part of `base` (since `base-4.0`).

Used at `src/YCHR/Internal/Parser.hs:57` (four call sites in the same file).

### Upstream fix sketch

Two lines in `Data.Either`:

```haskell
partitionEithers :: [Either a b] -> ([a], [b])
partitionEithers = foldr go ([], [])
  where
    go (Left  x) (ls, rs) = (x : ls, rs)
    go (Right x) (ls, rs) = (ls, x : rs)
```

### Local workaround

Drop the `Data.Either` import and inline the same definition at the
top of `Parser.hs`. Three lines.


## 6. No `TemplateHaskell` support

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

None. `mcabal build` is expected to fail at `src/YCHR/Internal/StdLib.hs` and
`src/YCHR/Internal/TypeCheck/Compiled.hs`. Users must build with `cabal`/GHC.
This was a conscious trade-off taken when reverting from the runtime
loader (the change `2142c05` was originally motivated by) back to TH
embedding: the runtime loader had a known cwd-relative bug, and the
GHC-only fix is the cleanest available. If future work restores mhs
compat, the loaders will need a per-backend split (`src/ghc/` +
`src/mhs/`, mirroring the existing `YCHR.Internal.LineInput` pattern) — but
that machinery is intentionally not added preemptively.


## Out of scope (not gaps, just noted)

- `Data.List.foldl'` is present in MicroHs but isn't re-exported from
  `Prelude`. Modules that use it currently rely on GHC ≥ 9.6
  re-exporting it. Adding an explicit `import Data.List (foldl')` to
  each affected module (`Compile.hs`, `Compile/Occurrences.hs`,
  `Desugar.hs`, `Runtime/Interpreter.hs`) works on both compilers and
  is a one-line per-file change. Not a MicroHs bug — but flagged here
  so it isn't mistaken for one when sweeping the diff.
