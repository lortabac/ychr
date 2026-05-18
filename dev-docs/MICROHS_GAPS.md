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


## 1. Cross-module collision of generated record selectors

The biggest blocker. Causes every YCHR module that uses
`OverloadedRecordDot` on a record type whose field name is shared with
a record in another transitively-imported module to fail with errors
like:

```
Cannot satisfy constraint: HasField "kept" _a3940 [HeadConstraint]
Cannot satisfy constraint: Rule ~ (_a4 -> _a5)
```

YCHR has three rule ASTs — `YCHR.Parsed.Rule`, `YCHR.Resolved.Rule`,
`YCHR.Desugared.Rule` — each with a `head` field, and two records with
`kept` / `removed` fields (`YCHR.Desugared.Head`, `YCHR.DSL.Simpa`).
That's enough to trigger the bug pervasively.

### Root cause

`MicroHs/src/MicroHs/Deriving.hs`, `genHasField`:

```haskell
getName = mkGetName tycon fld
mkGetName tycon fld = qualIdent (mkIdent "get$") $ qualIdent tycon fld
```

`tycon` is the **unqualified** local type-constructor identifier, so
two modules that each declare `data Rule { head :: ... }` both emit a
top-level helper called `get$.Rule.head`. The corresponding instance
body — `getField _ = get$.Rule.head` — is then ambiguous in any
compilation unit that reaches both definitions through its import
graph.

Confirmed with `mhs -ddump-typecheck`: both `YCHR.Parsed` and
`YCHR.Desugared` emit `get$.Rule.head` and `get$.Rule.name` with
identical names but different signatures.

### Workaround observation

With `import YCHR.Desugared` (open import), `rule.head` works. With
`import YCHR.Desugared qualified as D` or
`import YCHR.Desugared (Rule)`, it fails. The unqualified open import
brings the ambiguous selector into scope unambiguously somehow; the
qualified / selective forms leave the instance method body
unresolvable.

### Upstream fix sketch

In `mkGetName`, qualify with the **module name** as well as the
tycon, e.g. produce `get$.YCHR.Desugared.Rule.head`. The
`HasField`/`SetField` instance bodies should reference that fully
qualified helper. This makes per-module selectors unique and
collision-free regardless of import style.

### Local workaround

At every call site that triggers the failure, replace `r.fld` (or
chained `r.fld1.fld2`) with explicit record-pattern destructuring at
the top of the function, then use plain bindings:

```haskell
-- before
foo r = ... r.head.sourceLoc ... r.head.node.kept ...

-- after
foo r =
  let D.Rule {head = headAnn} = r
      AnnP {node = headNode, sourceLoc = headLoc} = headAnn
      D.Head {kept = keptHC} = headNode
  in ... headLoc ... keptHC ...
```

The destructure pattern carries enough type information for MicroHs
to commit to a single `HasField` instance. This is the workaround
most likely to bloat the codebase — flag it as the canary for the
"give up on MicroHs compatibility" decision.


## 2. `NoFieldSelectors` is silently ignored

`MicroHs/src/MicroHs/Deriving.hs` unconditionally emits the field
selector function for every record (`Sign [getName]` + `Fcn getName`).
There is no check for the `NoFieldSelectors` extension; the pragma is
accepted by the parser but has no effect on code generation.

This is what makes gap 1 observable in YCHR: GHC under
`NoFieldSelectors` only generates `HasField` instances, not top-level
selectors, so the collision can't arise. MicroHs generates both.

### Upstream fix sketch

Honour `NoFieldSelectors` in `expandField` — when enabled, skip the
`Sign [getName]` / `Fcn getName` pair and inline the case-match
directly into the `HasField` instance method. (Or: still keep the
helper but make it private to the module — see gap 1.)

### Local workaround

None directly — this gap is only observable as gap 1, and its
workaround is the same.


## 3. Record update on a record-dot expression doesn't parse

The expression form `e.fld { f = ... }` (record update applied to the
result of a record-dot selector chain) fails with a parse error:

```
src/YCHR/Desugar.hs:642:48:
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
| `all`       | `src/YCHR/PExpr.hs:275`, `src/YCHR/PExpr.hs:843`, `src/YCHR/Backend/Scheme.hs:618`, `src/YCHR/SExpr.hs:111,113` |
| `any`       | `src/YCHR/SExpr.hs:105` |
| `concatMap` | `src/YCHR/Compile/Names.hs:75`, `src/YCHR/SExpr.hs:69` |
| `strip`     | `src/YCHR/Repl.hs:213` |
| `breakOn`   | `src/YCHR/Meta.hs:54` |

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

Used at `src/YCHR/Parser.hs:57` (four call sites in the same file).

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

YCHR uses TH to embed `libraries/*.chr` and
`typechecker/typechecker.chr` into the binary at compile time
(`YCHR.StdLib.TH`, `YCHR.TypeCheck.TH`). This makes the GHC-built
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

None. `mcabal build` is expected to fail at `src/YCHR/StdLib.hs` and
`src/YCHR/TypeCheck/Compiled.hs`. Users must build with `cabal`/GHC.
This was a conscious trade-off taken when reverting from the runtime
loader (the change `2142c05` was originally motivated by) back to TH
embedding: the runtime loader had a known cwd-relative bug, and the
GHC-only fix is the cleanest available. If future work restores mhs
compat, the loaders will need a per-backend split (`src/ghc/` +
`src/mhs/`, mirroring the existing `YCHR.LineInput` pattern) — but
that machinery is intentionally not added preemptively.


## Out of scope (not gaps, just noted)

- `Data.List.foldl'` is present in MicroHs but isn't re-exported from
  `Prelude`. Modules that use it currently rely on GHC ≥ 9.6
  re-exporting it. Adding an explicit `import Data.List (foldl')` to
  each affected module (`Compile.hs`, `Compile/Occurrences.hs`,
  `Desugar.hs`, `Runtime/Interpreter.hs`) works on both compilers and
  is a one-line per-file change. Not a MicroHs bug — but flagged here
  so it isn't mistaken for one when sweeping the diff.
