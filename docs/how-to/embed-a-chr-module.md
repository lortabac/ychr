# How to embed a CHR module in a Haskell program

Worked example: a Curry-style simply-typed lambda-calculus type
inferencer written in CHR, driven from Haskell. Sources:
[`examples/stlc/`](../../examples/stlc/). With no arguments it is a
REPL — each line is parsed by a tiny `parsec` grammar
([`Parser.hs`](../../examples/stlc/Parser.hs)) and becomes one
`runQueryCompiled` call. `--demo` prints a fixed table:

```sh
cabal run stlc-typechecker -- --demo
```

```
Curry-style STLC type inference (via a CHR module):

\x. x + 1                  :  int -> int
\x. x                      :  a -> a
(\x. x + 1) 5              :  int
\x. \y. x                  :  a -> b -> a
\f. \x. f (f x)            :  (a -> a) -> a -> a
let f = \x. x + 1 in f 5   :  int
\x. x x                    :  TYPE ERROR: cannot construct the infinite type (_ -> _)
1 2                        :  TYPE ERROR: cannot unify int with (int -> _)
y                          :  TYPE ERROR: unbound variable y
```

## 1. The CHR module

[`stlc.chr`](../../examples/stlc/stlc.chr) exports one entry
constraint, `typecheck/2`, and the object language as a declared,
exported type:

```prolog
:- module(stlc, [typecheck/2, type(expr/0)]).

:- chr_type expr ---> evar(string)
                    ; lam(string, expr)
                    ; app(expr, expr)
                    ; lit_int(int)
                    ; add(expr, expr).
```

Export the type. Goal arguments are renamed like rule-head arguments,
so a bare `evar` becomes `stlc:evar` and matches the compiled heads.
An unexported type stays unqualified in the goal, its rules never
fire, and the result variable comes back unbound
(`Note [Goal argument canonicalization]` in
[`src/YCHR/Convert.hs`](../../src/YCHR/Convert.hs)).

Type errors are *reported* into an accumulator through a custom
`unify_ty` constraint — a raw `=` failure would abort the run.
Residual type variables are numbered with `term_variables` at the
end, so `\x. x` comes back as `arrow(tvar(0), tvar(0))`.

## 2. Encode the input with `ToTerm`

One `compound` per constructor:

```haskell
data Expr = Var Text | Lam Text Expr | App Expr Expr | IntLit Integer | Add Expr Expr

instance ToTerm Expr where
  toTerm (Var x)    = compound "evar" [toTerm x]
  toTerm (Lam x b)  = compound "lam" [toTerm x, toTerm b]
  toTerm (App f a)  = compound "app" [toTerm f, toTerm a]
  toTerm (IntLit n) = compound "lit_int" [toTerm n]
  toTerm (Add a b)  = compound "add" [toTerm a, toTerm b]
```

```haskell
typecheckGoal :: Expr -> Term
typecheckGoal e = compound "typecheck" [toTerm e, VarTerm "Result"]
```

Goal arguments are evaluated, but `evar/1` resolves to an exported
constructor, so it stays data — no `quote` needed. It is `evar`, not
`var`, because the prelude has a `var/1` function and a bare
constructor may not share a name with a visible function
(`YCHR-20020`). Undeclared compounds have no such protection: wrap
them in `quote` ([reusing a compiled
program](../reference/convert.md#reusing-a-compiled-program)).

## 3. Decode the result with `FromTerm`

The answer is `ok(Type)` or `type_error(Errors)`. `decodeSum`
dispatches on the local functor name, so `stlc:arrow` decodes:

```haskell
data Type = TInt | TArrow Type Type | TVar Int

instance FromTerm Type where
  fromTerm = decodeSum
    [ ("tint",  0, \_  -> Right TInt)
    , ("arrow", 2, \as -> TArrow <$> argAt 0 as <*> argAt 1 as)
    , ("tvar",  1, \as -> TVar   <$> argAt 0 as)
    ]
```

## 4. Compile once, query many

[`Main.hs`](../../examples/stlc/Main.hs) embeds the `.chr` source with
a Template Haskell splice, compiles it once, and runs one
`runQueryCompiled` per term:

```haskell
cp <- case compileModules stdlib True [(stlcPath, embeddedSource)] of
        Right (cp, _warnings) -> pure cp
        Left err              -> fail (displayError err)

result <- runQueryCompiled cp (typecheckGoal e) "Result"
  :: IO (Either ConvertError TCResult)
```

All of it — `compileModules`, `CompiledProgram`, `runQueryCompiled`,
`ToTerm`/`FromTerm`, `compound`/`decodeSum`/`argAt` — is one
`import YCHR`. For a `.chr` file on disk use `compileFiles`. Variants:
[convert.md §Reusing a compiled program](../reference/convert.md#reusing-a-compiled-program).

## 5. Supplying the resources

The `ychr` library embeds nothing at compile time. Its two
compile-time resources are explicit arguments, because they are needed
at different points and a MicroHs build has no Template Haskell to bake
them in:

| resource | type | who needs it |
|---|---|---|
| the standard library | `StdLib` (`YCHR.Internal.StdLib`) | every entry point that compiles: `compileModules`, `compileFiles`, `compileParsedModules`, `compileTypeCheckerModules`, the three `runQuery*` variants and the two `runDSL*` variants |
| the type-checker | `SessionInput` (`YCHR.Internal.Runtime.Session`) | every entry point that type-checks: `typeCheckProgram`, `typeCheckGoals`, `prepareQuery`, `runPreparedGoal`, `runProgramWithGoal`, `runProgramWithQuery` |

`YCHR.Run.prepareQueryUnchecked` is the checker-free companion of
`prepareQuery` (the REPL's `--no-check` path uses it), and
`YCHR.Internal.Repl.runRepl` takes the checker as a `Maybe`: `Nothing`
skips the checker the way `--no-check` does.

Each is built once, from the bundled sources, and reused. A minimal
`Resources.hs` for a GHC embedder that wants a self-contained binary:

```haskell
{-# LANGUAGE TemplateHaskell #-}

module Resources (stdlib, typeCheckerProgram) where

import Data.List (sort)
import Data.Text (Text)
import Data.Text.IO qualified as TIO
import Language.Haskell.TH (Exp, Q)
import Language.Haskell.TH.Syntax (lift, runIO)
import System.Directory (listDirectory)
import System.FilePath (takeExtension, (</>))
import YCHR.Internal.Runtime.Session (SessionInput)
import YCHR.Internal.StdLib (StdLib, parseStdLib)
import YCHR.Internal.TypeCheck.Compiled (compileTypeCheckerModules)

-- Every *.chr in a directory, sorted, paired with its path and contents.
chrDirSources :: FilePath -> Q Exp
chrDirSources dir = do
  files <-
    runIO (sort . filter ((== ".chr") . takeExtension) <$> listDirectory dir)
  pairs <-
    mapM
      (\f -> let p = dir </> f in runIO ((p,) <$> TIO.readFile p))
      files
  lift (pairs :: [(FilePath, Text)])

stdlib :: StdLib
stdlib = case parseStdLib $(chrDirSources "libraries") of
  Right m -> m
  Left err -> error ("Failed to parse embedded standard library: " ++ show err)

typeCheckerProgram :: SessionInput
typeCheckerProgram =
  case compileTypeCheckerModules stdlib $(chrDirSources "typechecker") of
    Right si -> si
    Left err -> error ("Failed to compile embedded typechecker: " ++ show err)
```

(The repository's own copies — one generator module per directory, plus
[`embed/YCHR/Embedded.hs`](../../embed/YCHR/Embedded.hs) for the two
splices — also register each file for recompilation with
`addDependentFile`.)

Without Template Haskell, read the same two directories at run time and
hand the lists to `parseStdLib` / `compileTypeCheckerModules`. The
library ships that loop as
[`YCHR.Internal.Resources`](../../src/YCHR/Internal/Resources.hs):
`loadResources` looks the sources up under `$YCHR_LIB_DIR`, or the
current directory when that variable is unset or empty — point it at a
YCHR source tree (the directory holding `libraries/` and `typechecker/`).
This is the path the MicroHs build takes: the `ychr` executable's
`YCHR.Embedded` has a MicroHs twin
([`src/mhs/YCHR/Embedded.hs`](../../src/mhs/YCHR/Embedded.hs)) that
re-exports `loadResources`, while the GHC one returns the values its
splice baked in and touches no filesystem. Keep the type-checker binding
lazy if the program never type-checks (`SessionInput` is only forced on
first use), and note that the standard library is always needed: the
prelude is seeded into every compilation.
