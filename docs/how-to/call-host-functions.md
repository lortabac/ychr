# How to call host-language functions

`host:f(args)` calls a function the runtime provides, not a CHR rule
or a `:- function`. Arguments and result are `any` to the type
checker. Semantics: [language reference](../reference/language.md#host-calls).
Built-in primitives (arithmetic, comparisons, type predicates, term
meta, I/O): [`libraries/prelude.chr`](../../libraries/prelude.chr).

## Register your own

Lift a Haskell function with a `hostFn*` adapter, put it in a
registry, run with a `…WithHostCallRegistry` query. Every name below
comes from `import YCHR`.

```haskell
{-# LANGUAGE OverloadedStrings #-}
import Data.Text (Text)
import YCHR

-- 1. A program that calls host:my_add — compilation does not resolve the
--    name; the registry supplies it at run time.
source :: Text
source =
  ":- chr_constraint compute/2.\n\
  \compute(X, R) <=> R is host:my_add(X, 3).\n"

-- 2. Register the Haskell implementation. hostFn2 marshals the Int
--    arguments and result through ToTerm / FromTerm for you.
registry :: HostCallRegistry
registry = withDefaultHostFunctions
  [ ("my_add", hostFn2 ((+) :: Int -> Int -> Int)) ]

main :: IO ()
main =
  case compileModules True [("compute.chr", source)] of
    Left err -> putStr (displayError err)
    Right (cp, _warnings) -> do
      -- 3. Run against the custom registry and decode the result.
      r <- runQueryCompiledWithHostCallRegistry registry cp
             (CompoundTerm (Unqualified "compute") [IntTerm 2, VarTerm "R"])
             (decodeVar "R")
      print (r :: Either ConvertError Int)
      -- Right 5
```

Adapter table, registry semantics, marshalling and errors:
[convert.md §Registering host functions](../reference/convert.md#registering-host-functions).

## Give it a type

A `host:` call is untyped. A `:- function` wrapper types the boundary:

```prolog
:- function my_add(int, int) -> int.
my_add(X, Y) -> host:my_add(X, Y).
```

Callers of `my_add/2` are now checked against `(int, int) -> int`.

## See also

- [Haskell conversion reference](../reference/convert.md)
- [Embed a CHR module in Haskell](embed-a-chr-module.md)
