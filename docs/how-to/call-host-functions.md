# How to call host-language functions

> **Goal:** invoke a host primitive from a YCHR program, and register your
> own host functions from Haskell when embedding YCHR as a library.

## The `host:` namespace

`host:f(args)` calls a function provided by the runtime rather than a CHR
rule or a user-defined function. Its arguments and result are untyped
(`any` to the type checker). The prelude's arithmetic and comparison
operators are thin wrappers over `host:` primitives:

```prolog
X + Y -> host:'+'(X, Y).
```

For the built-in primitives (arithmetic, comparisons, type predicates,
term meta, I/O, `'$call'`), see [`prelude.md`](../reference/prelude.md),
`libraries/prelude.chr`, and `src/YCHR/Internal/Runtime/`.

## Registering your own host functions

When you embed YCHR as a Haskell library, you can back a `host:` call with
your own Haskell code. Lift a plain function with the `hostFn*` adapters,
collect the entries into a registry, and run with a `…WithHostCallRegistry`
query variant. The YCHR names below all come from a single `import YCHR`.

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
    Left err -> fail (show err)
    Right (cp, _warnings) -> do
      -- 3. Run against the custom registry and decode the result.
      r <- runQueryCompiledWithHostCallRegistry registry cp
             (CompoundTerm (Unqualified "compute") [IntTerm 2, VarTerm "R"])
             (decodeVar "R")
      print (r :: Either ConvertError Int)
      -- Right 5
```

`withDefaultHostFunctions` keeps the built-ins available alongside your
functions; a custom entry with the same name as a built-in overrides it.
For an effectful implementation (I/O, dereferencing, store access), use the
`hostFn*M` variants (their body runs in `Chr`); for a fixed-shape need
outside the marshalling, use the raw `hostFnValues`.

See the [host-function reference](../reference/host-functions.md) for the
full adapter table, marshalling rules, and error behaviour.

## Wrapping a host call with a typed signature

A `:- function` declaration narrows the types at the wrapper boundary even
though the underlying `host:` call is untyped — the wrapper is where a
statically-typed program regains its guarantees. See
[Add types to a program](add-types.md).

## See also

- [Host-function reference](../reference/host-functions.md).
- [Prelude reference](../reference/prelude.md).
- [Embed a CHR module in Haskell](embed-a-chr-module.md).
