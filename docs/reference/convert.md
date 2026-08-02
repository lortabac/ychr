# Haskell Conversion Reference

> **Audience.** Haskell developers embedding YCHR who want to pass and
> receive ordinary Haskell values instead of hand-building and
> pattern-matching `Term`s.
>
> **You will** learn the `ToTerm` / `FromTerm` classes, their built-in
> instances, how to decode query results, the typed query wrapper, and
> GHC-only `Generic` derivation.
>
> **Skip if** the [DSL](dsl.md)'s `Term` combinators and raw
> `Map Text Term` results are enough for you.

> **Shortcut.** Everything on this page lives in `YCHR.Convert` and is
> re-exported from the umbrella module `YCHR`, so `import YCHR` is
> usually all you need. Two exceptions: the compile-and-run-in-one
> `runQuery` family over DSL `[Module]` values is only in
> `YCHR.Convert`, and `Generic` derivation is in the GHC-only
> `YCHR.Convert.Generic`.

`YCHR.Convert` is a companion to [`YCHR.DSL`](dsl.md): the DSL builds CHR
*programs*, while `YCHR.Convert` converts *values* at the program
boundary. That boundary is entirely the pure `Term` type — a goal is a
`Term`, and a result is a `Map Text Term` keyed by goal-variable name — so
both classes target `Term` and never touch the runtime representation.

## The two classes

```haskell
class ToTerm a where
  toTerm :: a -> Term                             -- total

class FromTerm a where
  fromTerm :: Term -> Either ConvertError a       -- fallible
```

Encoding never fails. Decoding can, so it returns `Either ConvertError`:
the term may have the wrong shape, or be an unbound variable where a
ground value was required.

## Built-in instances

| Haskell | `Term` encoding |
|---|---|
| `Integer`, `Int` | `IntTerm` (`Int` bounds-checked on decode) |
| `Double` | `FloatTerm` (strict: an `IntTerm` is *not* coerced) |
| `Bool` | `true` / `false` atom |
| `Text` | `TextTerm` — the idiomatic CHR string type |
| `Char` | one-character `TextTerm` |
| `()` | `()` atom |
| `Maybe a` | `nothing` atom / `just(x)` |
| `Either a b` | `left(x)` / `right(y)` |
| `(a, b)` … `(a, b, c, d)` | `tuple(...)`, distinguished by arity |
| `[a]` | Prolog list — cons `.`/2, nil `[]` |
| `Term` | identity |

```haskell
toTerm (Just (5 :: Int))
-- CompoundTerm (Unqualified "just") [IntTerm 5]
```

Decoding also accepts the `prelude`-qualified forms of `true`/`false` and
the list cons/nil that appear in results, so a value produced by a run
round-trips back:

```haskell
fromTerm (CompoundTerm (Qualified "prelude" "true") []) :: Either ConvertError Bool
-- Right True
```

### `String` vs `Text`

`String = [Char]`, so a `String` round-trips as a *list of one-character
`TextTerm`s* via the `Char` and `[a]` instances — not as a single
`TextTerm`. Use `Text` (with `OverloadedStrings`) when you want a single
string term.

## Hand-writing an instance

A few combinators cover the common cases: `compound` and `atomTerm` build
terms; `matchCompound` and `decodeSum` take them apart; `argAt` decodes a
positional argument; and `ground` wraps a decoder to reject unbound
variables.

```haskell
data Point = Point Int Int

instance ToTerm Point where
  toTerm (Point x y) = compound "point" [toTerm x, toTerm y]

instance FromTerm Point where
  fromTerm t = do
    as <- matchCompound "point" 2 t     -- functor "point", arity 2
    Point <$> argAt 0 as <*> argAt 1 as
```

```haskell
toTerm (Point 3 4)
-- CompoundTerm (Unqualified "point") [IntTerm 3, IntTerm 4]

fromTerm (IntTerm 1) :: Either ConvertError Point
-- Left (TypeMismatch "point" (IntTerm 1))
```

For a sum type, `decodeSum` dispatches on `(functor, arity)`:

```haskell
instance FromTerm Shape where
  fromTerm = decodeSum
    [ ("dot",    0, \_  -> Right Dot)
    , ("circle", 1, \as -> Circle <$> argAt 0 as)
    , ("rect",   2, \as -> Rect   <$> argAt 0 as <*> argAt 1 as)
    ]
```

`ConvertError` is returned as data (never thrown): `TypeMismatch`,
`ArityMismatch`, `UnknownFunctor`, `UnboundValue`, `MissingBinding`
(for result decoding), and `MalformedGoal` (for a query goal that is
not a compound term).

## Decoding query results

A run yields a `Map Text Term` keyed by goal-variable name. Decode one
variable, or the whole map:

```haskell
decodeVar      :: FromTerm a => Text -> Map Text Term -> Either ConvertError a
decodeVarMaybe :: FromTerm a => Text -> Map Text Term -> Either ConvertError (Maybe a)
lookupBinding  :: Text -> Map Text Term -> Maybe Term
```

## The typed query wrapper

`runQuery` compiles the modules (with the stdlib and the default host-call
registry), runs a goal, and decodes one goal variable — compile + run +
decode in one call. The goal is built exactly like a DSL body goal.

```haskell
import YCHR.Convert
import YCHR.DSL

doubleModule :: Module
doubleModule =
  module' "demo"
    `exporting` ["double" // 2]
    `declaring` ["double" // 2]
    `defining`  [ [term "double" [var "X", var "R"]]
                    <=> [var "R" `is` (var "X" .* int 2)] ]

main :: IO ()
main = do
  r <- runQuery [doubleModule] (term "double" [int 21, var "R"]) "R"
  print (r :: Either ConvertError Int)
  -- Right 42
```

Use `runQueryWith` to decode several variables at once (e.g. assemble a
record from `decodeVar` calls), and `runQueryWithHostCallRegistry` when the
program calls custom `host:_` functions:

```haskell
runQueryWith [m] (term "pair" [var "X", var "Y"])
  (\bs -> (,) <$> decodeVar "X" bs <*> decodeVar "Y" bs)
```

Compilation failures are thrown as `YCHR.Run.Error` (as `runDSL` does);
decoding failures are returned as `Left`.

## Reusing a compiled program

`runQuery` compiles its modules on every call. To embed a real `.chr`
module — or to run many queries against one program — compile **once**
with `YCHR.Run.compileFiles` (source files), `compileModules`
(in-memory source text), or `compileParsedModules` (DSL modules), then
drive the resulting `CompiledProgram` with `runQueryCompiled`. Each
call is an independent run with a fresh store.

```haskell
runQueryCompiled
  :: FromTerm a => CompiledProgram -> Term -> Text -> IO (Either ConvertError a)
```

```haskell
import YCHR.Convert (runQueryCompiled)
import YCHR.Run (compileFiles, displayError)

main :: IO ()
main = do
  result <- compileFiles True ["typechecker.chr"]                  -- once
  case result of
    Left err -> putStr (displayError err)
    Right (cp, _warnings) -> do
      r1 <- runQueryCompiled cp (term "typecheck" [toTerm expr1, var "R"]) "R"
      r2 <- runQueryCompiled cp (term "typecheck" [toTerm expr2, var "R"]) "R"
```

`runQueryCompiledWith` and `runQueryCompiledWithHostCallRegistry` are the
whole-map and custom-registry variants, mirroring `runQueryWith` /
`runQueryWithHostCallRegistry`.

> **Passing symbolic data.** Goal arguments are *evaluated* (like any
> tell). If you pass a compound that should stay symbolic — an
> object-language term, say — wrap it in `quote/1` with `quote expr`;
> otherwise a constructor whose name is also a declared function is called
> instead of kept as data. `quote` takes any `ToTerm` value, so it
> subsumes the `toTerm` call, and it belongs at the goal-construction site
> rather than inside a `ToTerm` instance.

For a complete worked example — a lambda-calculus type inferencer written in
CHR and driven from Haskell, including the `quote` pattern above — see
[`how-to/embed-a-chr-module.md`](../how-to/embed-a-chr-module.md) and
[`examples/stlc/`](../../examples/stlc/).

## Registering host functions

When a program calls `host:_` functions you supply, lift your Haskell
functions with the `hostFn*` adapters — they reuse the same `ToTerm` /
`FromTerm` classes — assemble a registry with `withDefaultHostFunctions`,
and run with the `…WithHostCallRegistry` variants used above. See the
[host-function reference](host-functions.md) for the adapter table and
marshalling rules.

## Generic derivation (GHC only)

Deriving `GHC.Generics.Generic` is enough to get instances for free — no
hand-written body. The helpers live in `YCHR.Convert.Generic`, which is
built only under GHC (`GHC.Generics` is unavailable on MicroHS); the core
`YCHR.Convert` stays Generics-free.

```haskell
import GHC.Generics (Generic)
import YCHR.Convert (ToTerm (..), FromTerm (..))
import YCHR.Convert.Generic (genericToTerm, genericFromTerm)

data Color = Red | Green | Blue deriving (Show, Generic)

instance ToTerm   Color where toTerm   = genericToTerm
instance FromTerm Color where fromTerm = genericFromTerm
```

```haskell
toTerm Red                                    -- CompoundTerm (Unqualified "red") []
fromTerm (toTerm Blue) :: Either ConvertError Color   -- Right Blue
```

A constructor becomes a compound whose functor is the constructor name
with its first character lowercased (`Circle 3` → `circle(3)`, `Red` →
`red`). Fields are positional in declaration order; a nullary constructor
is an atom. Record field names are ignored, so a generic-derived instance
agrees with a hand-written positional one.
