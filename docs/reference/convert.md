# Haskell Conversion Reference

Everything here is `YCHR.Convert`, re-exported from `YCHR`. Not in
`YCHR`: the `runQuery` family over DSL `[Module]`s (`YCHR.Convert` only)
and `Generic` derivation (`YCHR.Convert.Generic`, GHC only).

[`YCHR.DSL`](dsl.md) builds *programs*; this module converts *values*
at the boundary. That boundary is the pure `Term` type — a goal is a
`Term`, a result is a `Map Text Term` keyed by goal-variable name — so
neither class touches the runtime representation.

## The two classes

```haskell
class ToTerm a where
  toTerm :: a -> Term                             -- total

class FromTerm a where
  fromTerm :: Term -> Either ConvertError a       -- fallible
```

Encoding never fails. Decoding returns `Either ConvertError`: wrong
shape, or an unbound variable where a ground value was required.

## Built-in instances

| Haskell | `Term` encoding |
|---|---|
| `Integer`, `Int` | `IntTerm` (`Int` bounds-checked on decode) |
| `Double` | `FloatTerm` (strict: an `IntTerm` is *not* coerced) |
| `Bool` | `true` / `false` — a real boolean at run time, not an atom |
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

A `Bool` is the native boolean a rule's `true`/`false` produces, so a
host function returning `Bool` works with `not/1`, `boolean/1` and a
`f(true) -> ...` equation. A module declaring its own `true/0`
constructor cannot carry it across this bridge.

Decoding also accepts the `prelude`-qualified `true`/`false` and list
cons/nil that results contain, so a run's output round-trips:

```haskell
fromTerm (CompoundTerm (Qualified "prelude" "true") []) :: Either ConvertError Bool
-- Right True
```

### `String` vs `Text`

`String = [Char]` round-trips as a *list of one-character `TextTerm`s*
via the `Char` and `[a]` instances, not as one `TextTerm`. Use `Text`
(with `OverloadedStrings`) for a single string term.

## Hand-writing an instance

`compound` and `atomTerm` build terms; `matchCompound` and `decodeSum`
take them apart; `argAt` decodes a positional argument; `ground` wraps
a decoder to reject unbound variables.

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

Sum types: `decodeSum` dispatches on `(functor, arity)`:

```haskell
instance FromTerm Shape where
  fromTerm = decodeSum
    [ ("dot",    0, \_  -> Right Dot)
    , ("circle", 1, \as -> Circle <$> argAt 0 as)
    , ("rect",   2, \as -> Rect   <$> argAt 0 as <*> argAt 1 as)
    ]
```

`ConvertError` is data, never thrown: `TypeMismatch`, `ArityMismatch`,
`UnknownFunctor`, `UnboundValue`, `MissingBinding` (result decoding),
`MalformedGoal` (a query goal that is not a compound term).

## Decoding query results

A run yields a `Map Text Term` keyed by goal-variable name:

```haskell
decodeVar      :: FromTerm a => Text -> Map Text Term -> Either ConvertError a
decodeVarMaybe :: FromTerm a => Text -> Map Text Term -> Either ConvertError (Maybe a)
lookupBinding  :: Text -> Map Text Term -> Maybe Term
```

## The typed query wrapper

`runQuery` compiles the modules (stdlib, default host-call registry),
runs a goal, and decodes one goal variable. The goal is built like a
DSL body goal. The `StdLib` is an explicit first argument, because the
`ychr` library embeds nothing at compile time — see
[Supplying the resources](../how-to/embed-a-chr-module.md#5-supplying-the-resources).

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
  r <- runQuery stdlib [doubleModule] (term "double" [int 21, var "R"]) "R"
  print (r :: Either ConvertError Int)
  -- Right 42
```

`runQueryWith` decodes the whole map; `runQueryWithHostCallRegistry`
takes a custom registry (both take the `StdLib` first):

```haskell
runQueryWith stdlib [m] (term "pair" [var "X", var "Y"])
  (\bs -> (,) <$> decodeVar "X" bs <*> decodeVar "Y" bs)
```

Compilation failures are thrown as `YCHR.Run.Error` (as `runDSL`
does); decoding failures come back as `Left`.

## Reusing a compiled program

`runQuery` recompiles on every call. Compile once with
`YCHR.Run.compileFiles` (source files), `compileModules` (in-memory
source text) or `compileParsedModules` (DSL modules), then run
`runQueryCompiled` on the `CompiledProgram`. Each call is an
independent run with a fresh store, and none of the four type-checks a
goal, so no type-checker input is needed.

```haskell
runQueryCompiled
  :: FromTerm a => CompiledProgram -> Term -> Text -> IO (Either ConvertError a)
```

`runQueryCompiledWith` and `runQueryCompiledWithHostCallRegistry`
mirror `runQueryWith` / `runQueryWithHostCallRegistry`. Examples:
[README §Library](../../README.md#using-ychr-as-a-haskell-library)
(compile once, query many) and
[embed a CHR module](../how-to/embed-a-chr-module.md) with
[`examples/stlc/`](../../examples/stlc/).

Passing symbolic data: goal arguments are canonicalized like rule-head
arguments, so export the type they belong to, wrap an *undeclared*
compound in `quote`, and expect rename failures (`YCHR-20020`,
`YCHR-20012`, `YCHR-20010`) as thrown `Error`s. Full story:
`Note [Goal argument canonicalization]` in
[`src/YCHR/Convert.hs`](../../src/YCHR/Convert.hs).

## Registering host functions

A `host:f(args)` call resolves at run time against a
`HostCallRegistry`. The prelude's operators are thin wrappers over
registered host functions (`X + Y -> host:'+'(X, Y).`); add your own
the same way. Everything here is re-exported from `YCHR`.

| Adapter | Lifts | Notes |
|---|---|---|
| `hostFn1`, `hostFn2`, `hostFn3` | `a -> b -> r` | arguments `FromTerm`, result `ToTerm` |
| `hostFn1M`, `hostFn2M`, `hostFn3M` | `a -> b -> Chr r` | body runs in `Chr`: `liftIO`, `deref`, store access |
| `hostFn0M` | `Chr r` | nullary, effectful (a pure nullary is a constant) |
| `hostFnN` | `[Term] -> Either ConvertError Term` | variadic |
| `hostFnValues` | `[Value] -> Chr Value` | raw, no marshalling |

`hostFunctions [("my_add", hostFn2 ((+) :: Int -> Int -> Int))]`
builds a registry; the name is the bare functor at the call site.
`withDefaultHostFunctions` unions your entries over the default
registry (builtins, meta and search); on a clash yours wins. Run with
`runQueryCompiledWithHostCallRegistry`, or
`runQueryWithHostCallRegistry` for DSL modules. Complete program:
[the how-to](../how-to/call-host-functions.md).

Compilation does not resolve `host:` names; an unknown one is a
run-time error when the call fires.

Arguments are dereferenced recursively before decoding, so a variable
bound inside a compound argument arrives resolved. A result need not
be ground; each distinct `VarTerm` in it becomes a fresh variable.
Marshalling failures are runtime errors:

| Situation | Error |
|---|---|
| Wrong argument count | `host call: expected N argument(s), got M` |
| Undecodable argument | `host call: TypeMismatch …` |
| Unbound argument | `host call: UnboundValue …` |

`UnboundValue` is an instantiation failure: in a rule guard it makes
the guard false and binding the variable retries the rule
([soft guard failure](language.md#soft-guard-failure)). The other two
are hard errors everywhere. Decode an argument as `Term` if it may
legitimately be unbound.

`hostFnValues` gets its arguments dereferenced at the top level only;
chase nested variables with `deref`. Compare `Value`s with `equal`
(CHR's `==`). There is no `Eq Value` on purpose: a derived instance
would compare variables by reference.

## Generic derivation (GHC only)

`YCHR.Convert.Generic` derives both instances from
`GHC.Generics.Generic`. It is built only under GHC (`GHC.Generics` is
unavailable on MicroHs); `YCHR.Convert` itself stays Generics-free.

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
`red`). Fields are positional in declaration order; a nullary
constructor is an atom. Record field names are ignored, so a
generic-derived instance agrees with a hand-written positional one.
