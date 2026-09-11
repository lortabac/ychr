# Haskell DSL Reference

`import YCHR.DSL` builds CHR *programs* as Haskell values. It is an
opt-in companion to the umbrella `YCHR` module, which does not
re-export it. Every combinator builds the same `Module` value the
parser produces from `.chr` text; validation (undeclared constraints,
ill-typed bodies) happens in the compilation pipeline, as for parsed
input. Use it when the program is built or generated from Haskell;
`.chr` files on disk go through `compileFiles`.

## Building blocks

| Kind | Type | Built by |
|---|---|---|
| Module | `Module` | `module'`, then `importing`/`library`/`declaring`/`defining`/`withEquations`/`withExtensions`/`chrType`/`exporting` |
| Declaration | `Declaration` | `(//)`, `function`, `openFunction`, `class_`, `openClass`, `extendClassType`, `typeExport`, `op` |
| Rule | `Rule` | `(<=>)`, `(==>)`, `(\\)` (with `<=>`), `(@:)`, `(\|-)` |
| Term | `Term` | `var`, `atom`, `int`, `float`, `bool`, `text`, `wildcard`, `term`, `qterm`, `quote` |

Constraint occurrences, function calls and data-constructor terms are
all compound terms, classified by what is declared; `term` (qualified:
`qterm`) builds all of them. Append-style modifiers (`importing`,
`declaring`, `defining`, `withEquations`, `chrType`, `library`)
accumulate across calls.

## Mapping from `.chr` to DSL

| Surface CHR | DSL |
|---|---|
| `:- module(order, [leq/2]).` | `module' "order" \`exporting\` ["leq" // 2]` |
| `:- chr_constraint leq/2.` | `\`declaring\` ["leq" // 2]` |
| `:- function factorial/1.` | `\`declaring\` [function "factorial" 1]` |
| `:- class size/1.` | `\`declaring\` [class_ "size" 1]` |
| `:- open_function f/1.` | `\`declaring\` [openFunction "f" 1]` |
| `:- open_class f/1.` | `\`declaring\` [openClass "f" 1]` |
| `:- extend_class_type (f(int) -> int).` | `\`declaring\` [extendClassType "f" [TypeCon (Unqualified "int") []] (TypeCon (Unqualified "int") [])]` |
| `:- extend_function f(X) -> X.` | `\`withExtensions\` [equation "f" [var "X"] [] (var "X")]` |
| `:- extend_class f(X) -> X.` | `\`withClassExtensions\` [equation "f" [var "X"] [] (var "X")]` |
| `:- chr_type color ---> red ; green.` | `\`chrType\` tyDef "color" [] [dataCtor "red" [], dataCtor "green" []]` |
| `:- use_module(other).` | `\`importing\` ["other"]` |
| `:- use_module(library(lists)).` | `\`library\` "lists"` |
| `name @ leq(X, Y), leq(Y, X) <=> X = Y.` | `"name" @: [term "leq" [var "X", var "Y"], term "leq" [var "Y", var "X"]] <=> [var "X" .=. var "Y"]` |
| `kept \ removed <=> body.` | `[kept] \\ [removed] <=> [body]` |
| `head ==> body.` | `[head] ==> [body]` |
| `head <=> guard \| body.` | `[head] <=> [body] \|- [guard]` |
| `R is X * 2.` | `var "R" \`is\` (var "X" .* int 2)` (or with the `Num` instance, `var "X" * 2`) |
| `c(quote(plus(X, 3))).` | `term "c" [quote (term "plus" [var "X", int 3])]` |
| `host:print(X).` | `hostCall "print" [var "X"]` |

## Rules

### Simplification

```haskell
[term "leq" [var "X", var "X"]] <=> [bool True]
```

`[bool True]` is the empty body (`... <=> true.`).

### Propagation

```haskell
[term "leq" [var "X", var "Y"], term "leq" [var "Y", var "Z"]]
  ==> [term "leq" [var "X", var "Z"]]
```

### Simpagation

```haskell
[term "leq" [var "X", var "Y"]] \\ [term "leq" [var "X", var "Y"]]
  <=> [bool True]
```

`\\` yields a `Simpa` that the same `<=>` consumes (`IsRuleHead`).

### Naming and guards

```haskell
"low" @: [term "clamp" [var "X", var "Lo", var "R"]]
        <=> [var "R" .=. var "Lo"]
        |- [var "X" .< var "Lo"]
```

`@:` (`infixr 0`) names a finished rule; `|-` (`infixl 1`) attaches a
guard list. The chained form needs no parentheses.

## Functions and types

Equations go in with `withEquations`, type definitions with `chrType`:

```haskell
module' "fact"
  `exporting` ["compute" // 1]
  `declaring` ["compute" // 1, function "factorial" 1]
  `withEquations`
    [ equation "factorial" [int 0] [] (int 1)
    , equation "factorial" [var "N"] [var "N" .> int 0]
        (var "N" .* call_ (funRef "factorial" 1) [var "N" .- int 1])
    ]
  `defining`
    [ [term "compute" [var "R"]]
        <=> [var "R" `is` call_ (funRef "factorial" 1) [int 5]]
    ]
```

`call_ f args` is `'$call'(F, A...)`; `funRef "f" 2` is `fun f/2`.
Lambdas:

```haskell
lambda [var "X"] (var "X" .+ int 1)
```

is `fun(X) -> X + 1 end`.

## Numeric and comparison sugar

`Term` is a `Num` instance:

```haskell
var "R" `is` (1 + var "X" * 2)        -- with the Num instance
var "R" `is` (int 1 .+ var "X" .* int 2)  -- explicit, equivalent
```

Comparisons use the prefixed operators, mapping to the operators
declared in [`libraries/prelude.chr`](../../libraries/prelude.chr):

| DSL | Surface |
|---|---|
| `.<` | `<` |
| `.<=` | `=<` |
| `.>` | `>` |
| `.>=` | `>=` |
| `.==` | `==` |

No inequality operator: negate with the prelude's `not/1`. Structural
unification (CHR's `=`) is `.=.`:

```haskell
var "X" .=. var "Y"
```

## Compiling and running

`runDSL` compiles the modules with the stdlib and runs one goal with
the CLI's default registry (builtins, meta and search host calls):

```haskell
import YCHR.DSL
import qualified Data.Map.Strict as Map

main :: IO ()
main = do
  let m = module' "g"
            `exporting` ["clamp" // 3]
            `declaring` ["clamp" // 3]
            `defining`
              [ "low"  @: [term "clamp" [var "X", var "Lo", var "R"]]
                          <=> [var "R" .=. var "Lo"] |- [var "X" .<  var "Lo"]
              , "high" @: [term "clamp" [var "X", var "Lo", var "R"]]
                          <=> [var "R" .=. var "X" ] |- [var "X" .>= var "Lo"]
              ]
  bindings <- runDSL [m] (term "clamp" [int 3, int 5, var "R"])
  print (Map.lookup "R" bindings)
  -- Just (IntTerm 5)
```

Goal arguments are renamed like a surface-text goal's: a bare
`atom "red"` or `term "red" []` naming an exported constructor
(`typeExport`) becomes `m:red`, which the compiled heads match; an
unexported one stays bare and its rules never fire
(`Note [Goal argument canonicalization]` in
[`src/YCHR/Convert.hs`](../../src/YCHR/Convert.hs)).

Custom `host:` functions:

```haskell
runDSLWithHostCallRegistry myHostCalls [m] (term "g" [var "R"])
```

`YCHR.DSL` exports `HostCallRegistry`; the builders (`hostFunctions`,
`withDefaultHostFunctions`, `hostFn*`) need `import YCHR.Convert` or
`import YCHR` — see
[convert.md §Registering host functions](convert.md#registering-host-functions).

Finer control (several goals, one compiled program for many runs,
warnings): `compileParsedModules True modules` is `compileFiles True
paths` minus parsing (`False` skips the stdlib); feed the result to
`runProgramWithGoalDSL` / `runProgramWithQuery` (re-exported from
`YCHR.Run`). Compilation and runtime errors are exceptions
(`YCHR.Run.Error` and the runtime's error types).

## Pitfalls

- **Variables vs. atoms.** `var "X"` and `atom "x"` are different
  things. `Term` is not an `IsString` instance; there is no coercion
  from string literals.
- **Head coercion.** `<=>` / `==>` / `\\` / `runDSL` accept `[Term]`
  and coerce each compound to a `Constraint`; a bare variable or
  literal in head or goal position throws
  `YCHR.DSL: term is not a valid constraint occurrence` (an `error`,
  not a diagnostic — the mirror of the parser's `MalformedConstraint`).
- **Orphan `Num Term`.** `1 + 2 :: Term` is the symbolic compound
  `+(1, 2)` wherever `YCHR.DSL` and `Term` are both in scope. `negate`
  on a non-literal, `abs` and `signum` build `-/1`, `abs/1`, `sign/1`
  compounds the prelude does not declare; prefer `.-` and friends. No
  `Fractional` instance: use `float`.
- **`exporting` switches to an explicit export list.** Without it a
  module exports everything; further `exporting` calls append.
- **Runnable.** Every snippet here is from `test/YCHR/DSLTest.hs`
  (`endToEnd` group):
  `cabal test ychr-tests --test-options='-p endToEnd'`.
