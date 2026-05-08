# Haskell DSL Reference

> **Audience.** Haskell developers who want to embed YCHR as a library —
> build CHR programs from Haskell code, compile and run them in-process,
> without writing or shipping `.chr` files.
>
> **You will** learn how the combinators in `YCHR.DSL` map to the surface
> language, and how to compile and run a DSL-built program.
>
> **Skip if** you only ever compile `.chr` files from disk.

The DSL lives in [`YCHR.DSL`](../../src/YCHR/DSL.hs) and is a thin layer
over the surface AST in [`YCHR.Parsed`](../../src/YCHR/Parsed.hs). Every
combinator is a pure function that builds the same `Module` value the
parser would produce from `.chr` text. Validation (undeclared constraints,
ill-typed bodies, etc.) is deferred to the compilation pipeline, exactly
as for parsed input.

## When to use the DSL

| Situation | Use |
|---|---|
| Shipping a stand-alone interpreter | `.chr` files + `compileFiles` |
| Embedding CHR in a Haskell application | `YCHR.DSL` + `runDSL` |
| Generating CHR programs at runtime (rule synthesis, search) | `YCHR.DSL` |
| Library tests that exercise the full pipeline | `YCHR.DSL` |

## The four building blocks

A DSL program is built from four kinds of value:

| Kind | Type | Built by |
|---|---|---|
| Module | `Module` | `module'`, then `importing`/`library`/`declaring`/`defining`/`withEquations`/`chrType`/`exporting` |
| Declaration | `Declaration` | `(//)`, `function`, `openFunction`, `typeExport`, `op` |
| Rule | `Rule` | `(<=>)`, `(==>)`, `(\\)` (with `<=>`), `(@:)`, `(\|-)` |
| Term | `Term` | `var`, `atom`, `int`, `float`, `bool`, `text`, `wildcard`, `term`, `qterm` |

The surface language doesn't distinguish a constraint occurrence
(`leq(X, Y)`), a function call (`factorial(5)`), and a data-constructor
term (`cons(H, T)`) — they're all the same compound-term shape, and the
renamer/desugarer classifies them by what's been declared. The DSL
matches that: there is a single `term` (and qualified `qterm`)
constructor for compound terms, used for rule-head occurrences,
body goals, and arbitrary terms alike.

All append-style modifiers (`importing`, `declaring`, `defining`,
`withEquations`, `chrType`, `library`) accumulate; calling them more than
once on the same module is the same as calling them once with the
combined arguments.

## Mapping from `.chr` to DSL

| Surface CHR | DSL |
|---|---|
| `:- module(order, [leq/2]).` | `module' "order" \`exporting\` ["leq" // 2]` |
| `:- chr_constraint leq/2.` | `\`declaring\` ["leq" // 2]` |
| `:- function factorial/1.` | `\`declaring\` [function "factorial" 1]` |
| `:- chr_type color ---> red ; green.` | `\`chrType\` tyDef "color" [] [dataCtor "red" [], dataCtor "green" []]` |
| `:- use_module(other).` | `\`importing\` ["other"]` |
| `:- use_module(library(lists)).` | `\`library\` "lists"` |
| `name @ leq(X, Y), leq(Y, X) <=> X = Y.` | `"name" @: [term "leq" [var "X", var "Y"], term "leq" [var "Y", var "X"]] <=> [var "X" .=. var "Y"]` |
| `kept \ removed <=> body.` | `[kept] \\ [removed] <=> [body]` |
| `head ==> body.` | `[head] ==> [body]` |
| `head <=> guard \| body.` | `[head] <=> [body] \|- [guard]` |
| `R is X * 2.` | `var "R" \`is\` (var "X" .* int 2)` (or with the `Num` instance, `int 1 + var "X"`) |
| `host:print(X).` | `hostCall "print" [var "X"]` |

## Rules

All four rule combinators produce the same `Rule` AST node the parser
emits, so they go through the same renaming, desugaring, and type-checking.

### Simplification

```haskell
[term "leq" [var "X", var "X"]] <=> [bool True]
```

The body `[bool True]` is the canonical empty body — it desugars to
nothing, exactly like the surface `... <=> true.`.

### Propagation

```haskell
[term "leq" [var "X", var "Y"], term "leq" [var "Y", var "Z"]]
  ==> [term "leq" [var "X", var "Z"]]
```

The same `term` constructor builds head occurrences and body goals;
the desugarer classifies a compound-term goal whose name resolves to a
declared constraint as a body constraint call.

### Simpagation

```haskell
[term "leq" [var "X", var "Y"]] \\ [term "leq" [var "X", var "Y"]]
  <=> [bool True]
```

`\\` produces an intermediate `Simpa` value; the same `<=>` operator
consumes it via the `IsRuleHead` typeclass.

### Naming and guards

```haskell
"low" @: [term "clamp" [var "X", var "Lo", var "R"]]
        <=> [var "R" .=. var "Lo"]
        |- [var "X" .< var "Lo"]
```

`@:` (loosest, `infixr 0`) wraps a finished rule with a name. `|-`
(`infixl 1`) attaches a guard list. The fixities are chosen so that
chained CHR-like notation parses without parentheses.

## Functions and types

Function equations are appended to a module with `withEquations`; type
definitions with `chrType`.

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

`call_ f args` builds the surface `'$call'(F, A...)`; `funRef "f" 2`
builds the surface `fun f/2`.

Anonymous functions use `lambda`:

```haskell
lambda [var "X"] (var "X" .+ int 1)
```

which corresponds to the surface `fun(X) -> X + 1 end`.

## Numeric and comparison sugar

`Term` is an instance of `Num`, so integer literals and the standard
arithmetic operators compile to the corresponding surface compounds:

```haskell
var "R" `is` (1 + var "X" * 2)        -- with the Num instance
var "R" `is` (int 1 .+ var "X" .* int 2)  -- explicit, equivalent
```

For comparisons in guards, use the prefixed operators (mapping to the
prelude operators in [`docs/reference/prelude.md`](prelude.md)):

| DSL | Surface |
|---|---|
| `.<` | `<` |
| `.<=` | `=<` |
| `.>` | `>` |
| `.>=` | `>=` |
| `.==` | `==` |

YCHR's prelude has no built-in inequality operator; for "X /= Y" write
the negation explicitly (e.g. through a host call or a user function).

For structural unification (the `=` of CHR), use `.=.`:

```haskell
var "X" .=. var "Y"
```

## Compiling and running

The simplest path is `runDSL`. It compiles the given modules with the
stdlib and runs a single goal using the same default host-call registry
the `ychr` CLI uses (`baseHostCallRegistry <> metaHostCallRegistry`).

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

If you need to register custom `host:_` functions, use
`runDSLWithHostCallRegistry`:

```haskell
runDSLWithHostCallRegistry myHostCalls [m] (term "g" [var "R"])
```

For finer control — multi-goal queries, reusing a compiled program
across several runs, or inspecting warnings — call `compileParsedModules`
directly and feed the result to `runProgramWithGoalDSL` /
`runProgramWithQuery` (re-exported from `YCHR.Run`).

`compileParsedModules True modules` is the equivalent of `compileFiles
True paths` for DSL-built modules: it runs the same pipeline minus the
parsing step. Pass `False` for `includeStdlib` if you want to compile
without auto-importing stdlib libraries.

Compilation errors and runtime errors are raised as exceptions
(`YCHR.Run.Error` and the runtime's standard error types).

## Pitfalls

- **Variables vs. atoms.** `var "X"` and `atom "x"` are different things.
  `Term` is *not* an `IsString` instance — there is no auto-coercion from
  string literals. Always use the right constructor.
- **One constructor for compound terms.** `term` (and `qterm`) build
  every compound shape — head constraint occurrence, body goal,
  function call, data-constructor term. Heads in `<=>` / `==>` accept
  `[Term]` and the DSL coerces each compound to a `Constraint`
  internally; a bare variable in a head position is rejected with
  `YCHR.DSL: term is not a valid constraint occurrence` (the
  type-system mirror of the parser's `MalformedConstraint`).
- **`exporting` switches to an explicit export list.** A module without
  any `exporting` call (the default after `module'`) exports everything;
  calling `exporting [...]` switches it to an explicit list.
- **Append, not replace.** All the module modifiers append. Calling
  `\`declaring\` xs` twice is the same as calling it once with the
  concatenation.
- **Default host calls.** `runDSL` uses the same registry as the CLI:
  arithmetic, comparisons, `print`, and meta primitives like
  `copy_term/2`. If your program needs more, use
  `runDSLWithHostCallRegistry`.
- **Live, runnable examples.** Every code snippet on this page is taken
  from `test/YCHR/DSLTest.hs` (the `endToEnd` test group). Running
  `cabal test ychr-tests --test-options='-p endToEnd'` exercises them.
