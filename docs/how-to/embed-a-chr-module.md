# How to embed a CHR module in a Haskell program

> **Goal:** compile a `.chr` module once inside a Haskell program, then
> feed it Haskell values and decode its answers back. The whole
> compile-and-query surface is available from a single `import YCHR` (the
> umbrella entry point); the value bridge itself is documented in
> [`YCHR.Convert`](../reference/convert.md).

The worked example is a Curry-style simply-typed lambda-calculus **type
inferencer** written in CHR. Type inference is constraint solving, so the
whole checker is a handful of simplification rules. The complete sources
are in [`examples/stlc/`](../../examples/stlc/).

With no arguments it is a small type-inference REPL — each line is parsed
(a tiny `parsec` grammar in [`Parser.hs`](../../examples/stlc/Parser.hs)),
type-checked by the CHR module, and its inferred type printed:

```
$ cabal run stlc-typechecker
stlc> \x. x + 1
int -> int
stlc> \f. \x. f (f x)
(a -> a) -> a -> a
stlc> let f = \x. x + 1 in f 5
int
stlc> 1 2
TYPE ERROR: cannot unify int with (int -> _)
```

`--demo` prints a fixed table instead — a good self-check:

```sh
cabal run stlc-typechecker -- --demo
```

```
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

The rest of this guide is about the embedding — parsing is just the front
end; each REPL line becomes one `runQueryCompiled` call (step 4).

## 1. The CHR module

[`examples/stlc/stlc.chr`](../../examples/stlc/stlc.chr) exports a single
entry constraint, `typecheck/2`. It infers the type of a lambda term by
threading a fresh logical variable through the term and unifying type
structures with a small custom `unify_ty` constraint (a raw `=` failure
would abort the whole run, so type errors are *reported* into an
accumulator instead). A polymorphic result such as `arrow(tvar(0),
tvar(0))` is produced by numbering the residual type variables with
`term_variables` at the very end.

The object language (`var`, `lam`, `app`, `lit_int`, `add`) is
**host-supplied data**, matched structurally in rule heads. It is left
undeclared rather than given a `:- chr_type`, because a declared
constructor is module-qualified and would not match the bare functors the
host builds. (`ychr check` notes each as an undeclared constructor; that
is expected here.)

## 2. Encode the input with `ToTerm`

Model the object language as an ordinary Haskell type and hand-write
`ToTerm` — one `compound` per constructor:

```haskell
data Expr = Var Text | Lam Text Expr | App Expr Expr | IntLit Integer | Add Expr Expr

instance ToTerm Expr where
  toTerm (Var x)    = compound "var" [toTerm x]
  toTerm (Lam x b)  = compound "lam" [toTerm x, toTerm b]
  toTerm (App f a)  = compound "app" [toTerm f, toTerm a]
  toTerm (IntLit n) = compound "lit_int" [toTerm n]
  toTerm (Add a b)  = compound "add" [toTerm a, toTerm b]
```

The goal wraps the encoded term in `quote/1` — that is what `quote` does —
so it is passed as data. Without the quote, the argument would be
*evaluated*, and `var("x")` in particular would call the prelude's `var/1`
predicate instead of naming a variable node (see
[the language reference](../reference/language.md) on the `quote/1` quoting
form):

```haskell
typecheckGoal :: Expr -> Term
typecheckGoal e = compound "typecheck" [quote e, VarTerm "Result"]
```

`quote` accepts any `ToTerm` value, so the `toTerm e` call is implicit.

## 3. Decode the result with `FromTerm`

The inferencer answers with `ok(Type)` or `type_error(Errors)`. `decodeSum`
dispatches on the functor's local name, so the module-qualified `stlc:arrow`
that comes back still decodes:

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

[`Main.hs`](../../examples/stlc/Main.hs) embeds the `.chr` source at build
time (a Template Haskell splice, so the binary is self-contained), compiles
it once into a `CompiledProgram`, and drives it with `runQueryCompiled` —
one independent run per demo term:

```haskell
cp <- case compileModules True [(stlcPath, embeddedSource)] of
        Right (cp, _warnings) -> pure cp
        Left err              -> fail (displayError err)

result <- runQueryCompiled cp (typecheckGoal e) "Result"
  :: IO (Either ConvertError TCResult)
```

Everything above — `compileModules`, `CompiledProgram`, `runQueryCompiled`,
`ToTerm`/`FromTerm`, and the `compound`/`decodeSum`/`argAt` combinators —
comes from the single umbrella import:

```haskell
import YCHR
```

`runQueryCompiled` and its variants are documented in the
[conversion reference](../reference/convert.md#reusing-a-compiled-program).
For a `.chr` file on disk (rather than an embedded splice), swap
`compileModules` for `compileFiles` (also re-exported by `YCHR`).
