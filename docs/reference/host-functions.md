# Host-Function Registration Reference

> **Audience.** Haskell developers embedding YCHR who want a `host:f(...)`
> call in a CHR program to run their own Haskell code.
>
> **You will** learn how to lift ordinary Haskell functions into the
> host-call registry with the `hostFn*` adapters, assemble a registry, and
> run queries against it.
>
> **Skip if** the built-in host functions (arithmetic, comparisons, string
> and term operations — see the [prelude reference](prelude.md)) already
> cover your program.

A `host:f(args)` call in a CHR program invokes a *host-language* function
rather than a CHR rule or a user-defined function. Every such call is
resolved at run time against a **`HostCallRegistry`**. The prelude's
arithmetic and comparison operators are thin wrappers over registered
host functions (`X + Y -> host:'+'(X, Y).`), and you can register your
own.

The whole surface below is re-exported from the umbrella module `YCHR`, so
`import YCHR` is all you need; `YCHR.Convert` is the module of record.

## The adapters

Each adapter lifts a Haskell function into a `HostCallFn`, marshalling
arguments and the result through the same [`ToTerm` / `FromTerm`](convert.md)
classes used for goals and results. You never touch the runtime value
representation for the common case.

| Adapter | Lifts | Notes |
|---|---|---|
| `hostFn1`, `hostFn2`, `hostFn3` | `a -> b -> r` (pure) | argument types are `FromTerm`, result is `ToTerm` |
| `hostFn1M`, `hostFn2M`, `hostFn3M` | `a -> b -> Chr r` | body runs in `Chr`: I/O (via `liftIO`), variable dereferencing, store access |
| `hostFn0M` | `Chr r` | nullary effectful (a clock, a fresh value); there is no pure `hostFn0` because that is just a constant |
| `hostFnN` | `[Term] -> Either ConvertError Term` | variable arity, still `Term`-marshalled |
| `hostFnValues` | `[Value] -> Chr Value` | raw escape hatch, no marshalling (see [below](#the-raw-escape-hatch)) |

```haskell
hostFn2 ((+) :: Int -> Int -> Int)   -- Int arguments, Int result
hostFn1 Data.Text.toUpper            -- Text -> Text
hostFn0M (liftIO getSomething)       -- nullary, effectful
```

The call-site name is chosen at registration, below.

## Assembling and running

`hostFunctions` builds a registry from named entries; the name is the bare
functor at the call site. `withDefaultHostFunctions` unions your entries
over the full default registry (base builtins plus the meta operations),
so a program can call both — on a name clash, your entry wins.

```haskell
registry :: HostCallRegistry
registry = withDefaultHostFunctions
  [ ("my_add",  hostFn2 ((+) :: Int -> Int -> Int))
  , ("shout",   hostFn1 Data.Text.toUpper)
  , ("sum_all", hostFnN sumTerms)                 -- variadic
  ]
  where
    sumTerms ts = toTerm . sum <$> (traverse fromTerm ts :: Either ConvertError [Int])
```

Run with `runQueryCompiledWithHostCallRegistry` — the registry-taking
counterpart of `runQueryCompiledWith`:

```haskell
runQueryCompiledWithHostCallRegistry
  :: HostCallRegistry -> CompiledProgram -> Term
  -> (Map Text Term -> Either ConvertError a) -> IO (Either ConvertError a)
```

For a complete compilable program built around this registry, see the
[how-to guide](../how-to/call-host-functions.md).

(For [DSL](dsl.md)-built `[Module]` values there is also a
compile-and-run-in-one `runQueryWithHostCallRegistry`; it lives in
`YCHR.Convert` and is *not* re-exported from `YCHR`.)

Compilation does not resolve `host:` names, so an unknown host function is a
run-time error, not a compile error — the registry is consulted only when
the call fires.

## Marshalling and errors

Arguments are decoded with `fromTerm` and the result encoded with `toTerm`.
The bridge **recursively dereferences**, so a logical variable bound inside
a compound argument is resolved before decoding:

```haskell
-- compute_nested(R) <=> X = 5, R is host:echo(wrap(X, 2)).
-- echo = hostFn1 (id :: Term -> Term)
-- R is bound to  wrap(5, 2)  — the nested X is resolved to 5, not left symbolic.
```

Marshalling failures surface as a **runtime error** (the same mechanism as
a unification failure), because a host call fires deep inside solving:

| Situation | Result |
|---|---|
| Wrong number of arguments | runtime error: `host call: expected N argument(s), got M` |
| An argument the type cannot decode | runtime error: `host call: TypeMismatch …` |
| An argument still unbound at call time | runtime error: `host call: UnboundValue …` (instantiation kind) |

A result term need not be ground: each distinct `VarTerm` name in it
becomes a fresh unbound logical variable.

> **`UnboundValue` in a rule guard.** The `UnboundValue` failure is
> classified as an *instantiation* failure, so a host call in a rule
> guard that cannot decode an unbound argument makes the guard
> evaluate to false rather than aborting the query; binding the
> variable reactivates the constraint and the rule is retried. See
> [Soft guard failure](language.md#soft-guard-failure). The other two
> rows are ordinary failures and stay hard errors everywhere. A host
> function that wants an argument to stay symbolic should decode it as
> `Term`, which accepts an unbound variable instead of reporting
> `UnboundValue`.

> **Booleans.** A boolean marshals to/from the atom `true` / `false`
> (matching how a source-level `true` compiles), so a `hostFn2 (… :: … -> Bool)`
> composes with guards written against those atoms.

## The raw escape hatch

For a host function that needs the runtime representation directly — bulk
`Value` inspection, selective deep dereferencing, or anything the `Term`
bridge does not express — use `hostFnValues`, which is the `HostCallFn`
constructor under a descriptive name:

```haskell
hostFnValues :: ([Value] -> Chr Value) -> HostCallFn
```

Arguments arrive **top-level dereferenced only** (a variable nested inside a
compound is *not* chased — use `deref`, re-exported from `YCHR`, yourself).
This is the same
low-level shape the built-in host functions are written in; reach for it
only when the marshalled adapters do not fit.

To compare two `Value`s, use `equal` (also re-exported from `YCHR`),
which implements CHR's `==`. There is deliberately no `Eq Value`
instance: a derived one would compare logical variables by reference
and disagree with `==` on unbound variables.

## See also

- [How to call host-language functions](../how-to/call-host-functions.md) —
  task-oriented walkthrough.
- [Haskell conversion reference](convert.md) — the `ToTerm` / `FromTerm`
  classes the adapters build on.
- [Prelude reference](prelude.md) — the built-in host functions.
