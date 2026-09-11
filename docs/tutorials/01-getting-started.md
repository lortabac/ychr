# Getting Started

YCHR compiles **Constraint Handling Rules (CHR)**: rules that rewrite a
*multiset* of facts, the *constraint store*. A rule fires when its
left-hand side is in the store and replaces it with its right-hand side.

## 1. Prerequisites

```sh
ghc --version    # 9.6 or newer
cabal --version  # 3.4 or newer
```

Missing either? Install via [GHCup](https://www.haskell.org/ghcup/).

## 2. Build and install

From the repo root:

```sh
make build
make install
ychr --help
```

`make install` puts `ychr` on your `$PATH` (usually `~/.cabal/bin` or
`~/.local/bin`). `--help` lists the subcommands: `repl`, `run`,
`compile`, `gen-driver`, `check`.

## 3. The example program

[`examples/bakery.chr`](../../examples/bakery.chr):

```prolog
% examples/bakery.chr
:- module(bakery).

:- chr_constraint
    egg/0, glass_of_milk/0, glass_of_flour/0, glass_of_sugar/0,
    bake/0, cake/0.

cake_recipe @
    egg, egg, egg,
    glass_of_milk, glass_of_flour, glass_of_sugar,
    bake
  <=> cake.
```

`<=>` is *simplification*: the matched constraints are removed and the
body takes their place. The store is a multiset, so the head needs
three separate `egg`s, in any order.

## 4. Try it in a live session

```sh
ychr repl examples/bakery.chr
```

`:begin` opens a *live session*: the store persists across inputs and
the prompt changes from `ychr> ` to `ychr live> `. `print_store.`
lists the store.

```ychr-repl
ychr> :begin
ychr live> egg.
ychr live> egg.
ychr live> print_store.
bakery:egg
bakery:egg
ychr live> egg.
ychr live> glass_of_milk.
ychr live> glass_of_flour.
ychr live> glass_of_sugar.
ychr live> print_store.
bakery:egg
bakery:egg
bakery:egg
bakery:glass_of_flour
bakery:glass_of_milk
bakery:glass_of_sugar
ychr live> bake.
ychr live> print_store.
bakery:cake
ychr live> :end
ychr>
```

Nothing fires until `bake` completes the head. `:end` discards the
store. `print_store` comes from the meta library, which the REPL
auto-loads. More in the [REPL reference](../reference/repl.md).

## 5. Without the REPL

`ychr run` runs one goal and exits. The goal must be a single declared
constraint. Nothing is printed on success:

```sh
ychr run -g cake examples/bakery.chr
```

`--show-bindings` prints the goal's variables, one per line:

```sh
ychr run -g 'compute(10, R)' --show-bindings examples/fib.chr
```

```
R = 55
```

`ychr compile examples/bakery.chr` writes the VM dump to `./program.vm`
(`-t scheme` for a Scheme library, `-d DIR` for the directory).
`ychr check` type-checks and is silent on success. `run`, `check`,
`compile` and `gen-driver` take `--Werror`, which exits non-zero on a
warning before the goal runs or the file is written.

## 6. Where to go next

- [CHR primer](02-chr-primer.md) — the three rule kinds and firing order.
- [Your first YCHR program](03-your-first-program.md) — grow the recipe.
