# Getting Started

> **Audience:** anyone, regardless of CHR/Prolog background.
> **You will:** install YCHR, load a small program, and watch a CHR
> rule fire as you add constraints to the store.

YCHR is a compiler for **Constraint Handling Rules (CHR)** — a small
rule-based language whose programs rewrite a *multiset* of facts (the
*constraint store*). A rule matches when its left-hand side is present
in the store, and replaces those facts with its right-hand side. The
example below has one rule; you'll add facts one at a time and watch
the rule fire.

## 1. Prerequisites

YCHR needs a recent GHC and Cabal. Check what you have:

```sh
ghc --version    # 9.6 or newer
cabal --version  # 3.4 or newer
```

If either is missing, install via [GHCup](https://www.haskell.org/ghcup/).

## 2. Build and install

From the repo root:

```sh
make build
make install
```

This places the `ychr` binary on your `$PATH` (per Cabal's install
location — usually `~/.cabal/bin` or `~/.local/bin`).

Smoke-check the installation:

```sh
ychr --help
```

You should see the available subcommands (`repl`, `run`, `compile`,
`gen-driver`, `check`).

## 3. Meet the example program

We'll use a toy CHR program from this repo: a cake recipe.

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

A single rule says: when the constraint store contains *three* eggs,
one each of milk, flour, sugar, and a `bake` trigger, replace them
with `cake`. The `<=>` operator is *simplification*: it removes the
matched constraints and adds the body in their place.

Note that the head requires *three* `egg` constraints. CHR matches
against a *multiset*: every head constraint must be present
simultaneously, in any order, but with the right multiplicity.

## 4. Try it in a live session

Open the REPL on this file:

```sh
ychr repl examples/bakery.chr
```

The prompt is `ychr> `. Enter a *live session* with `:begin` — this
gives you a persistent constraint store that survives across inputs
(outside live sessions each query starts fresh). The prompt switches
to `ychr live> `.

Add ingredients one at a time and use `print_store.` to inspect the
store along the way:

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

Each `egg.` and each glass added one constraint to the store. After
the first six ingredients nothing had fired yet — `bake` was still
missing. Posting `bake.` completed the rule's left-hand side, so all
seven head constraints were removed at once and `cake` took their
place. The `print_store.` that follows shows the store after the
firing.

Order of insertion did not matter: the rule would have fired the same
way with the eggs added last. And because the store is a multiset, the
three `egg` constraints sat in it side by side until the rule consumed
all three together.

Two REPL details worth knowing. `print_store.` comes from the meta
library, which the REPL auto-loads — no `:- use_module` needed; it
prints every alive constraint, qualified by module. And `:end`
discards the live store, so the next query starts from an empty one.

## 5. Where to go next

- New to CHR? Read the [CHR primer](02-chr-primer.md) for the
  underlying ideas before going further.
- Already comfortable with CHR or Prolog? Jump to
  [Your first YCHR program](03-your-first-program.md), where we
  build the recipe (and a few more rules) from scratch.
- For day-to-day reference: the [CLI](../reference/cli.md) and
  [REPL](../reference/repl.md) pages.
