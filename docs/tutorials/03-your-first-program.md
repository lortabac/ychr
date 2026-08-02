# Your First YCHR Program

> **Audience:** comfortable with CHR or Prolog basics. If "rule head"
> and "constraint store" don't ring a bell, read the
> [CHR primer](02-chr-primer.md) first.
> **You will:** write a CHR program that grows from one rule to three,
> seeing how simplification and propagation rules interact.

The bakery example you ran in
[Getting started](01-getting-started.md) had a single simplification
rule. Here we'll start from a blank file
and grow it into a slightly richer program — a tiny recipe book — to
see how multiple rules interact.

Create a new file `recipes.chr` next to where you'll run YCHR.

## 1. The first recipe

Open `recipes.chr` and write:

```prolog
:- module(recipes).

:- chr_constraint
    egg/0, glass_of_milk/0, glass_of_flour/0, glass_of_sugar/0,
    bake/0, cake/0.

cake_recipe @
    egg, egg, egg,
    glass_of_milk, glass_of_flour, glass_of_sugar,
    bake
  <=> cake.
```

This is the bakery program from
[Getting started](01-getting-started.md) under a new name: one
simplification rule that collapses three eggs, the three glasses, and
a `bake` into a `cake`. Load it with `ychr repl recipes.chr` and
tell it the ingredients to confirm it still works as before.

## 2. A second recipe and rule selection

Add a second simplification, with a head that *partly overlaps*
the first. Edit `recipes.chr` and append:

```prolog
:- chr_constraint butter/0, cookies/0.

cookies_recipe @
    egg, butter,
    glass_of_flour, glass_of_sugar,
    bake
  <=> cookies.
```

(For brevity we add `butter/0` and `cookies/0` as new constraints
inline; in a finished program you'd merge them into the top
declaration.)

Reload from the REPL with `:recompile` (or restart it). The `cake`
and `cookies` rules can both fire when their heads are present in the
store. What happens when *both* heads are satisfiable from the same
store?

First, give it a clean cookies-only run — only the cookies rule's
head is fully present:

```ychr-repl
ychr> :begin
ychr live> egg.
ychr live> butter.
ychr live> glass_of_flour.
ychr live> glass_of_sugar.
ychr live> bake.
ychr live> print_store.
recipes:cookies
ychr live> :end
ychr>
```

Now stock the pantry with enough for *either* recipe — three eggs,
butter, milk, flour, sugar, and a single `bake`:

```ychr-repl
ychr> :begin
ychr live> egg.
ychr live> egg.
ychr live> egg.
ychr live> butter.
ychr live> glass_of_milk.
ychr live> glass_of_flour.
ychr live> glass_of_sugar.
ychr live> bake.
ychr live> print_store.
recipes:butter
recipes:cake
ychr live> :end
ychr>
```

The cake rule won, because CHR commits to the first rule it can fire.
When `bake` becomes the active constraint, the runtime tries the rules
in source order, finds the cake rule's head fully present, fires it,
and commits — consuming the `bake`. With `bake` gone, the cookies rule
can no longer fire, and the leftover `butter` stays in the store.

Source order matters when heads overlap.

## 3. Propagation: announce the bake

The two recipes consume their inputs. Sometimes you want a rule to
*derive a new fact without removing the existing ones* — that is what
propagation rules do. They use `==>` instead of `<=>`.

Append:

```prolog
:- chr_constraint serving_ready/0.

serve @ cake ==> serving_ready.
```

This says: whenever `cake` is in the store, also place
`serving_ready` in the store. The `cake` itself is kept.

Reload and bake:

```ychr-repl
ychr> :begin
ychr live> egg.
ychr live> egg.
ychr live> egg.
ychr live> glass_of_milk.
ychr live> glass_of_flour.
ychr live> glass_of_sugar.
ychr live> bake.
ychr live> print_store.
recipes:cake
recipes:serving_ready
ychr live> :end
ychr>
```

`cake` survived, and `serving_ready` was added.

A subtlety: the *propagation history* (see the
[primer](02-chr-primer.md#5-firing-order-and-propagation-history))
keeps `serve` from firing twice on the same `cake` — otherwise this
rule would loop forever. Different `cake` constraints have distinct
identities, so each gets its own `serving_ready`:

```ychr-repl
ychr> :begin
ychr live> egg.
ychr live> egg.
ychr live> egg.
ychr live> glass_of_milk.
ychr live> glass_of_flour.
ychr live> glass_of_sugar.
ychr live> bake.
ychr live> egg.
ychr live> egg.
ychr live> egg.
ychr live> glass_of_milk.
ychr live> glass_of_flour.
ychr live> glass_of_sugar.
ychr live> bake.
ychr live> print_store.
recipes:cake
recipes:cake
recipes:serving_ready
recipes:serving_ready
ychr live> :end
ychr>
```

Two cakes, two notifications.

## 4. Where to go next

This program used simplification and propagation; the third rule kind,
*simpagation* (`Kept \ Removed <=> ...`), and rule *guards* are
covered in the [primer](02-chr-primer.md) and the
[language reference](../reference/language.md).

- [Functions, types, and lambdas](04-functions-and-types.md) — adding
  user-defined functions and type annotations.
- [How-to: use the REPL](../how-to/use-the-repl.md) — `:recompile`,
  meta-commands, and other live-session conveniences.
- [Language reference](../reference/language.md) — the formal feature
  list, including simpagation and guard semantics.
