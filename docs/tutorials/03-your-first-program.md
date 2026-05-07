# Your First YCHR Program

> **Audience:** comfortable with CHR or Prolog basics. If "rule head"
> and "constraint store" don't ring a bell, read the
> [CHR primer](02-chr-primer.md) first.
> **You will:** write a CHR program that grows from one rule to three,
> meeting all the rule kinds along the way.

The bakery example you ran in the [previous tutorial](01-getting-started.md)
had a single simplification rule. Here we'll start from a blank file
and grow it into a slightly richer program — a tiny recipe book — to
see how multiple rules interact.

Create a new file `recipes.chr` next to where you'll run YCHR.

## 1. The first recipe

Open `recipes.chr` and write:

```chr
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

This is the same program as the bakery from the previous tutorial. The
`<=>` operator is **simplification**: it removes every constraint in
the head and adds the body in their place. With this rule alone, three
eggs, three glasses, and a `bake` collapse into a `cake`.

Load it and confirm:

```sh
ychr repl recipes.chr
```

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
recipes:cake()
ychr live> :end
ychr>
```

## 2. A second recipe and rule selection

Let's add a second simplification, with a head that *partly overlaps*
the first. Edit `recipes.chr` and append:

```chr
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
store. The interesting question is: what happens when *both* heads are
satisfiable from the same store?

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
recipes:cookies()
ychr live> :end
ychr>
```

Now stock the pantry with enough for **either** recipe — three eggs,
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
recipes:butter()
recipes:cake()
ychr live> :end
ychr>
```

The cake rule won. Why? CHR uses **committed-choice** semantics: when
`bake` becomes the active constraint, the runtime tries the rules in
source order, finds the cake rule's head fully present, fires it, and
commits — consuming the `bake`. With `bake` gone, the cookies rule
can no longer fire. The leftover `butter` stays in the store.

Source order matters when heads overlap.

## 3. Propagation: announce the bake

The two recipes consume their inputs. Sometimes you want a rule to
*derive a new fact without removing the existing ones* — that is what
propagation rules do. They use `==>` instead of `<=>`.

Append:

```chr
:- chr_constraint serving_ready/0.

serve @ cake ==> serving_ready.
```

This says: whenever `cake` is in the store, also place
`serving_ready` in the store. The `cake` itself is **kept**.

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
recipes:cake()
recipes:serving_ready()
ychr live> :end
ychr>
```

`cake` survived, and `serving_ready` was added.

A subtlety: propagation rules carry a **propagation history** that
prevents the same combination of head constraints from firing twice.
If `serve` fired every time the runtime examined `cake`, you'd get an
infinite loop. The history records *"serve fired with this particular
cake"* and skips re-fires for the same combination. Different `cake`
constraints (i.e. those produced by separate rule firings) have
distinct identities, so each gets its own `serving_ready`:

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
recipes:cake()
recipes:cake()
recipes:serving_ready()
recipes:serving_ready()
ychr live> :end
ychr>
```

Two cakes, two notifications.

## 4. What you've built

Three rules covering two of the four CHR rule kinds:

| Rule | Operator | Removes head? | Adds body? |
|------|----------|---------------|------------|
| `cake_recipe` | `<=>` (simplification) | yes | yes |
| `cookies_recipe` | `<=>` (simplification) | yes | yes |
| `serve` | `==>` (propagation) | no | yes |

The two missing pieces — **simpagation** (`Kept \ Removed <=> ...`,
which keeps some head constraints while removing others) and
**guards** (boolean tests that gate a rule firing) — show up next.

## 5. Where to go next

- [Functions, types, and lambdas](04-functions-and-types.md) — adding
  user-defined functions and type annotations.
- [How-to: use the REPL](../how-to/use-the-repl.md) — `:recompile`,
  meta-commands, and other live-session conveniences.
- [Language reference](../reference/language.md) — the formal feature
  list, including simpagation and guard semantics.
