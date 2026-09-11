# Your First YCHR Program

Start from a blank `recipes.chr` and grow the bakery program from
[Getting started](01-getting-started.md) into a small recipe book.

## 1. The first recipe

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

`ychr repl recipes.chr`, then add the ingredients as in tutorial 01.

## 2. A second recipe and rule selection

Append a rule whose head overlaps the first:

```prolog
:- chr_constraint butter/0, cookies/0.

cookies_recipe @
    egg, butter,
    glass_of_flour, glass_of_sugar,
    bake
  <=> cookies.
```

(Declaring `butter/0` and `cookies/0` inline is fine; merge them into
the top declaration when you tidy up.) Reload with `:recompile`.

Cookies alone:

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

Now stock enough for either recipe, with one `bake`:

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

Rules are tried in source order. `bake` completes both heads; the cake
rule comes first, fires, and consumes the `bake`, so cookies can no
longer fire and `butter` is left over.

## 3. Propagation: announce the bake

`==>` adds the body and keeps the head. Append:

```prolog
:- chr_constraint serving_ready/0.

serve @ cake ==> serving_ready.
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
recipes:cake
recipes:serving_ready
ychr live> :end
ychr>
```

The [propagation
history](02-chr-primer.md#5-firing-order-and-propagation-history)
stops `serve` firing twice on one `cake`. A second `cake` is a new
identity and gets its own `serving_ready`:

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

## 4. Where to go next

- [Functions, types, and lambdas](04-functions-and-types.md).
- [REPL reference](../reference/repl.md) — `:recompile`, meta-commands,
  live sessions.
