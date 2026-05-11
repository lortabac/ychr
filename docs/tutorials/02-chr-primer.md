# A CHR Primer

> **Audience:** readers new to Constraint Handling Rules.
> **You will:** learn what CHR is, meet the three rule kinds, watch a
> small program rewrite the constraint store, and understand guards
> and firing order.
> **Skip if:** you already know CHR — go to
> [Your first YCHR program](03-your-first-program.md).

Tutorial 01 showed a single rule firing. This one explains what was
happening underneath: what the constraint store really is, what kinds
of rules CHR offers, and the order in which the runtime tries to fire
them.

## 1. The constraint store is a multiset

A CHR program's only state is the **constraint store**: a *multiset* of
facts (called *constraints*). "Multiset" means duplicates count — two
copies of `egg` are two distinct items in the store, not one. The
bakery rule from tutorial 01 needed three `egg` constraints; if the
store had been a set, three `egg.` inputs would have collapsed to one
and the rule could never have fired.

CHR is **forward-chaining**: the runtime starts from the constraints
you put in the store and pushes the store forward by firing rules. It
is not Prolog. There is no goal-directed search, no backtracking. Rule
choice is **committed-choice**: once a rule fires, the runtime does not
later "undo" that firing to try another.

A program is a list of **rules**. Each rule has a *head* (what must be
in the store), an optional *guard* (extra conditions), and a *body*
(what to do when the rule fires).

## 2. The three rule kinds

CHR has three kinds of rule, distinguished by what they do with the
head constraints when they fire.

**Simplification** (`<=>`) removes the head and replaces it with the
body. The bakery rule from tutorial 01 was a simplification:

```chr
cake_recipe @
    egg, egg, egg, glass_of_milk, glass_of_flour, glass_of_sugar, bake
  <=> cake.
```

Seven head constraints are consumed; one body constraint takes their
place.

**Propagation** (`==>`) keeps the head and *adds* the body to the
store. Nothing is removed.

```chr
transitivity @ leq(X, Y), leq(Y, Z) ==> leq(X, Z).
```

If `leq(1, 2)` and `leq(2, 3)` are both in the store, this rule adds
`leq(1, 3)` — without removing the originals.

**Simpagation** (`Kept \ Removed <=> Body`) is a mix: the constraints
to the *left* of the backslash are kept, the ones to the *right* are
removed, and the body is added. It is the idiomatic way to deduplicate:

```chr
idempotence @ leq(X, Y) \ leq(X, Y) <=> true.
```

Read it as "given two structurally identical `leq` constraints, keep
the left one and remove the right one." The body is `true` — nothing is
added.

## 3. A worked example: the `leq` solver

Put all three rule kinds together and you get one of the most
well-known CHR programs: a partial-order solver for `leq` (less-or-equal).
It lives at [`examples/leq.chr`](../../examples/leq.chr):

```chr
:- module(order, [leq/2]).
:- chr_constraint leq/2.

reflexivity   @ leq(X, X) <=> true.
antisymmetry  @ leq(X, Y), leq(Y, X) <=> X = Y.
idempotence   @ leq(X, Y) \ leq(X, Y) <=> true.
transitivity  @ leq(X, Y), leq(Y, Z) ==> leq(X, Z).
```

Four rules, one for each property of a partial order. Let's load it
and watch the store evolve.

```sh
ychr repl examples/leq.chr
```

### Transitivity fires

Start a live session and post `leq(1, 2)`:

```ychr-repl
ychr> :begin
ychr live> leq(1, 2).
ychr live> print_store.
order:leq(1, 2)
ychr live>
```

One constraint sits in the store, none of the rules' heads are
satisfied, nothing fires.

Now add `leq(2, 3)`:

```ychr-repl
ychr live> leq(2, 3).
ychr live> print_store.
order:leq(1, 2)
order:leq(2, 3)
order:leq(1, 3)
ychr live>
```

Transitivity fired. The head `leq(X, Y), leq(Y, Z)` matched with
`X = 1, Y = 2, Z = 3`, and the body `leq(X, Z)` — i.e. `leq(1, 3)` —
was added. Both originals stayed, because propagation rules don't
remove their head.

### Idempotence keeps the store small

Post `leq(1, 2)` a second time:

```ychr-repl
ychr live> leq(1, 2).
ychr live> print_store.
order:leq(1, 2)
order:leq(2, 3)
order:leq(1, 3)
ychr live>
```

The store didn't grow. The new `leq(1, 2)` matched the right half of
the idempotence rule (`leq(X, Y) \ leq(X, Y) <=> true.`) and was
silently removed; the older copy survived. End the session:

```ychr-repl
ychr live> :end
ychr>
```

### Reflexivity collapses trivial constraints

In a fresh session, post `leq` with both arguments equal:

```ychr-repl
ychr> :begin
ychr live> leq(5, 5).
ychr live> print_store.
ychr live> :end
ychr>
```

`print_store` produced no output — the store is empty. The
reflexivity rule `leq(X, X) <=> true.` matched and removed the
constraint immediately.

### Antisymmetry forces unification

Antisymmetry says: if `leq(X, Y)` and `leq(Y, X)` both hold, then
`X = Y`. Post them as a single goal so both `X`s refer to the same
variable:

```ychr-repl
ychr> :begin
ychr live> leq(X, Y), leq(Y, X).
X = _,
Y = _.
ychr live> print_store.
ychr live> :end
ychr>
```

The store is empty. Antisymmetry fired, removed both `leq` constraints,
and executed the body `X = Y` — a unification, not a stored constraint,
so nothing is added to the store. The `X = _, Y = _` lines are the
REPL reporting the two variables: they are now bound to *each other*,
but neither has a ground value, so both print as the anonymous `_`.

> **Each input is its own goal.** In a live session every input line is
> a separate top-level goal with its own variable scope — the same rule
> as `ychr run -g GOAL`. Posting `leq(X, Y).` and `leq(Y, X).` on two
> lines gives you four different variables, so antisymmetry would not
> match. To share variables, put the constraints on one comma-separated
> line as above. The *store* persists across lines (that's what a live
> session is for); *variables* do not.

## 4. Guards

A head match is not always enough to fire a rule. CHR lets you attach
a **guard** — a boolean test that must hold for the rule to fire. The
syntax is `Head <=> Guard | Body`. The companion file
[`examples/clamp.chr`](../../examples/clamp.chr) shows two rules that
share a head and differ only in their guards:

```chr
:- module(clamp, [clamp/3]).
:- use_module(prelude).
:- chr_constraint clamp/3.

low  @ clamp(X, Lo, R) <=> X < Lo  | R = Lo.
high @ clamp(X, Lo, R) <=> X >= Lo | R = X.
```

Run it once below the floor and once above:

```sh
ychr run -g 'clamp:clamp(3, 5, R)' --show-bindings examples/clamp.chr
```

```
R = 5
```

```sh
ychr run -g 'clamp:clamp(7, 5, R)' --show-bindings examples/clamp.chr
```

```
R = 7
```

For each input, only one rule's guard passes; the other rule's match
silently fails.

**Guards are pure tests.** They use comparisons like `<`, `>=`, `==`
and host calls. They **must not bind variables** — that is what the
body is for. The guard test for equality is `==` (structural equality,
no mutation); the body uses `=` (unification, may bind).

| Position | Operator | Effect |
|----------|----------|--------|
| Guard | `==` | Pure equality test. Returns false for two unbound variables. |
| Body | `=` | Unification. May bind variables. |

This is why the antisymmetry rule's body uses `=` and a guard expression
on the same arguments would not work — `X == Y` for two distinct
unbound variables is false.

## 5. Firing order and propagation history

CHR's evaluation strategy is the **refined operational semantics** (ωr).
Two facts about it cover almost everything you'll need day to day:

- **Rules are tried in source order.** When several rules could match,
  the one that appears first in the file fires. Tutorial 03 shows this
  in action when two recipes overlap.
- **Propagation rules carry a history.** A propagation rule never
  fires twice on the same combination of head constraint *identities*.
  Without this, `transitivity` would loop on `leq(1, 2)` and
  `leq(2, 3)` — both are kept in the store, both still match the head,
  so the runtime would keep re-deriving `leq(1, 3)` indefinitely. The
  history records "this rule already fired with these particular
  constraint identifiers" and skips re-fires for the same combination.
  Note that this is keyed by *identifiers*, not values — two structurally
  identical constraints created at different times have distinct
  identities, so each gets its own chance to fire.

That is enough to follow most CHR programs. The
[refined operational semantics](../explanation/operational-semantics.md)
page goes deeper when you want it.

## 6. Where to go next

- [Your first YCHR program](03-your-first-program.md) — build a small
  program from scratch.
- [Functions, types, and lambdas](04-functions-and-types.md) — add
  computation on top of CHR's relational core.
- [Language reference](../reference/language.md) — the precise spec
  for everything introduced here.
