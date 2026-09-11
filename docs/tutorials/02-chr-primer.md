# A CHR Primer

What happened underneath tutorial 01: the store, the three rule kinds,
guards, and firing order.

## 1. The constraint store is a multiset

The only state is the *constraint store*, a multiset of facts called
*constraints*. Duplicates count: the bakery rule needed three `egg`s
and got three.

CHR is forward-chaining and committed-choice. It starts from the
store, fires rules until none applies, and never undoes a firing.
There is no goal-directed search and no backtracking.

A rule has a *head* (what must be in the store), an optional *guard*
(extra tests), and a *body* (what happens when it fires).

## 2. The three rule kinds

**Simplification** (`<=>`) removes the head and adds the body:

```prolog
cake_recipe @
    egg, egg, egg, glass_of_milk, glass_of_flour, glass_of_sugar, bake
  <=> cake.
```

**Propagation** (`==>`) keeps the head and adds the body:

```prolog
transitivity @ leq(X, Y), leq(Y, Z) ==> leq(X, Z).
```

**Simpagation** (`Kept \ Removed <=> Body`) keeps what is left of the
backslash, removes what is right of it, and adds the body. The idiom
for deduplication:

```prolog
idempotence @ leq(X, Y) \ leq(X, Y) <=> true.
```

A body of `true` adds nothing.

## 3. A worked example: the `leq` solver

[`examples/leq.chr`](../../examples/leq.chr) is a partial-order
solver, one rule per axiom:

```prolog
:- module(order, [leq/2]).
:- chr_constraint leq/2.

reflexivity   @ leq(X, X) <=> true.
antisymmetry  @ leq(X, Y), leq(Y, X) <=> X = Y.
idempotence   @ leq(X, Y) \ leq(X, Y) <=> true.
transitivity  @ leq(X, Y), leq(Y, Z) ==> leq(X, Z).
```

```sh
ychr repl examples/leq.chr
```

### Transitivity fires

```ychr-repl
ychr> :begin
ychr live> leq(1, 2).
ychr live> print_store.
order:leq(1, 2)
ychr live>
```

No head matches yet.

```ychr-repl
ychr live> leq(2, 3).
ychr live> print_store.
order:leq(1, 2)
order:leq(2, 3)
order:leq(1, 3)
ychr live>
```

Transitivity added `leq(1, 3)`; both originals stay.

### Idempotence keeps the store small

```ychr-repl
ychr live> leq(1, 2).
ychr live> print_store.
order:leq(1, 2)
order:leq(2, 3)
order:leq(1, 3)
ychr live>
```

The duplicate matched the removed half of `idempotence` and is gone.

```ychr-repl
ychr live> :end
ychr>
```

### Reflexivity collapses trivial constraints

```ychr-repl
ychr> :begin
ychr live> leq(5, 5).
ychr live> print_store.
ychr live> :end
ychr>
```

Empty store: `leq(X, X) <=> true` removed it on arrival.

### Antisymmetry forces unification

Post both constraints in one goal so they share `X` and `Y`:

```ychr-repl
ychr> :begin
ychr live> leq(X, Y), leq(Y, X).
X = Y,
Y = X.
ychr live> print_store.
ychr live> :end
ychr>
```

The body `X = Y` is a unification, not a constraint, so the store is
empty; the REPL reports that the two variables now alias each other.

Each input line is a separate goal with its own variables, as with
`ychr run -g`. `leq(X, Y).` then `leq(Y, X).` on two lines are four
different variables and antisymmetry would not match. The store
persists across lines; variables do not.

## 4. Guards

`Head <=> Guard | Body`: the guard must hold for the rule to fire.
[`examples/clamp.chr`](../../examples/clamp.chr) has two rules with
the same head and different guards:

```prolog
:- module(clamp, [clamp/3]).
:- chr_constraint clamp/3.

low  @ clamp(X, Lo, R) <=> X < Lo  | R = Lo.
high @ clamp(X, Lo, R) <=> X >= Lo | R = X.
```

```sh
ychr run -g 'clamp(3, 5, R)' --show-bindings examples/clamp.chr
```

```
R = 5
```

```sh
ychr run -g 'clamp(7, 5, R)' --show-bindings examples/clamp.chr
```

```
R = 7
```

Guards are pure tests — comparisons, host calls — and never bind
variables. That is the body's job.

| Position | Operator | Effect |
|----------|----------|--------|
| Guard | `==` | Equality test. False for two unbound variables. |
| Body | `=` | Unification. May bind variables. |

This is why antisymmetry's body uses `=`: `X == Y` on two distinct
unbound variables is false.

## 5. Firing order and propagation history

Rules are tried in source order; the first one that matches fires.
Tutorial 03 shows two overlapping recipes competing.

A propagation rule never fires twice on the same combination of head
constraint *identities*. Without this, `transitivity` would re-derive
`leq(1, 3)` from `leq(1, 2)` and `leq(2, 3)` forever. The key is
identity, not value: two equal constraints created at different times
each get their own firing.

The full story is the refined operational semantics, ωr: Duck, Stuckey,
García de la Banda, Holzbaur, *The refined operational semantics of
Constraint Handling Rules*, ICLP 2004.

## 6. Where to go next

- [Your first YCHR program](03-your-first-program.md) — build a small
  program from scratch.
- [Language reference](../reference/language.md) — the precise spec.
