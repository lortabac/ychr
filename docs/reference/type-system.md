# YCHR Type System Specification

The YCHR static type system is a gradual, consistency-based type
checker for CHR programs. Types are erased at runtime; the checker
produces errors without transforming the program.


## Overview

The type system catches inconsistencies statically and stays optional:
programs without type annotations are accepted. One type language
covers constraints and functions. The checker takes a
`Desugared.Program` and produces errors and warnings; errors stop
compilation, and `--Werror` promotes warnings to errors.


## Types

The type language:

```
τ  ::=  int                          -- integers
     |  float                        -- floating-point numbers
     |  string                       -- strings
     |  any                          -- the dynamic type
     |  α                            -- type variable
     |  C(τ₁, ..., τₙ)              -- algebraic or opaque type constructor
     |  fun(τ₁, ..., τₙ) -> τᵣ      -- function type
```

### Built-in types

- **`int`** — arbitrary-precision integer values. Arithmetic never
  overflows; the host runtime carries integers as bignums.
- **`float`** — floating-point values.
- **`string`** — string values.
- **`any`** — the dynamic type. Consistent with every other type; the
  escape hatch for gradually typed code.

`bool` is not built-in: the prelude declares it as the algebraic type
`bool ---> true ; false`.

### Algebraic types

User-defined types are declared with `:- chr_type` directives:

```prolog
:- chr_type option(A) ---> none ; some(A).
:- chr_type list(A)   ---> [] ; [A|list(A)].
:- chr_type color     ---> red ; green ; blue.
```

An algebraic type definition introduces:

- A type constructor name with zero or more type parameters.
- One or more data constructors, each with zero or more typed fields.

### Opaque types

An *opaque type* is a nominal type whose values are introduced and
eliminated only by (host-backed) functions. It is declared with
`:- opaque_type` and has **no data constructors**:

```prolog
:- opaque_type set(X).
:- opaque_type handle.
```

The definition introduces a type constructor name with zero or more
type parameters and nothing else. With no data constructors, an opaque
value cannot be built or pattern-matched structurally in CHR source;
it is produced only as a function's declared return and consumed only
by passing it to a function whose parameter has that type:

```prolog
:- module(foo, [type(set/1)]).

:- opaque_type set(X).

:- function set_new() -> set(X).
:- function set_member(set(X), X) -> bool.
set_new() -> host:set_new().
set_member(S, X) -> host:set_member(S, X).
```

Well-formedness of `:- opaque_type T(α₁, ..., αₙ).`:

- The `αᵢ` are distinct type variables.
- *Phantom* parameters are allowed: an opaque type has no fields for a
  parameter to occur in.
- A constructor body (`---> ...`) is a syntax error (`YCHR-15016`):
  opaque types cannot have data constructors.
- `T` must not collide with a base/reserved type name or another
  visible type.

**Consistency (nominal).** An opaque type `T(τ₁, ..., τₙ)` is a type
constructor application, so it obeys the ordinary `[C-Con]`,
`[C-Any-L]`, `[C-Any-R]`, and `[Inconsistency]` rules below: `T` is
consistent only with itself (parameters checked pairwise) and with
`any`, and inconsistent with every other type constructor and every
base or function type. Distinct opaque types never unify, and an
opaque type never unifies with its representation.

**Abstraction.** An opaque type's name `T` is a *type-constructor*
name, not a data constructor — like an algebraic type's name (`list`,
`option`) — and is meaningful only in *type-expression* position
(function and constraint signatures, other type declarations).
`T(...)` in *term* position — `X = set(1)`, or `set(X)` in a guard,
head, or equation pattern — does not build an opaque value: `T` is an
unknown data constructor there, so the term is typed `any` and, like
every unknown constructor, draws an `UndeclaredDataConstructor`
warning (`YCHR-20101`). Opaque values are obtained and consumed by
calling a function declared to return or accept `T(...)`. As with
algebraic types, the soundness of the typed fragment rests on the
gradual guarantee, not a syntactic ban: a forged `set(1)` typed `any`
can still flow into a `set`-typed position, as a nonsensical `list(1)`
can into a `list`-typed one.

**Visibility.** Opaque types obey the module type-export/import rules
([`language.md`](language.md)) and share the type namespace with
algebraic types, so they are exported and imported with the same
`type(T/n)` form; there is no separate opaque-export syntax. Having no
constructors, the `type(T/n, [...])` allowlist form is useless for one
— naming a constructor there is rejected as unknown (`YCHR-20008`).

### Function types

Function types describe first-class callable values (lambdas and
function references):

```
fun(int, int) -> bool end
fun(A) -> A end
```

`fun(τ₁, ..., τₙ) -> τᵣ` is a callable taking `n` arguments of types
`τ₁, ..., τₙ` and returning a `τᵣ`.

In *concrete* syntax a function type is closed by `end` —
`fun(int, int) -> bool end` — mirroring lambda syntax; the `end`
delimits the return type and is not part of the abstract grammar. This
document writes types in abstract syntax (no `end`) except inside
program examples.

### Type variables

Type variables (uppercase identifiers in CHR source) are implicitly
universally quantified over the enclosing declaration (constraint or
function). There is no explicit quantification and no rank-n
polymorphism.

Each use site of a declared constraint or function instantiates its
type variables with fresh flexible unification variables;
implementation sites — a function's own equations, a constraint's
rule-head occurrences — allocate rigid variables instead (§Type
variables and instantiation).


## Defaults

Missing type annotations default to `any`:

- A constraint declared `name/arity` has every argument type `any`.
- A function declared `name/arity` has every argument type and its
  return type `any`.

`:- chr_constraint leq/2` is equivalent to
`:- chr_constraint leq(any, any)`: type checking treats the two forms
identically. The one place an untyped declaration is *not*
interchangeable with its all-`any` form (declaration grouping for
overloaded classes) is in §Signature Overloading.


## Consistency

The type system is based on *consistency checking* in the style of
gradual typing. Two types are consistent (`τ₁ ~ τ₂`) if they could be
the same type up to the presence of `any` — weaker than equality,
since `any` stands in for any type without committing to one.

### Consistency rules

```
                                                    [C-Any-L]
  ────────────
  any ~ τ

                                                    [C-Any-R]
  ────────────
  τ ~ any

                                                    [C-Refl]
  ────────────
  B ~ B                       (B a base type: int, float, string)

  τ₁ ~ σ₁   ...   τₙ ~ σₙ                         [C-Con]
  ────────────────────────────
  C(τ₁,...,τₙ) ~ C(σ₁,...,σₙ)

  τ₁ ~ σ₁   ...   τₙ ~ σₙ   τᵣ ~ σᵣ              [C-Fun]
  ────────────────────────────────────
  fun(τ₁,...,τₙ) -> τᵣ ~ fun(σ₁,...,σₙ) -> σᵣ
```

Any two types with distinct outermost forms — neither being `any` or
a type variable — are **inconsistent**:

```
  C ≠ D                                             [Inconsistency]
  ────────────────────────────
  C(...) ~ D(...)  is an error
```

Here a base type counts as a nullary type constructor, and the
function-type former `fun/n` as a type constructor distinct from every
base type and every other constructor: `int ~ bool`,
`option(int) ~ list(int)`, and `int ~ fun(int) -> int` are all errors.

Type variables are deliberately absent: which types bind them and how
they interact with `any` is defined by the meet table in §Type states.


## Type Propagation and Consistency

The checker infers types for source variables by propagation. Types
flow into variables from declarations (head constraints, function
signatures) and between variables through unification and `is`
expressions; when two types meet, the checker performs a *consistency
check* per the previous section.

### Type states

Every type the checker manipulates is in exactly one of four states:

- **`any`** — the dynamic type. A *variable* is typed `any` only when
  a declaration says so: an `any`-annotated or untyped argument
  position **in a rule head or an equation's parameter list**, or an
  `any`-declared constructor field reached from such a pattern
  (§Sources of Type Information, source 8). An `any` argument position
  at a use site (a body tell or call) is only checked against and
  types nothing — a variable whose only occurrences are use sites
  stays flexible. Certain *expressions* are also typed `any`;
  §Soundness lists every `any`-introduction form.
- **Concrete** — a base type, an algebraic or opaque constructor
  application, or a function type.
- **Flexible** — an unsolved unification variable. Instantiating a
  declared signature at a use site allocates fresh flexible variables
  for its type parameters, and a source variable with no
  declaration-derived type is likewise typed by a fresh flexible. There is no
  separate "unknown" state.
- **Rigid** — a declaration's own type parameter at an implementation
  site: a function's type parameter while its equations are checked,
  or a typed polymorphic constraint's type parameter at a rule-head
  occurrence while that rule is checked (§Rigid and flexible type
  variables) — or a fresh skolem introduced by a `GuardMatch` at a
  rigid scrutinee (§Guard-Derived Type Evidence). It behaves as an
  opaque type constant (a skolem): an arbitrary caller- or
  store-chosen type about which nothing may be assumed beyond what
  guard-derived evidence establishes (§Guard-Derived Type Evidence).

When two types meet — through unification, argument checking, or any
other consistency check:

| Meet | Outcome |
|------|---------|
| flexible α, concrete τ | succeeds; **α := τ** |
| flexible α, flexible β | succeeds; α and β are aliased |
| flexible α, rigid T | succeeds; **α := T** (rigidity travels through the alias) |
| flexible α, `any` | succeeds; α is **not** bound |
| rigid T, rigid T (same) | succeeds |
| rigid T, rigid U (distinct) | error |
| rigid T, concrete τ | error |
| rigid T, `any` | succeeds; nothing binds |
| concrete τ, concrete σ | consistency check per §Consistency |
| `any`, anything | succeeds; nothing binds |

Only *solid* types — concrete types and rigid variables — bind
flexible variables; `any` binds nothing. The principle behind the
table:

> **`any` never binds a type variable and never propagates; it is
> only checked against. A variable's type is `any` only when a
> declaration says so.**

A variable typed by several declaration positions keeps the most
informative source: a concrete or type-parameter source determines the
variable's type and the `any` positions are merely checked; the
variable is typed `any` only when every source is `any`.

This is decided **position by position**, not for the variable as a
whole. Given

```prolog
:- chr_constraint p(list(any)), q(list(int)), s(list(string)).
p(X), q(X) <=> s(X).
```

`X`'s two sources agree on the outer `list` and disagree on its
element: `int` is the more informative, so `X` is `list(int)` and the
body's `s(X)` is an inconsistency. The head `q(X), p(X)` reports the
same error — source order never matters. A position is `any` only when
*every* source leaves it `any`, and then it stays dynamic:
`p(list(any))` alone lets `X` be passed to both a `list(string)` and a
`list(int)` parameter.

The meet table governs every ordinary meet. Rigid variables admit one
exception, defined in §Guard-Derived Type Evidence: a guard whose
operational success entails a typing fact may bind or merge rigid
variables. Nothing — not even evidence — ever narrows `any`.

### The role of `any`

`any` is the escape hatch for gradual typing: consistent with every
other type but inert in propagation — a variable typed `any` carries
no type information between positions, and `any` never overwrites a
type established elsewhere:

- A variable whose declaration positions all use `any` (an argument of
  a constraint declared `foo(any)`, or of an untyped constraint) is
  typed `any`. If it also has a concrete or polymorphic declaration
  source, that source wins and the `any` positions are merely checked
  (§Type states).
- A variable with a known concrete type that meets `any` through
  unification or a consistency check **retains** its concrete type:
  the check succeeds without replacing it.
- When `any` meets a flexible or rigid type variable, the check
  succeeds and the variable is **not** bound, so `any` cannot leak
  through shared type parameters or chains of local variables and mask
  real inconsistencies (§Type variables and instantiation).

No construct replaces `any` with something more precise: `R is e`
checks the RHS's inferred type against an `any`-typed `R` without
refining it, and plain unification (`=`) checks against `any` without
binding anything (§Sources of Type Information §5). Keeping the
invariant unqualified is what lets the order-independence guarantee of
§Type Checking Procedure hold without carve-outs: every source of type
information is part of the solved constraint set, and no directed
narrowing step depends on the order body goals are examined in.

Narrowing `any` would never accept more programs — `any` already
passes every check — only reject programs that run. Static findings
about `any`-typed code (a refinement predicate proving a later use
doomed, say) therefore belong to a planned opt-in warning pass
([roadmap](../roadmap.md)), never to the checker's errors.

### Example: propagation through a shared variable

```prolog
:- chr_constraint foo(int), bar/1.
rule @ foo(X) <=> bar(X).
```

- `X : int` (from `foo(int)` in the head).
- Body `bar(X)`: `X` is `int`, so `bar` is called with an `int`
  argument — the type propagated from head to body through the shared
  `X`.

### Example: `any` stops propagation

```prolog
:- chr_constraint foo(any), bar(int), baz(bool).
foo(X), bar(Y), baz(Z) <=> X = Y, X = Z.
```

- `X : any` (from `foo`), `Y : int` (from `bar`), `Z : bool` (from
  `baz`).
- `X = Y`: `any ~ int` → succeeds. `Y` remains `int`.
- `X = Z`: `any ~ bool` → succeeds. `Z` remains `bool`.

No error: the `any` in `foo` makes both checks involving `X` succeed,
and `Y` and `Z` retain their declared types — `X`'s `any` does not
propagate to them. Had the rule also contained `Y = Z`, the checker
would report `int ~ bool`.

### Example: inference through `is`

```prolog
:- chr_constraint result(int).
rule @ result(R) <=> S is R + 1, result(S).
```

- `R : int` (from `result(int)` in the head).
- `S is R + 1`: the RHS is an evaluated position, so `R + 1` is typed
  by the declared signature of `+`, giving `int`. `S` is a local
  variable — a fresh flexible — and binds to `int`.
- Body `result(S)`: `S` is `int`, consistent with the declared
  argument type.

`R is e` flows the inferred type of `e` into a *flexible* LHS — the
ordinary meet of §Type states. An `any`-typed LHS is checked against
and never refined:

```prolog
:- chr_constraint out/1.
:- function double(int) -> int.
rule @ out(R) <=> R is double(1).
```

- `R : any` (from the untyped `out/1`, i.e. `out(any)`).
- `R is double(1)`: the RHS type `int` is checked against `any` and
  `R` stays `any` — nothing narrows `any` (§The role of `any`).

The first rule uses `is`, not `=`. `=` is structural (§Expression
Typing): `S = R + 1` binds `S` to the symbolic compound
`prelude:+(R, 1)`, whose type *as a term* is `any`; `any` does not
propagate, so `S` would stay flexible and a later misuse would go
unreported. Use `is` for the arithmetic — and the type.

At a *rigid* LHS, `is` is an error:

```prolog
:- chr_constraint go(A, A).
go(R, _) <=> R is 1 + 1.
```

- `R : T` — the head occurrence of the polymorphic `go(A, A)`
  allocates a rigid `T` (§Rigid and flexible type variables).
- `R is 1 + 1`: the RHS type `int` meets the rigid `T` — an error. The
  store chose `T` when the matched constraint was told; a rule that
  writes an `int` into a `T` position is only correct at `T = int`,
  which nothing enforces. Declaring `go(int, int)`, or guarding the
  rule with the evidence form `integer(R)` (§Guard-Derived Type
  Evidence), states that intent and checks.

A well-typed expression can still fail at runtime: a function call
type-checks against the declared return type, but the runtime raises
`YCHR-60001` if no equation matches the actual arguments. Given a
partial function

```prolog
:- function half(int) -> int.
half(0) -> 0.
```

`R is half(5)` type-checks with `R : int`, yet at runtime raises
`YCHR-60001` ("no matching equation") because no equation covers `5`.
The checker does not model which inputs an equation set covers; that
is enforced only at evaluation time.


## Type Checking Procedure

Type checking operates on each rule, function equation, and
top-level goal independently. Goals are checked exactly like rule
bodies: each constraint tell or expression in a goal is a use site,
and bounded constraints discharge their bounds there (§Bounded
Polymorphism). For each such unit, the checker:

1. Collects type constraints from all positions (see below).
2. Solves the constraints together using unification and consistency.
3. Reports all inconsistencies as type errors.

Constraints come in two tiers:

- **Equational constraints** — unifications, `is` flows, and plain
  consistency checks, solved as a set by ordinary unification under
  the meet table of §Type states.
- **Residual checks** — overload resolutions (§Signature Overloading
  §Resolution) and bound checks (§Bounded Polymorphism §Use-site
  checking). A residual check is *pending* until it can act, under
  the following discipline:

  1. A pending overload resolution **fires** — commits to a declared
     signature, unifying argument types and propagating the return
     type — only when all of its surviving candidate signatures are
     equal after substitution (in the common case exactly one
     survives). Firing adds information and may enable other pending
     checks; solving repeats until none can fire.
  2. A pending check whose candidate set becomes empty reports an
     error (`NoMatchingOverload` for resolutions, `BoundUnsatisfied`
     for bound checks) whenever that happens.
  3. A pending check still ambiguous when solving ends succeeds
     silently — the gradual behavior: its result type stays flexible
     and nothing is propagated.
  4. A fired commitment is never retracted; if later information
     contradicts it, the contradiction surfaces as an ordinary
     inconsistency error.

  Bound checks are the propagation-free special case: they never
  modify the substitution, so for them "firing" is merely the
  existence check of §Use-site checking.

Solving is order-independent in this precise sense: the set of
accepted programs and the final type assignment do not depend on the
order constraints are gathered or pending checks examined in; only
error attribution (which check reports first) may vary. The reason is
monotonicity: solving only adds information, so a candidate set only
shrinks and never grows back from one candidate to several; the
signature a check fires on is therefore uniquely determined whenever
it fires, and if the chosen candidate would later have been
eliminated, every examination order rejects the program — early firing
surfaces the contradiction through the propagated types, late
examination through an empty candidate set.

One unit-level rule sits above the per-check discipline: a unit whose
evidence facts contradict a known type is *inaccessible*
(§Guard-Derived Type Evidence §Inaccessible branches). A contradicting
fact binds nothing, so solving proceeds normally; afterwards the unit
reports its ordinary errors if any, and the `YCHR-20104` warning only
otherwise — a warning never suppresses an error. Both ingredients are
properties of the gathered constraints, so this rule is
order-independent too.

### Type variables and instantiation

At a use site (a call, a body tell, a goal) the checker instantiates
the declared type with fresh flexible unification variables: if
`member(A, list(A))` is called twice in a rule, each use gets
independent fresh variables (`a₁, list(a₁)` and `a₂, list(a₂)`).
Implementation sites — function equations and rule-head occurrences —
instead allocate *rigid* variables (below).

Type variables unify by substitution under the meet table of §Type
states: a type variable that meets `any` is **not bound**, so `any`
cannot leak through shared type variables and mask real
inconsistencies.

Given `:- chr_constraint foo(A, A).` and a use `foo(X, Y)` with
`X : any` and `Y : int`:

- Fresh `α` for `A`.
- `α ~ any` (from X): succeeds, `α` unchanged.
- `α ~ int` (from Y): `α = int`.

The concrete type `int` is preserved despite the `any` input.

Type variables still unconstrained after solving are not errors: they
are genuinely polymorphic usage.

#### Rigid and flexible type variables

Unsolved type variables come in two flavors:

- A **flexible** type variable is a fresh unification variable
  allocated at a use site of a declared constraint or function — a
  normal HM unification variable: later constraints can bind it to a
  concrete type, it succeeds silently in overload resolution when its
  declared counterpart is also unbound (§When arguments are not yet
  resolved), and it satisfies the gradual guarantee.

- A **rigid** type variable is a declaration's own type parameter at
  an *implementation site*: a function's type parameter, in scope
  while its equations are checked, or a typed polymorphic constraint's
  type parameter, in scope at a rule-head occurrence while that rule
  is checked. It behaves as an opaque type constant (a skolem):
  consistent with itself, with `any` (nothing binds), and with
  flexible variables — which it *binds*, so rigidity travels through
  intermediate flexibles (calling `id(A) -> A` at a rigid `T` yields a
  `T`, not an unconstrained variable); inconsistent with every
  concrete type and every distinct rigid variable, so it never
  silently matches a declared concrete type. (A `GuardMatch` at a
  rigid scrutinee also introduces fresh rigid variables for the
  matched constructor's type parameters — §Guard-Derived Type
  Evidence.) A body that uses an overloaded operation at a rigid tvar
  must therefore resolve it through an ambient signature from a
  `requiring` clause (§Bounded Polymorphism) or through guard-derived
  evidence that pins the variable (§Guard-Derived Type Evidence);
  without either the call fails with `NoMatchingOverload`
  (YCHR-60006).

Each rule-head occurrence allocates its **own** rigid variables, even
between two occurrences of the same constraint. The store is a
heterogeneous multiset: with `:- chr_constraint leq(T, T).`, an
`leq(1, 2)` and an `leq(a, b)` may be stored side by side, and each
head occurrence matches an independently chosen instance; a single
rule-wide rigid `T` would silently assume all matched partners share
one instantiation, which nothing enforces. Where matching *does* force
instances to agree — a variable shared between head positions — the
agreement is recovered as evidence: HNF desugars the shared variable
into an explicit `GuardEqual` (§Sources of Type Information §8), an
evidence form which, when the variable occupies two whole rigid
positions, merges the two skolems (a variable shared only *inside* a
parametric type, `list(T₁)` against `list(T₂)`, merges nothing — a
parameter-erasing value satisfies that equality without the instances
agreeing; §What evidence does). Multi-head idioms like transitivity of
a polymorphic `leq(T, T)` therefore still check; see the worked
example in §Guard-Derived Type Evidence.

Rigidity is local to the implementation-site check: every use site (a
call, a body tell, a goal) allocates fresh *flexible* variables by
`copy_term`-style refresh, so callers keep the gradual guarantee
unchanged. Untyped and `any`-annotated declarations have no type
parameters to make rigid — their argument positions stamp `any` (§Type
states) — so unannotated programs never meet a rigid variable.


## Sources of Type Information

These constructs generate type constraints within a rule or function
equation:

### 1. Constraint head positions

A rule-head constraint constrains its argument variables: with
`leq(int, int)` declared, a head `leq(X, Y)` gives `X : int` and
`Y : int`. A *polymorphic* constraint's head occurrence types its
variables through fresh per-occurrence rigid parameters (§Rigid and
flexible type variables): with `leq(T, T)` declared, the same head
gives `X : T` and `Y : T` at that occurrence's rigid `T`.

### 2. Function equation parameters

A function's declared argument types constrain the parameter
variables: with `sign(int) -> result` declared, an equation
`sign(N) -> ...` gives `N : int`.

### 3. Function return type

The declared return type constrains each equation's right-hand side:
with `sign(int) -> result`, each RHS must be consistent with `result`.

### 4. `is` expressions (RHS to LHS flow)

In `R is expr`, the type of `expr` flows to `R` through the ordinary
meet of §Type states: a flexible LHS binds to the RHS's concrete (or
rigid) type; `any` on either side is checked against without binding —
an `any`-typed RHS leaves the LHS unchanged, an `any`-typed LHS is
never refined (§The role of `any`); a rigid LHS meeting a concrete RHS
type is an error, like every rigid/concrete meet.

Inside a function body, `R is expr` *rebinds* `R` rather than
constraining it: the runtime introduces a fresh local, and the checker
gives it a fresh type slot for the statements that follow. A
declared-`any` `R` is the exception — its rebound local keeps `any`
whatever the RHS evaluates to; anything else would make `is` a
back-door refinement of precisely the variables the declaration asked
to leave alone (§The role of `any`).

### 5. Unification (bidirectional)

In `X = Y` (body unification) type information flows both ways, per
the meet table of §Type states: a flexible variable binds to the other
side's concrete (or rigid) type, two flexible variables alias, and
`any` on either side is checked against without binding — a variable
never becomes `any` through unification, and an `any`-typed variable
never loses its `any`. Two known concrete types are checked for
consistency. Non-variable operands are typed structurally (§Expression
Typing).

### 6. Body constraint calls

A body constraint call constrains its argument expressions: with
`leq(int, int)` declared, a body `leq(X, Z)` requires `X` and `Z`
consistent with `int`.

### 7. Body function calls

A function call in a body or guard constrains its argument expressions
and produces a result type: with `sign(int) -> result`, a body
`R is sign(X)` requires `X` consistent with `int` and gives `R` type
`result`.

### 8. Desugared guards (HNF synthetic guards)

Head Normal Form desugaring introduces synthetic guards:

- **`GuardMatch term functor arity`**: relates `term` to the algebraic
  type containing the given constructor (§Constructor Typing). An
  **evidence form**: a successful match proves the value inhabits that
  type, so the fact may bind a rigid scrutinee (§Guard-Derived Type
  Evidence).
- **`GuardGetArg var term index`**: the extracted variable gets the
  type of the constructor's field at the given index, at the
  instantiation the preceding match determined (§Guard-Derived Type
  Evidence §What evidence does). A `GuardGetArg` always follows a
  `GuardMatch` on the same term, which establishes the constructor and
  so the field types.
- **`GuardEqual term1 term2`**: relates the two terms' types. An
  **evidence form**: ask-equality succeeds only on structurally
  identical terms, so whenever the guard passes the two types agree
  *up to their outermost type constructors* — a value determines its
  constructor nominally but not the constructor's parameters
  (§Guard-Derived Type Evidence).
- **`GuardExpr term`**: a general boolean guard expression (`N > 0`);
  `term` must be consistent with `prelude:bool`. A call of a
  refinement predicate on a bare variable here is an evidence form
  (§Guard-Derived Type Evidence).

These guards carry the same type information as the pattern the user
wrote. When an evidence form's fact contradicts a concrete type, the
guard can never succeed: the enclosing rule or equation is dead code
and — when it otherwise checks clean — draws the inaccessible-branch
warning (`YCHR-20104`) rather than an error (§Guard-Derived Type
Evidence).

Body goals not listed above (`true`, say) generate no type
constraints.


## Guard-Derived Type Evidence

Implementation sites are checked under rigid type variables: a rule or
equation body must be correct for an *arbitrary* instantiation of each
skolem (§Rigid and flexible type variables). A `requiring` clause
(§Bounded Polymorphism) is one way to discharge an obligation at a
skolem; this section defines the other: facts established by the
*operational success* of guards.

### The evidence criterion

> A guard form is an **evidence form** exactly when its success at
> runtime entails a typing fact. The fact may be assumed in every
> position that executes only after the guard has succeeded: the
> guard conjuncts to its right, and the rule or equation body.

The criterion is the soundness argument in miniature: code guarded by
an evidence form runs only in executions where the fact holds, so
checking it under the fact claims nothing about executions that cannot
happen. Evidence availability is determined purely by source position
and fixed when constraints are gathered; solving them remains
order-independent (§Type Checking Procedure). The left-to-right
sensitivity is operational, not an artifact: `integer(X), X > 0` and
`X > 0, integer(X)` genuinely differ at runtime — in the second `>`
can receive a non-integer — and the checker's verdicts differ in
exactly the same way. HNF-synthetic guards (§8) represent head
matching, which happens before any user guard runs, so their evidence
is available to the whole guard sequence and body.

One consequence of order-independent solving: a check still *residual*
when a later evidence fact is told sees that fact, since retries run
against everything solved, evidence gathered to the check's right
included. This does not widen the criterion — a check with enough
information to decide at its gather position already decided there. In
`X > 0, integer(X)` at a rigid `X : T`, the overload resolution finds
an empty candidate set at the unpinned skolem and errors immediately,
before the `integer` fact exists; only checks still waiting for
information can be revived by one.

### Evidence forms

| Form | Fact on success |
|------|-----------------|
| `GuardEqual t₁ t₂` — emitted only by HNF, for a variable shared between head positions or a non-variable head argument (§8) | `type(t₁)` and `type(t₂)` agree on their outermost type constructor; at a rigid variable the pin this induces is per §What evidence does |
| `GuardMatch x c/n`, where `c` is a declared constructor of `D(α₁, ..., αₖ)` | `type(x)` is an application of `D` (parameter instantiation per §What evidence does) |
| A call `p(X)` on a bare variable, where `p` is declared `refining τ` | `type(X)` is `τ` (parameter instantiation per §What evidence does) |

A `GuardEqual` between the HNF halves of one repeated source variable
additionally carries the declaration-source merge of §Type states: the
two halves are one variable, so a still-flexible half takes the
other's type — at every depth, not just the top level: a half is
routinely structured (matching `p([E | X])` types `X` as `list(α)`,
and a partner `q(X)` at `q(list(int))` is what says `α` is `int`), and
the merge reaches inside type constructors as ordinary unification
does. That binding is ordinary meet, not evidence — evidence proper
stays inert at a flexible variable (§What evidence does) — and the
distinction matters only where one half has a solid declaration source
and the other does not.

The declaration-source merge cannot be asserted of a variable whose
two halves are `α` and a type *containing* `α`, as in `p([X | X])`: no
finite type satisfies it. At a flexible half the fact is dropped
silently — such a pattern still matches an improper list at run time,
and the checker does not move in the rejecting direction on code it
was told nothing about. At a rigid half no cycle arises: the evidence
pin never copies the other side's parameters (§What evidence does), so
`T` against `list(T)` pins `T := list(β)` with a fresh rigid `β` —
satisfiable by `p([[] | []])`, so nothing is reported.

Justifications. Ask-equality (`==`) succeeds only on structurally
identical terms — the *same* still-unbound variable on both sides
included — and a constructor determines its algebraic type nominally,
so equal structure entails equal *type constructor*. It does not
entail equal type *parameters*: a parametric type has values that fail
to determine them — `[]` inhabits `list(τ)` for every `τ`, `empty`
inhabits `box(τ)` for every `τ` — so two structurally identical values
may be typed at different instantiations, and an equality between them
proves nothing about the parameters (the observation that also
excludes `atom(X)` as an evidence form, §Non-forms). Identical
variables denote the same future value, so any type describing one
describes the other — again up to the outermost constructor. A
successful `GuardMatch` proves the value was built by `c`, and within
the typed fragment `c`-values inhabit only `D` (a forged `c` compound
is typed `any`, an `any`-introduction form, §Soundness); how `D`'s
type parameters are instantiated depends on the scrutinee's state
(§What evidence does). A refinement predicate's fact is not justified
but *declared*: see below.

#### Refinement predicates

A function declares itself a refinement predicate with a `refining`
clause on its signature:

```prolog
:- function integer(any) -> bool refining int.
:- function is_list(any) -> bool refining list(A).
```

The clause is an **axiom**. The equations are type-checked like any
others, but nothing checks them *against* the clause — and for the
usual case, a predicate backed by a host call whose argument and
result are typed `any`, there would be nothing at that boundary to
check. The declaration is a promise that a successful call proves its
argument has the refined type, and it is the author's to keep
(§Soundness).

Only a guard call of the form `p(X)`, on a *bare* variable, in a rule
guard or a function-equation guard, contributes a fact. A call on a
compound argument, a call in a body, and a call on the right of `is`
contribute nothing.

The clause is permitted only on a closed `:- function` carrying a
single typed signature of the exact shape `name(any) -> bool`. It is
rejected on `:- open_function`, on `:- class` and `:- open_class`, on
the untyped `name/arity` spelling, at any arity other than 1, and when
the argument is not `any` or the return is not `bool`. Combining it
with `requiring` is rejected by the grammar rather than by a check:
the two are operators of equal priority, so they cannot chain in
either order. Every other violation is `YCHR-16021`, and one on a
`:- chr_constraint` is `YCHR-15020`.

The refined type must be a base type (`int`, `float`, `string`) or a
type constructor applied to *distinct type variables*. A nullary
constructor is the zero-parameter case, so `refining bool` and
`refining color` are fine.

The parameters must be named variables; a wildcard (`refining
list(_)`) is not a type expression and is rejected earlier, as
`YCHR-15009`.

The parameters carry the restriction. Evidence pins only the outermost
constructor, at fresh parameters (§What evidence does), so `refining
list(int)` could only ever mean `refining list(A)`: the concrete
parameter is rejected rather than silently widened, and a parameter
repeated as in `pair(A, A)` for the same reason. A bare type variable
and `any` are rejected at the other end — they constrain nothing, so
the clause would buy the caller no evidence — and a function type
because a refinement predicate tests a value, not a callable.

The prelude declares four: `integer/1`, `float/1`, `string/1` and
`boolean/1`. `atom/1`, `var/1`, `nonvar/1` and `ground/1` deliberately
do not (§Non-forms). Two more ship in the libraries: `is_list/1` in
`library(lists)`, refining `list(A)`, and `is_maybe/1` in
`library(maybe)`, refining `maybe(A)`. Both answer `false` where a
type predicate has nothing to stand on — an unbound argument included,
since a variable that may yet be bound to a list is not a list.

### Non-forms

The criterion excludes, deliberately:

- User-written `==` in a guard: it desugars to `GuardExpr` — an
  ordinary call of the prelude function `'=='(A, A)` — not to
  `GuardEqual`, so it contributes no evidence. A `refining` clause
  cannot express it either: the fact `==` would establish is
  *relational* (its two operands agree), and a refinement predicate
  states a type of one argument. The `GuardEqual` form above is the
  relational reading, and HNF is the only thing that emits it.
- `var(X)`, `nonvar(X)`, `ground(X)`: success entails a *boundness*
  fact, not a type fact.
- `atom(X)`: success entails that `X` is *some* nullary data
  constructor, but nullary constructors inhabit many types (`red :
  color`, `[] : list(A)`, `true : bool`) and the type grammar has no
  unions, so no single typing fact follows.
- Overloaded comparisons and arithmetic (`X > 0`): success does not
  pin the operand's type — which signature ran is a runtime matter,
  and a host-backed comparison need not reject every value its
  static signatures would.
- Ordinary function calls in guards: success entails only the
  declared return type, which call typing already provides (§7).

### What evidence does

Evidence acts according to the *state* (§Type states) of the type it
scrutinizes:

- **Rigid** — the fact binds or merges the skolem, but only to the
  extent the underlying runtime fact determines a type. Three cases:
  - *Rigid meets rigid, whole types*: `type(X) = type(Y)` at `X : T₁`,
    `Y : T₂` merges `T₁` and `T₂` — the multi-head idiom (§Worked
    example: multi-head rules).
  - *Rigid meets a non-parametric type* (a base type or a nullary
    constructor application): the fact pins the skolem —
    `type(X) = int` at `X : T` binds `T := int`. Such a type is
    determined by its values, so the pin is exactly what the guard's
    success proves.
  - *Rigid meets a parametric application or a function type*: the
    fact pins only the outermost constructor, at **fresh rigid
    parameters** — `T` against `list(int)` pins `T := list(β)` with
    `β` fresh and *unrelated* to `int` — the same discipline as
    `GuardMatch` at a rigid scrutinee (below): the values witnessing
    the equality need not determine the parameters (`[]` inhabits
    every `list(τ)`), so nothing downstream may assume more than the
    constructor.

  Inside a shared constructor — the parameter positions of a
  `GuardEqual` whose two sides are applications of the same constructor,
  `box(A)` against `box(int)` — equality evidence derives *nothing*
  about rigid variables, no pins and no merges: a parameter-erasing
  value may account for the equality, so no parameter-position fact is
  entailed. (The declaration-source merge at *flexible* parameter
  positions still applies, §Evidence forms.) Binding or merging a rigid
  variable is the single exception to the meet table's rigid rows, and
  evidence is the *only* mechanism that may perform it.
- **Concrete** — the fact is checked. A mismatch means the guard can
  never succeed within the typed fragment, so the enclosing rule or
  equation is *dead code*. The contradicting fact binds nothing — the
  scrutinized type is already known — so checking continues with the
  declared types; if the unit otherwise checks clean, the checker
  emits the **inaccessible-branch warning** (`YCHR-20104`, severity
  *warning*) and the program still compiles. A dead unit that also
  contains ordinary errors reports those and omits the warning: a
  warning never suppresses an error (§Inaccessible branches).
  `--Werror` promotes the warning, as with exhaustiveness
  (§Exhaustiveness checking). (During per-signature checking of a
  `:- class` equation, a contradiction instead counts as failure under
  that candidate signature and emits nothing — §Signature Overloading
  §Equation checking.)
- **`any`** — inert. Nothing narrows `any` (§The role of `any`);
  findings about `any`-typed code are reserved for a planned opt-in
  warning pass.
- **Flexible** — inert *as evidence*: refinement predicates and
  `GuardEqual` contribute nothing at a flexible variable, so evidence never
  restricts unannotated code. (`GuardMatch`'s ordinary
  constructor-typing meet still applies and binds the flexible — next
  paragraph — but that is declaration-derived information, not
  evidence, as is the merge of the two HNF halves of one repeated
  source variable, §Evidence forms.)

For `GuardMatch`, the instantiation of `D`'s type parameters follows
the same states. At a rigid scrutinee `x : T`, the match binds
`T := D(β₁, ..., βₖ)` with fresh **rigid** `βᵢ` — the matched value's
field types are store-chosen, and nothing downstream may assume more
about them than the match proved; `GuardGetArg` types the extracted
fields at those `βᵢ`. At a scrutinee whose type is already known —
concrete, or a constructor application such as the `list(T)` argument
of a polymorphic `sorted` — the fact reduces to constructor
*membership*: `c` must belong to that type (otherwise the branch is
inaccessible, `YCHR-20104`), and `GuardGetArg` reads field types off
the known instantiation (matching `[X | Xs]` against `list(T)` gives
`X : T` and `Xs : list(T)`). At an `any` scrutinee the match says
nothing about the scrutinee — nothing narrows `any` — while the
extracted fields are typed at a fresh all-flexible instantiation of
the constructor's declared field types. At a flexible scrutinee the
match is the ordinary meet: the flexible binds to `D` at a fresh
flexible instantiation.

The asymmetry is the design principle. At a rigid variable evidence is
purely *enabling*: a skolem rejects every concrete use, so evidence
can only accept programs otherwise rejected. At `any` or a flexible
variable it could only *restrict* — `any` already passes every check —
and the checker never moves in the rejecting direction on unannotated
code. This is also why the gradual guarantee is unaffected: rigid
variables exist only where a declaration introduces type parameters,
so a program without annotations never meets evidence (§Soundness).

### Worked example: multi-head rules

```prolog
:- chr_constraint leq(T, T).
trans @ leq(X, Y), leq(Y, Z) ==> leq(X, Z).
```

HNF renames the shared `Y`, giving heads `leq(X, Y), leq(Y1, Z)` with
the synthetic guard `GuardEqual(Y, Y1)` (§8). Checking:

- First head occurrence: fresh rigid `T₁`; `X : T₁`, `Y : T₁`.
- Second head occurrence: fresh rigid `T₂`; `Y1 : T₂`, `Z : T₂`.
- `GuardEqual(Y, Y1)`: evidence `type(Y) = type(Y1)`, i.e. `T₁ = T₂` —
  the two skolems merge into one `T`.
- Body tell `leq(X, Z)`: a use site; its fresh flexible variable
  instantiates to `T` from both arguments. The rule checks.

Without the evidence step the two skolems would stay distinct and the
body tell would fail. The evidence recovers exactly the agreement
runtime matching guarantees: both occurrences matched the same value
for `Y`, so their instantiations coincide. Contrast a rule whose head
occurrences share nothing:

```prolog
:- chr_constraint pair(T, T), out(T, T).
weird @ pair(X, _), pair(_, Y) ==> out(X, Y).
```

No `GuardEqual` links the occurrences, so `X : T₁` and `Y : T₂` stay
distinct and the tell `out(X, Y)` is an error — correctly so: the
store may hold `pair(1, 1)` and `pair("a", "b")` simultaneously, and
firing would tell an `out` at `(int, string)`, which no instantiation
of `out(T, T)` allows.

### Worked example: type-case equations

```prolog
:- function int_to_string(int) -> string.
:- function show(T) -> string.
show(X) | integer(X) -> int_to_string(X).
show(X) | string(X)  -> X.
```

`T` is rigid in each equation. The first equation's guard contributes
`type(X) = int`, binding `T := int` for that equation;
`int_to_string(X)` then resolves, and the RHS type is consistent with
the declared return type. The second equation checks at `T := string`
the same way. Called at a type neither guard accepts, the runtime
falls through to the ordinary "no matching equation" error
(`YCHR-60001`); no value is ever misused, which is what makes the
per-equation assumption sound. (Multi-signature `:- class`
declarations get a similar effect through per-signature equation
checking, §Signature Overloading §Equation checking; evidence brings
the same expressiveness to single-signature polymorphic functions.)

An operation at a rigid variable can therefore be discharged two
ways: statically, by a `requiring` clause whose ambient signature
covers it at every instance (§Bounded Polymorphism), or dynamically,
by an evidence guard that pins the variable on the one path where
the operation runs. The first says "callers must supply this"; the
second says "this branch handles exactly this case".

### Inaccessible branches

```prolog
:- chr_type color ---> red ; green ; blue.
:- chr_constraint tag(color).
dead @ tag(X) <=> integer(X) | true.
```

`X : color` (concrete), and the guard's fact `type(X) = int`
contradicts it: within the typed fragment no `color`-typed value is
an integer, so the guard cannot succeed and the rule cannot fire.
The rule otherwise checks clean, so it draws `YCHR-20104`
(warning). The same applies to a `GuardEqual` between positions
whose concrete types differ at the *outermost* constructor — for
instance a variable shared between an `int` and a `string` head
position — and to a `GuardMatch` against a constructor of a type
other than its scrutinee's: each marks a rule or equation that can
never fire in the typed fragment. That is dead code, not a type
error. A gradually-typed program can still reach such a rule by
flowing `any`-typed values into it; the warning severity reflects
that the checker's claim is limited to the typed fragment. A
mismatch confined to the *parameters* of a shared constructor — a
variable linking a `box(int)` position to a `box(bool)` one — is
**not** dead code and draws nothing: a parameter-erasing value
(`empty`, `[]`) satisfies the equality, so the rule can fire.

A contradicting fact binds nothing — the scrutinized type is
already known — so checking simply continues with the declared
types, and whether the warning is reported is decided after
solving: a dead unit that also contains ordinary errors reports
those errors and omits the warning (inaccessibility is a warning,
and a warning never suppresses an error); a dead unit that
otherwise checks clean reports exactly `YCHR-20104`. Had the
`dead` rule's body also misused `X` — say `Y is X + 1` — the
resulting overload error would be reported and the warning
dropped. Both the unit's error set and the presence of a
contradiction are properties of the gathered constraints, not of
any examination order, so acceptance remains order-independent
(§Type Checking Procedure).


## Expression Typing

Expression typing follows evaluation. Positions the runtime
*evaluates* — function, constructor, and tell-side constraint
arguments, `is` right-hand sides, guards — are typed by the signatures
of the functions involved. Positions the runtime treats *structurally*
— the operands of `=`, head and equation patterns, `GuardEqual`
operands, `quote`d terms — are typed by constructor typing alone
(§Constructor Typing). In a structural position, a compound whose
functor names a declared function or class is *not* a call: the
functor is not a data constructor, so the term is typed `any` (an
*evaluable-headed* term, §Constructor Typing). So `Sum = 1 + 1` binds
`Sum` to a symbolic compound typed `any`, while `Sum is 1 + 1` gives
`Sum : int`.

An expression's type is determined by its outermost form:

- **Literal**: `3` has type `int`, `"hi"` has type `string`.
- **Known constructor**: looked up via constructor typing (§Constructor Typing).
- **Unknown constructor**: type `any`. The argument *positions* impose
  no expected type, but each argument expression is still typed by its
  own rules, so an error nested inside one is still reported.
- **Variable**: determined by the constraints on that variable.
- **Function call `f(e₁, ..., eₙ)`**: the declared type variables are
  instantiated with fresh unification variables; each argument `eᵢ`
  must be consistent with the corresponding declared parameter type,
  and the call's type is the declared return type under the same
  substitution. The implementation's RHS type is only checked for
  consistency with the declaration — callers never see through to the
  implementation.
- **Host call**: every argument position and the return type are
  `any`; the argument expressions themselves are still typed.


## Constructor Typing

An atom or compound term is typed by looking its constructor up in the
visible type definitions.

### Known constructors

If `some` is a constructor of `option(A)` with field type `A`, then
`some(X)` has type `option(A)` (with `A` fresh), and `X` gets type
`A`.

A constructor's arity is part of its identity: `some/1` and `some/2`
are not two arity-overloaded constructors but a duplicate declaration,
so using a known constructor with the wrong number of arguments is a
type error (`ConstructorArityMismatch`, YCHR-60008), not a
fall-through to `any`. The error names the declared arity, and the
offending use is then typed `any` so it draws no second, downstream
mismatch. The renamer reports the same mistake independently as
warning `YCHR-20102`; a use the checker reports also draws the
renamer's warning.

### Unknown constructors

A constructor found in no visible type definition is typed `any` and
draws an `UndeclaredDataConstructor` warning (`YCHR-20101`, severity
*warning*). No error is produced:

- If the context expects a concrete type, the unknown constructor is
  consistent (`any ~ τ` for all `τ`) — the checker cannot verify it is
  correct, but cannot prove it wrong either.
- If the context expects a specific algebraic type and the constructor
  is *known to belong to a different type*, that is an error via
  normal consistency checking.

### Evaluable-headed terms

A compound in structural position whose functor names a declared
function or class — `+(1, 1)` as an operand of `=` — is also typed
`any` but draws **no** warning: the functor is known, just not a data
constructor, and building symbolic terms over evaluable functors is a
deliberate feature. Like every `any`-typed expression, such a term is
an `any`-introduction form (§Soundness): it type-checks against any
context, and the checker promises nothing about what happens when it
is later consumed as a value.

### Constructor disambiguation

Constructors are disambiguated by module qualification, per the module
system: if `red` is a constructor of both `color` and `traffic_light`
(in different modules), the user must write `color:red` or
`traffic_light:red`.


## Exhaustiveness checking

The compiler warns (`YCHR-20103`, severity *warning*) when a
function's pattern-matching equations cannot match some value of a
declared algebraic type:

```prolog
:- module(m, []).

:- chr_type color ---> red ; green ; blue.
:- function rank(color) -> int.
rank(red)   -> 1.
rank(green) -> 2.
```

emits

```
Non-exhaustive patterns in function 'm:rank/1': no equation matches m:rank(m:blue)
```

The check is deliberately narrow:

- It applies to **functions only**, never to rules.
- A function argument is checked **only when its declared type is an
  algebraic type**. Positions of `int`/`float`/`string`, opaque types,
  type variables, `any`, or unknown types cannot be enumerated, so
  they never cause a warning (they count as always covered). A nested
  constructor field is checked under the same rule, at the field's
  declared type.
- Only **closed, single-signature** functions are checked.
  `:- open_function` and `:- open_class` may gain equations in other
  modules, so a local gap might be filled elsewhere; multi-signature
  `:- class` functions have no single column type to enumerate.
- An equation with a **user guard** does not count as covering its
  pattern, since the guard may fail at runtime. A variable or wildcard
  pattern covers a position exhaustively.
- A gap attributable **only to non-enumerable columns** produces no
  warning: the reported example must name at least one missing
  constructor. `:- function f(int) -> int.` with the single equation
  `f(0) -> 1.` is operationally non-exhaustive, but the only example
  it could report is `f(_)` — no declared type is missing a case, so
  nothing is reported.

The check uses Maranget's matrix/usefulness algorithm, so it handles
multiple arguments and nested constructor patterns and reports a
concrete unmatched example. Being a warning, a non-exhaustive function
still compiles and runs (raising a runtime error only if an unmatched
value reaches it); `--Werror` promotes it to a hard error.

The dual dead-code warning — a rule or equation that can never fire
because its guards contradict known types — is the
inaccessible-branch warning (`YCHR-20104`, §Guard-Derived Type
Evidence), which follows the same severity policy.


## Host Calls

Host language calls (`host:f(args)`) impose no expected type on their
arguments and return `any`. The checker does not look inside the host
function but does type the argument expressions, so an error nested in
one is still reported.

CHR library functions wrapping host calls (the prelude's `+`, `-`,
`>`) may have declared signatures; checking happens at the CHR
function call boundary, not at the host call:

```prolog
:- function '+'(int, int) -> int.
X + Y -> host:'+'(X, Y).
```

`X + Y` is checked against `(int, int) -> int`; the internal
`host:'+'(X, Y)` is unchecked (all `any`).


## First-Class Functions

Lambdas and function references are first-class values with function
types.

### Lambdas

A lambda `fun(X, Y) -> expr end` gets its function type from context:
where a `fun(int, int) -> bool` is expected, `X : int`, `Y : int`, and
`expr` must be consistent with `bool`.

A lambda where no function type is expected (passed to an `any`-typed
parameter, or unified with a fresh variable) is typed by inference
alone: each parameter gets a fresh flexible variable, the body is
checked normally, and the lambda's type is `fun(α₁, ..., αₙ) -> τ`,
`τ` the body's inferred type and the `αᵢ` whatever those variables
were bound to (possibly still flexible).

A lambda cannot carry a `requiring` clause: `requiring` attaches only
to declarations (`:- function`, `:- open_function`,
`:- chr_constraint`), and a lambda has none. A lambda whose body uses
bounded operations is checked against its expected function type, and
unresolved bounds discharge through the residual-constraint mechanism
that handles function references (§Function references).

### Function references

A reference `fun name/arity` is checked against the expected function
type at its use site: the checker instantiates the referenced
function's declared signature with fresh unification variables,
unifies it with the expected type, and — if the function carries a
`requiring` clause — emits a bound check at the resulting substitution
(§Bounded Polymorphism, §Use-site checking). The bound check is a
residual constraint, solved together with the surrounding equation's
other type constraints.

With `double(int) -> int` declared (no bound), `fun double/1` has type
`fun(int) -> int` at every use site.

A reference to a multi-signature class is itself a residual overload
resolution (§Type Checking Procedure): the expected function type at
the use site filters the class's signatures, and the reference commits
when all surviving candidates are equal after substitution; a
resolution still ambiguous when solving ends succeeds silently and the
reference's type stays flexible. This is asymmetric with §Resolution's
"result type never disambiguates": a *call*'s expected result type
never filters an overload, but a *reference* is matched against a full
function type, whose return component participates — a reference has
no argument expressions, so the expected type is all the checker has.

With `:- function max(T, T) -> T requiring '>'(T, T) -> bool.`
declared, `fun max/2` is well-typed wherever the context lets the
bound discharge. Given
`:- function apply2(fun(T, T) -> T end, T, T) -> T.`, which links the
reference's expected function type to the other two arguments:

- In `apply2(fun max/2, 1, 2)`, the args constrain the substitution to
  `T := int`; the residual bound `'>'(int, int) -> bool` resolves
  against the declared signature.
- In `apply2(fun max/2, "a", "b")`, the same mechanism produces
  `'>'(string, string) -> bool`, which has no consistent declared
  signature; error `BoundUnsatisfied` (YCHR-60012).
- In `apply2(fun max/2, X, Y)` with `X` and `Y` carrying no concrete
  type information, the substitution leaves `T` free and the bound
  succeeds silently per the gradual guarantee, exactly as ordinary
  overload resolution does under unresolved arguments.

To export a polymorphic value that refers to a bounded function and
propagates the bound to its callers, the enclosing declaration must
hoist the bound onto its own signature with its own `requiring` clause
(as a Haskell signature must include the constraint when partially
applying an overloaded operator). Without it, the outcome depends on
the enclosing declaration: if it is polymorphic, its type parameters
are rigid during equation checking, so the un-hoisted residual bound
finds no consistent candidate and fails with `BoundUnsatisfied` —
hoisting is mandatory, exactly as the missing constraint would be an
error in Haskell; if the enclosing position is untyped or `any`-typed,
no rigid variables are in play, so the bound discharges silently and
is invisible to callers — the usual gradual-typing tradeoff.

### `call`

The prelude provides a typed wrapper for first-class function
application:

```prolog
:- function call(fun(A) -> B end, A) -> B.
call(F, X) -> '$call'(F, X).
```

The internal `$call` primitive is a host-level operation typed `any`;
checking happens at the `call` boundary, not at `$call`.


## Type Definition Validation

The checker validates type definitions themselves:

1. **Bound variables**: all type variables appearing in constructor
   fields must be bound by the type definition header. For example,
   `type foo(A) ---> bar(B)` is an error (`UnboundTypeVar`,
   YCHR-60004) because `B` is not bound.

2. **Defined types**: types referenced in constructor fields must be
   defined. For example, `type foo ---> bar(undefined_type)` is an
   error (`UndefinedType`, YCHR-60005). Recursive references to the
   type being defined are fine: `type list(A) ---> cons(A, list(A))`
   is valid.

3. **Arity**: a type reference in a constructor field must apply the
   referenced type constructor to exactly as many arguments as its
   declaration has parameters; `bar(list)` is an error
   (`TypeRefArityMismatch`, YCHR-60013) if `list` is declared as
   `list(A)`.

Forward references and mutual recursion between type definitions are
allowed; declaration order is irrelevant.


## Signature Overloading

A *class* may be declared with multiple type signatures, each
specifying a distinct set of argument types and a return type. The
class has a single implementation; only the type checking is
overloaded.

Overloading is enabled explicitly by `:- class` / `:- open_class`. A
`:- function` / `:- open_function` declaration with more than one
typed signature is rejected (`MultiSigOnFunction`, YCHR-16011):
`:- function` advertises a single signature (and may carry a
`requiring` clause for bounded polymorphism), `:- class` an overload
set. Mixing the two forms for the same name+arity is `MixedDeclKinds`
(YCHR-16012).

A single-signature `:- class` is legal but verbose; idiomatic
single-signature code uses `:- function`.

### Declaration syntax

```prolog
:- class
    ('+'(int, int) -> int),
    ('+'(float, float) -> float).
```

Multiple comma-separated typed declarations with the same name and
arity are grouped into a single overloaded class definition. An
`:- open_class` extends across modules: other modules may add
signatures via `:- extend_class_type` and equations via
`:- extend_class`.

An untyped declaration (`:- function size/1.`) desugars to the
all-`any` signature for type checking (§Defaults) but — a deliberate
carve-out from that equivalence — does not count as a *typed*
signature for declaration grouping: it contributes nothing to the
"more than one signature" rule that separates `:- function` from
`:- class`. An untyped `:- function f/1.` and a typed
`:- function f(int) -> int.` for the same name and arity do not
trigger `MultiSigOnFunction`; only two or more *typed* declarations
would.

### Resolution

At a call to an overloaded class the checker filters the declared
signatures by consistency with the known argument types:

- If all surviving signatures are **equal after substitution** — in
  the common case, exactly one is consistent: the checker applies
  that signature, unifying argument types and propagating the return
  type. This is the "narrow when unambiguous" behavior.
- If **no** signature is consistent: `NoMatchingOverload` (YCHR-60006).
- If **multiple distinct** signatures are consistent (ambiguous): the
  checker succeeds silently without propagating type information.

Filtering uses consistency, not equality: an argument typed `any` or
an unbound *flexible* type variable is consistent with any declared
type. It considers argument types only; the call's expected result
type never disambiguates an overload, deliberately.

Resolution is a residual check (§Type Checking Procedure): retried as
solving adds information, it fires only when all surviving candidates
are equal after substitution, succeeds silently if still ambiguous when
solving ends, and reports an empty candidate set whenever that occurs.

### When arguments are not yet resolved

The check depends on the variable's flavor (§Type variables and
instantiation):

- **Flexible** type variables (use-site fresh variables with no
  concrete type yet) are consistent with every declared type; the
  check succeeds silently, preserving the gradual guarantee:
  unannotated code produces no errors.

- **Rigid** type variables (declaration type parameters at
  implementation sites — function equations and rule-head occurrences
  of typed polymorphic constraints) are inconsistent with every
  declared concrete type (§Rigid and flexible type variables). If no
  declared signature is consistent with the rigid tvar — no ambient
  signature from a `requiring` clause covers it, and no guard-derived
  evidence has pinned it to a concrete type (§Guard-Derived Type
  Evidence) — the call fails with `NoMatchingOverload` (YCHR-60006).
  This closes the soundness gap that would let `foo(T, T) -> bool`
  silently type-check while calling an overloaded `>` at `T` in its
  body, and the analogous gap for the rules of a polymorphic
  constraint.

### Equation checking

Each equation of an overloaded class is checked against the declared
signatures and accepted if it type-checks under at least one, with its
parameters typed by that signature's argument types and its RHS
checked against its return type. An equation that type-checks under
none is `NoMatchingOverload` (YCHR-60006).

During a per-signature attempt, a guard's evidence fact that
contradicts the candidate signature's types counts as failure under
that signature, and no inaccessible-branch warning is emitted for the
attempt (§Guard-Derived Type Evidence). This is how a
refinement-predicate guard selects its signature: below, `size(N) | integer(N) -> N`
fails under `size(string) -> int` and checks under `size(int) -> int`.
An equation whose guards contradict *every* signature checks under
none — the `NoMatchingOverload` error, not a warning.

Failing to check under a signature is the *only* thing that moves the
search on: an attempt that raises a runtime error — a bug in the
checker, not the program — aborts the check and surfaces as that error
rather than counting as one more signature that did not fit.

### Example

```prolog
:- chr_type color ---> red ; green ; blue.

:- class
    (size(int) -> int),
    (size(string) -> int).

size(N) | integer(N) -> N.
size(S) | string(S) -> string_length(S).

:- chr_constraint foo(color).
foo(X) <=> R is size(X).   %% Error: no matching overload
                            %% (color is not int or string)
```


## Bounded Polymorphism

A function or constraint declaration may carry a `requiring` clause
that constrains its type variables by *required signatures* on other
functions. A use of the bounded declaration is well-typed only at
substitutions of those type variables for which every required
signature is satisfied by an existing declaration.

This section describes the mechanism for functions; §Bounded
constraints collects the adaptations for `:- chr_constraint`
declarations.

`requiring` and `refining` (§Refinement predicates) are mutually
exclusive: they are operators of equal priority, so a signature
carrying both is a syntax error in either order.

This is ad-hoc polymorphism without elaboration: the checker verifies
that the required operations exist at the inferred type but never
modifies the program or threads runtime evidence. Dispatch stays
dynamic — the runtime selects a matching equation by pattern matching,
exactly as for unbounded functions.

The "type-class" `requiring` abstracts over is implicit (YCHR's
`:- class` keyword is unrelated — explicit multi-signature
overloading, §Signature Overloading — and there is no `:- instance`
declaration). Its name is the required-function name itself:
`requiring '>'(T, T) -> bool` plays the role of `Ord T` in classical
type-class systems, and the declared signatures of `>` the role of
`Ord` instances.

### Declaration syntax

The `requiring` clause is a comma-separated list of *bound signatures*
`name(τ₁, ..., τₙ) -> τᵣ`:

```prolog
:- chr_type pair(K, V)  ---> pair(K, V).
:- chr_type option(A)   ---> none ; some(A).

:- function max(T, T) -> T requiring '>'(T, T) -> bool.

:- function clamp(T, T, T) -> T requiring
    '>'(T, T) -> bool,
    '<'(T, T) -> bool.

:- function lookup(K, list(pair(K, V))) -> option(V) requiring
    '=='(K, K) -> bool.
```

`requiring` is allowed on `:- function`, `:- open_function`, and
`:- chr_constraint` (§Bounded constraints); *not* on `:- class` /
`:- open_class` (`RequiringOnClass`, YCHR-15005) nor on
`:- extend_class_type` (`RequiringOnExtendClassType`, YCHR-15006). The
two features are orthogonal: `requiring` for bounded single-signature
declarations, `:- class` for explicit multi-signature overloading.

A bounded `:- open_function` already has an extensibility story: its
instance set is determined by what its bound-named functions are
declared for. To extend the types at which it works, declare new
instances of its bound-named functions — not new ground signatures of
the bounded function itself. A type extension on a bounded open
function draws *two* diagnostics on the offending
`:- extend_class_type`: `ExtendClassTypeOnFunction` (YCHR-16013, type
extensions must target an `:- open_class`) and
`ExtendTypeOnBoundedFunction` (YCHR-16007, the target's instance set
is determined by its bound). Both are accurate; the redundancy is
intentional so each rule fails loudly on its own terms.

Equation extensions via `:- extend_function` *are* allowed on bounded
open functions. The new equation is checked under the same bound as
the original equations — the required signatures are ambient in the
extension's checking context exactly as in the original module's — and
the extending module needs no additional declaration.

A `:- chr_constraint` declaration may carry the same clause:

```prolog
:- chr_constraint sorted(list(T)) requiring '<'(T, T) -> bool.
```

Bounds always name *functions*, never constraints.

Every function named in a `requiring` clause must be declared or
imported; a bound naming an undeclared function is
`UnknownBoundFunction` (YCHR-16009). A bound may name an *untyped*
declaration: per §Defaults it desugars to the all-`any` signature, so
the bound is vacuously satisfied at every substitution — opting
callers out of bound discipline for that function, exactly like an
explicit `g(any, ..., any) -> any` signature.

### Type-variable scoping

Type variables in a `requiring` clause are those of the enclosing
declaration's signature (function or constraint), under the same
implicit quantification. Every variable in the clause must also appear
in the primary signature; one appearing only on the clause side is
`UnboundBoundVariable` (YCHR-16008).

The bound clause does not introduce its own quantifier; the bound
signatures are not first-class types and cannot be referenced
elsewhere.

A `requiring` clause with no type variables is permitted: use-site
checking runs with `σ` the identity, so the bound is a one-shot check
that the named declarations exist, costing one overload-resolution
lookup per bound per call.

### Bound graph

The *bound graph* of a program has one vertex per declared function
and constraint, and an edge from `f` to `g` whenever `g` appears in
`f`'s `requiring` clause. Edges always point at functions. The graph
must be acyclic; a cycle is rejected at declaration time as
`BoundCycle` (YCHR-16010).

### Instances

A *substitution* σ for a bounded declaration maps each of its type
variables to a (possibly polymorphic) type. σ is **admissible** when,
for every bound signature `gᵢ(σᵢ₁, ..., σᵢₖᵢ) -> ρᵢ` in the clause,
the substituted form `gᵢ(σ(σᵢ₁), ..., σ(σᵢₖᵢ)) -> σ(ρᵢ)` is consistent
with at least one declared signature of `gᵢ` (after fresh-renaming
that signature's own type variables).

"Consistent with" is §Consistency extended with the type-variable
rules of §Type variables and instantiation: structural consistency on
type constructors, the absorbing rules for `any`, and unification of
type variables under the "concrete types bind, `any` does not"
discipline. Both the substituted bound and the fresh-renamed candidate
signature may contain free variables; consistency between them is
unification under those rules. Consequences:

- A declared signature of `gᵢ` that uses `any` is consistent with
  every shape, so it admits every substitution. Declaring
  `g(any, ..., any) -> any` opts every caller bounded by `g` out of
  bound discipline for `g`.
- Type variables in declared signatures of `gᵢ` are quantified per
  signature and freshly renamed at each consistency check.
- The instance set is *not* materialized by the checker; it is a
  conceptual set defining when a use site is well-typed.

### Use-site checking

At a call `f(e₁, ..., eₙ)` to a bounded function with parametric
signature `f(τ₁, ..., τₙ) -> τᵣ` and bound clause
`g₁(...) -> ρ₁, ..., gₘ(...) -> ρₘ`:

1. Compute argument types `A₁, ..., Aₙ` from the call's expressions.
2. Instantiate `f`'s declared type variables with fresh unification
   variables, yielding a substitution σ.
3. For each `i`, check `Aᵢ ~ σ(τᵢ)` and propagate.
4. For each bound `gⱼ(σⱼ₁, ..., σⱼₖⱼ) -> ρⱼ`, check whether at least
   one declared signature of `gⱼ` is consistent with the substituted
   bound `gⱼ(σ(σⱼ₁), ..., σ(σⱼₖⱼ)) -> σ(ρⱼ)`. This is an *existence
   check*, not a propagating overload resolution: it asks whether some
   substitution makes the candidate declared signature and the
   substituted bound consistent (per §Consistency, extended with §Type
   variables and instantiation). Any unifier the check produces is
   discarded; a successful bound check never modifies σ, even when
   exactly one candidate matches. If no declared signature of `gⱼ` is
   consistent with the substituted bound, the checker reports
   `BoundUnsatisfied` (YCHR-60012).

   During the equation checking of an enclosing bounded function,
   "declared signature" includes the ambient signatures contributed
   by that function's bound (§Equation checking).
5. The call's result type is `σ(τᵣ)`.

Bound checks are residual checks in the sense of §Type Checking
Procedure — the propagation-free special case — solved together with
the equation's other type constraints, so each bound discharges as
soon as σ is ground enough to identify (or rule out) a consistent
declared signature. Since a bound check does not modify σ on success
(step 4), the order-independence argument of §Type Checking Procedure
covers it trivially: its discharge order relative to other constraints
cannot affect the final type assignment.

A bound whose substitution is still partial when solving ends — free
type variables no other constraint pinned down — succeeds silently per
the gradual guarantee: a check that lacks the information to fail is
not a failure.

### Equation checking

This is the rule for function equations; the analogous rule for
constraints — head-only ambient signatures during rule checking — is
in §Bounded constraints.

Equations of a bounded function are checked under an extended
declaration context: each bound signature `gᵢ(...) -> ρᵢ` is treated
as an additional declared signature of `gᵢ`, available *only while
checking this function's equations*. The checker then runs the
standard procedure of §Type Checking Procedure.

For each equation:

1. Fresh **rigid** type variables are allocated for each declared
   type variable of the function (§Rigid and flexible type
   variables).
2. The equation's parameters are typed under the substituted parameter
   types and the equation's RHS under the substituted return type.
3. Calls to bound-named functions inside the equation resolve against
   the bound's signatures alongside those functions' other declared
   signatures. The ambient signature's type variables are *not*
   fresh-renamed at each call: they are the enclosing function's
   declared type variables (the variables allocated in step 1). Fresh
   renaming applies only to the *other* declared signatures of `gᵢ`
   participating in resolution.
4. Calls to non-bound functions resolve through their ordinary
   declared signatures.

The ambient signatures are visible to *every* overload resolution and
bound check performed while checking this function's equations —
including the use-site bound checks of calls to other bounded
functions in the body: "declared signature" in §Use-site checking
reads "declared signature, plus any ambient signature contributed by
the enclosing equation's bound". So a bounded function whose body
calls another bounded function at its own type variables stays
polymorphic: the inner bound check sees the ambient signature and does
not force the outer type variables to a concrete instance.

An equation that fails under this extended context is reported with
the error code the ordinary checker would have produced (typically a
constructor mismatch or `NoMatchingOverload` (YCHR-60006)); no new
code exists for equation-level failures, since the bound only enlarges
the set of valid programs.

This mirrors how a type-class method body is checked under its class
constraints, without the dictionary-passing translation classical
formulations emit: the bound's "evidence" is purely a checker-time
enlargement of the available signatures, and nothing flows from it
into the emitted code.

### Bounded constraints

A bounded `:- chr_constraint` uses the same syntax, §Type-variable
scoping rules, §Bound graph membership, and §Instances semantics as a
bounded function. It differs in two places: where use-site checking
discharges, and what replaces §Equation checking.

#### Use sites

A bounded constraint's **body tells** (and goal tells) are its use
sites. Each tell allocates a fresh substitution σ for the constraint's
declared type variables (§Use-site checking step 2) and discharges the
bound as a residual constraint over that σ: σ is refined by unifying
the tell's argument expressions against the declared argument types
(step 3), and the bound discharges whenever σ is ground enough to
identify (or rule out) a consistent declared signature. There is no
return type, so step 5 is dropped.

A **rule-head occurrence** is not a use site but an *implementation
site*: it allocates rigid variables for the constraint's type
parameters (§Rigid and flexible type variables), establishes the
types of the head's variables through the declared argument types
(§Sources of Type Information §1), and *assumes* the bound rather
than discharging it — its required signatures enter the ambient
context for the rule (next subsection). A head occurrence's rigid
variable is pinned only by guard-derived evidence (§Guard-Derived
Type Evidence); whether the bound holds at a particular instance is
answered at the tells that discharge there.

Each occurrence — including several of the same bounded constraint in
one rule — gets its own fresh type variables. Order-independence and
silent success on a partial σ at use sites carry over verbatim.

#### Rule-level ambient signatures (replacing §Equation checking)

Constraints have no equations; the analogous implementation site is
the set of rules whose **head** mentions the bounded constraint. While
such a rule is checked, every bound carried by a bounded constraint in
its head contributes its required signatures to the ambient
declaration context. Body tells of the same bounded constraint do
**not** contribute — they are use sites that discharge the bound, not
implementations that assume it. The asymmetry mirrors §Equation
checking: for functions the equation body sees the bound as ambient
and the call site discharges it; for constraints the rule head sees it
as ambient and the body tell discharges it.

Type checking operates on the desugared AST, where every rule has the
shape `kept + removed + guards + body`. "Head" means `kept ∪ removed`;
both contribute their bounds as ambient, guards and body goals do not.

A rule body is entitled to *assume* the bound, exactly as a function
equation is. Consider the recursive rule of a polymorphic `sorted`:

```prolog
sorted([X, Y | Rest]) <=> X < Y | sorted([Y | Rest]).
```

The head allocates a rigid `T`, with `X : T` and `Y : T`. Without
ambient signatures, the guard's call to `<` at `(T, T)` would end with
an empty candidate set — a rigid variable is inconsistent with every
declared concrete signature — and report a spurious *rule-level*
`NoMatchingOverload`. Under the bound's contract the rule may assume
`'<'(T, T) -> bool` exists: the guard resolves against the ambient
signature, the rule is checked parametrically in `T`, and instance
errors fire where they belong — at the tells that discharge the bound
— as a type-class method body defers instance selection to its
callers.

The contract covers uses *at the bound's own variables*, nothing
more:

```prolog
:- chr_constraint str(string).
weird @ sorted([X | _]), str(S) <=> X < S | true.
```

The second head pins `S : string`, so the guard calls `<` at
`(T, string)`. The ambient `'<'(T, T)` does not cover it — `string` is
inconsistent with the rigid `T` — and the call is rejected
(`NoMatchingOverload`). Correctly so: the store chose `T` when the
matched `sorted` was told, independently of any `str`, so the rule
would compare a `T`-typed element against a string at whatever `T`
happens to be. A rule that handles only the string instance can say so
with evidence: a `string(X)` guard before the comparison pins
`T := string` (§Guard-Derived Type Evidence), after which `X < S`
resolves against the ambient signature at `(string, string)`.

When the bounded constraint occurs in both head and body of one rule
(the recursive `sorted` above), the body occurrence is still a use
site and discharges its own bound: its fresh variables bind to the
head's rigid `T` through the shared argument (a flexible binds to a
rigid), and the discharge resolves against the ambient signature the
head occurrence contributed — exactly as a bounded function's
recursive call discharges against its own ambient signature (§Equation
checking).

With several bounded constraints in one head, the ambient set is the
union of their bounds. Each head occurrence's type variables are
freshly allocated (§Use sites), so two occurrences of the same bounded
constraint contribute structurally identical bounds at distinct
variable identities and cannot collide.

#### Worked example — polymorphic `sorted`

```prolog
:- open_class ('<'(int, int) -> bool), ('<'(float, float) -> bool).
:- chr_constraint sorted(list(T)) requiring '<'(T, T) -> bool.

sorted([]) <=> true.
sorted([_]) <=> true.
sorted([X, Y | Rest]) <=> X < Y | sorted([Y | Rest]).
```

Rule checking: each head mentions `sorted`, so a rigid `T` is
allocated and the ambient signature `<(T, T) -> bool` is in scope. The
third rule's guard `X < Y` calls `<`; the two declared signatures are
inconsistent with the rigid `T`, so the ambient bound is the sole
surviving candidate, the resolution fires and the guard types as
`bool`. The body tell `sorted([Y | Rest])` is a use site: its fresh
variable binds to the rigid `T` through `[Y | Rest] : list(T)`, and
its bound discharges against the ambient signature.

Use site `sorted([1, 2, 3])` (in another rule's body, or as a
top-level goal): σ = (T := int); the substituted bound
`<(int, int) -> bool` is consistent with the declared signature.

Use site `sorted(["a", "b"])`: σ = (T := string); no consistent
declared signature; error `BoundUnsatisfied` (YCHR-60012).

Use site `sorted(L)` where `L : list(any)` or `L : list(α)` with `α`
free: σ leaves `T` partial; the bound succeeds silently per the
gradual guarantee.

A later module extending the open class with
`:- extend_class_type ('<'(string, string) -> bool).` extends the
admissible instance set of `sorted` with no edit to its declaration —
the open-set property of bounded polymorphism at the constraint level.
(The bound-named class must be `:- open_class` for cross-module
extension; a closed `:- class` fixes the instance set at its
declaration.)

### Coexistence with multi-signature overloading

Multi-signature overloading (`:- class` / `:- open_class`, §Signature
Overloading) and bounded polymorphism are exclusive: `:- class` cannot
carry `requiring` (`RequiringOnClass`, YCHR-15005). Their expressive
power overlaps for finite instance sets, but the checker behaves
differently: a class's signatures are checked independently at use
sites, and an equation that types under any one is accepted; a bounded
function has a single parametric signature — equations are checked
once, with the bound enlarging the context, and use sites verify the
bound at the inferred substitution.

Likewise for constraints: `:- chr_constraint` may carry `requiring`,
and there is no multi-signature form for constraints.

### Errors

The bounded-polymorphism error codes — `YCHR-16007` through
`YCHR-16010` and `YCHR-60012` — are catalogued in
`src/YCHR/Internal/Display.hs`. Equation checking introduces no new
codes (equations check under the enlarged context or fail with
existing ones), and the constraint case shares the function case's.

### Worked examples

**Example 1 — Polymorphic `max`.**

```prolog
:- class ('>'(int, int) -> bool), ('>'(float, float) -> bool).
:- function max(T, T) -> T requiring '>'(T, T) -> bool.

max(X, Y) | X > Y -> X.
max(_, Y)         -> Y.
```

Equation checking: `T` is rigid; `X : T`, `Y : T`. The guard `X > Y`
calls `>`; the declared `int` and `float` signatures are inconsistent
with the rigid `T`, so the ambient signature `>(T, T) -> bool` is the
sole surviving candidate, the resolution fires and the call types as
`bool`. The RHS `X : T` matches the return type `T`; both equations
check.

Use site `R is max(3, 4)`: σ = (T := int); the substituted bound
`>(int, int) -> bool` is consistent with the declared signature;
result type `int`; `R : int`.

Use site `R is max(red, green)`, for a declared
`:- chr_type colour ---> red ; green`: σ = (T := colour); the
substituted bound `>(colour, colour) -> bool` has no consistent
declared signature; error `BoundUnsatisfied` (YCHR-60012). (The
prelude's own `>` is declared over `string` as well as the two numeric
types, so a *string* use site of the prelude's `max` resolves — it is
the absence of a matching signature, not the argument being
non-numeric, that makes a bound unsatisfiable.)

**Example 2 — Multi-variable bound.**

```prolog
:- chr_type pair(K, V)  ---> pair(K, V).
:- chr_type option(A)   ---> none ; some(A).
:- function eq(int, int) -> bool.
:- function lookup(K, list(pair(K, V))) -> option(V) requiring
    eq(K, K) -> bool.

lookup(_, [])                             -> none.
lookup(K, [pair(K2, V) | _]) | eq(K, K2)  -> some(V).
lookup(K, [_ | Rest])                     -> lookup(K, Rest).
```

(The bound function is a fresh `eq/2` rather than the prelude's
`'=='`: the prelude declares `'=='(A, A) -> bool`, a polymorphic
signature every substituted bound is consistent with, which would make
an `'=='` bound vacuously satisfied and the error below unreachable.)

Equations are checked parametrically over `K` and `V`. The recursive
call `lookup(K, Rest)` is itself a use site; the recursion's σ is the
same as the outer equation's, so the inner bound is the bound under
that σ — trivially consistent during equation checking because the
bound's signatures are ambient.

Use site `R is lookup(3, L)` where `L : list(pair(int, string))`: σ =
(K := int, V := string); substituted bound `eq(int, int) -> bool` is
consistent with the declared signature; result type `option(string)`.

Use site `R is lookup(0.5, M)` where `M : list(pair(float, int))` and
no `eq(float, float) -> bool` has been declared: error
`BoundUnsatisfied` (YCHR-60012) for the substituted bound at K :=
float.

### Interaction with `any`

`any` interacts with bounds as with ordinary overloading:

- A use site whose argument types are `any` makes σ partial; the bound
  check succeeds silently and the call's result type remains a fresh
  flexible variable (the `any` arguments bind nothing), exactly as in
  ordinary overload resolution under unresolved arguments.
- A bound that names a function with an all-`any` declared signature
  is satisfied by every substitution: declaring
  `g(any, ..., any) -> any` opts every caller bounded by `g` out of
  bound discipline for that `g`.
- A type variable that meets `any` does not bind (§Type variables and
  instantiation); a bound depending on it stays unresolved until
  concrete information arrives, then is checked.

## Soundness

The type system is gradual in the sense of Siek & Taha. Its
correctness properties:

1. **Soundness of the fully-typed fragment**: if no expression in a
   program is typed `any` and the program type-checks, then at runtime
   every value that is *bound* is bound within its static type
   (standard progress + preservation, restricted to that fragment).
   The claim is about values: a term that is still an unbound logical
   variable holds no value yet and falls under §No mode checking
   instead. The *`any`-introduction forms* — an `any`-annotated or
   untyped declaration position, a host call, an unknown constructor,
   an evaluable-headed term in structural position (§Expression
   Typing) — delimit exactly where the guarantee stops: a program that
   binds a symbolic `1 + 1` with `=`, calls the host, or forges an
   unknown constructor has left the fragment at that expression.

   A `refining` clause is a second trusted boundary, alongside a host
   call's declared signature (§Refinement predicates). The checker
   takes the declaration's word that a successful call proves its
   argument's type; nothing checks that against the equations, and for
   a host-backed predicate there would be nothing to check it against.
   A wrong `refining` clause is a wrong axiom, and property 1 holds
   only up to the ones the program declares.

2. **The gradual guarantee**: replacing any type annotation with `any`
   (making the program less precise) never introduces new type errors;
   conversely, making types more precise can only add errors, never
   remove them. Adding type annotations is therefore always safe and
   never breaks a working program.

Rigid type variables (§Rigid and flexible type variables) are what
make property 1 hold for polymorphic declarations whose
implementations use overloaded operations:
`:- function foo(T, T) -> bool.` with an equation body calling an
overloaded operator at `T` cannot type-check without a `requiring`
clause covering that operation or an evidence guard pinning the
variable (§Guard-Derived Type Evidence). Without rigidity such a
program type-checked silently (every declared signature filtered as
"consistent" against the unbound flexible variable for `T`) but could
fail at runtime when called at a type with no equation of the
overloaded operator. The same holds for polymorphic *constraints*:
rule-head occurrences allocate per-occurrence rigid variables, so
`:- chr_constraint foo(T, T). foo(X, Y) <=> X > Y.` is rejected
(`NoMatchingOverload` at the rigid `T`) unless the declaration carries
a `requiring` clause or an evidence guard covers the operation.
Multi-head idioms relying on cross-occurrence agreement (transitivity
of a polymorphic `leq(T, T)`) stay accepted through `GuardEqual`
evidence, which assumes exactly the agreement runtime matching
guarantees. Rigidity does not constrain unannotated programs: without
type annotations the enclosing declaration has no type variables to
make rigid, so the gradual guarantee still holds.

Property 1 is exercised by randomized property tests
(`test/YCHR/TypeSoundnessTest.hs`, generator under
`test/YCHR/TypeSoundness/`). They generate programs well-typed by
construction, run them through the real pipeline, and instrument every
generated rule with calls to a host function that snapshots the
runtime values it is handed and checks them against the static types
the generator gave those positions. A host call rather than an
in-language assertion is what lets it observe a position typed by a
*rigid* variable, where there is no static type an assertion could be
declared at.

The generated programs include the polymorphic machinery this section
credits: parametric algebraic types, constraints with type parameters,
per-occurrence rigid variables at every head, the skolem merge a
shared head variable forces, guard-derived evidence in each of its
forms, and `requiring` bounds with the ambient signatures a rule head
contributes. Since the generator models rigidity itself, a program it
believes well-typed that the checker rejects is a failure, not a
discarded sample — that disagreement is the defect the tests look for,
and one has already been found and fixed (the parameter pinning of
§What evidence does).

Two regimes are covered, as two properties. In the *closed* one every
argument position is ground. In the *open* one some positions are
declared willing to hold a term not yet bound, the goal stores query
variables at them, and later rules bind those variables — so a value
arrives from a different unit than the one that stored it. The open
property checks the claim in its sharpest form: a query variable
passed unbound into a declared position must, if anything binds it, be
bound within that position's type, however many units and
reactivations it passed through. A term still free at the end is not a
violation — that is the mode axis below, whose discipline the
generator observes.

### Bounded polymorphism

Bounded polymorphism preserves the gradual guarantee (property 2):

- **Conservativity over signature overloading.** Replacing a bounded
  declaration with an enumerated multi-signature declaration over
  the same instance set produces a program with the same set of
  accepted use sites at those instances.
- **Conservativity over `any`.** Replacing every type variable in a
  bounded declaration with `any` (and consequently every bound with
  the all-`any` form of its named function) produces a program that
  type-checks unchanged — the standard "more `any` never adds errors"
  property.
- **No elaboration.** The checker does not modify the AST: the bound
  is verified at each use site, and once verified no residual evidence
  is needed at runtime, since dispatch is dynamic (pattern matching
  across equations).

Bound checking is expressed as ordinary use-site overload resolution
and inherits its confluence and gradual properties. Bounds and
guard-derived evidence (§Guard-Derived Type Evidence) are the two
discharge mechanisms for an operation at a rigid variable: a bound
proves it statically at every caller, evidence proves it dynamically
on the guarded path.

The same properties hold for bounded constraints with no new soundness
argument: rule-level ambient signatures structurally mirror
equation-level ones, and the use-site mechanism is shared. The union
of several bounded constraints' ambient signatures in one rule is
sound because each occurrence's type variables are freshly allocated
per rule (§Use sites), so contributed signatures cannot collide on
shared variable identities.

### No mode checking

YCHR types terms; it does not track their *mode* — ground, partially
instantiated, or still a free variable. A declaration `c(int)` says
the `X` in `c(X)` is a term which, whenever bound, is an integer; it
does not say `X` is bound, and nothing checks the mode preconditions
of operations that require one.

("Mode" is the runtime instantiation state of a term, in Mercury's
sense — a different axis from the entirely static *type-variable*
instantiation of §Type variables and instantiation.)

The store is what makes the gap reachable. A constraint may be told
with an argument that is still unbound; another unit binds it later;
and in between, any rule matching that constraint sees a free
variable in a position whose declared type is `int`:

```prolog
:- chr_constraint c(int), mk(int), out(int), later(int).

m @ mk(_)    <=> c(E), later(E).   % c is stored while E is unbound
l @ later(E) <=> E = 1.
r @ c(N)     <=> N > 0 | out(N).   % N is E, still unbound, when r is first tried
```

This type-checks with no errors and no warnings, and `r` reaches
`prelude:'>'/2` with no value at all — not a value of the wrong type.
The same situation is described from the language side in [Tell-time
evaluation errors](language.md#tell-time-evaluation-errors):
evaluation is eager, with no auto-suspension and no symbolic fallback.

What happens next is decided at run time, not by the checker. `>`
raises an *instantiation* failure, and a rule guard is exactly where
such a failure is caught ([Soft guard
failure](language.md#soft-guard-failure)): the guard yields false, `r`
does not fire, `l` binds `E`, the binding reactivates `c`, and `r`
fires on the later activation with `N = 1`. So the program does
produce `out(1)` — the mode gap is *tolerated* at a guard, not closed.
The same `N > 0` in a rule body or an `is` expression is a hard
`YCHR-60001`, because only guards are retried.

The runtime also names the gap where it can. When a free variable
reaches a *function equation's* pattern test rather than a host call,
the `YCHR-60001` message reads "argument *K* of `M:f/N` is not
sufficiently instantiated to select an equation" instead of "no
matching equation in `M:f/N`" — the mode failure said out loud, at the
one place the compiler can see it.

A boundness guard makes the same wait explicit:

```prolog
r @ c(N) <=> integer(N), N > 0 | out(N).
```

`integer(N)` is statically redundant — `N` is already declared `int`,
and as an evidence form (§Evidence forms) it contributes a fact the
declaration already gave — but operationally it states the
precondition: it fails on a free variable, so the rule does not fire
until `E` is bound. Since soft guard failure gives the unguarded rule
the same schedule, the conjunct is a matter of style, not a
requirement: write it when the wait is part of what the rule means,
leave it out when the delay is incidental. That a conjunct can be
redundant for typing and load-bearing for execution is exactly the
mark of the axis the type system does not cover.

`var/1`, `nonvar/1` and `ground/1` serve the same purpose, and are
deliberately *not* evidence forms (§Non-forms): their success entails
a boundness fact, not a typing one — the same separation stated from
the other side.

None of this is mode *checking*. Nothing warns that `r` may be tried
unbound, nothing proves it is ever retried — a variable no stored
constraint observes is never bound and the rule delays for ever,
silently. The type system stays silent on the mode axis; the runtime
simply fails more gently at guards.

This is a scope boundary, not an oversight: a mode system is a second
analysis over the same programs, with its own annotation burden, and
in CHR a constraint argument's mode is genuinely flow-dependent — the
same argument position can be free in one activation of a rule and
bound in the next.

Since YCHR erases types completely (no runtime casts, no blame
tracking), the checker cannot guarantee that programs using `any` are
type-safe at runtime: it catches inconsistencies where it has enough
information and is silent where it does not — the standard trade-off
of gradual typing without runtime enforcement.

The ingredients behind these properties:

- The consistency relation is reflexive and symmetric but not
  transitive, as expected for gradual typing.
- Consistency with `any` is absorbing: `any ~ τ` always succeeds.
- Constraint solving is order-independent in the precise sense of
  §Type Checking Procedure: acceptance and the final type assignment
  do not depend on solving order; only error attribution may vary.
  Nothing narrows `any`, so no directed step sits outside this
  guarantee.
- Every evidence form satisfies the evidence criterion: its
  operational success entails the typing fact it contributes, so
  code checked under evidence runs only in executions where the
  fact holds (§Guard-Derived Type Evidence).
- The fully-typed fragment reduces to standard HM with algebraic
  data types, extended with local evidence assumptions at
  implementation sites.
- The guarantee is about bound values. Terms that are still free
  variables are governed by mode, which the type system does not
  track (§No mode checking).
