# YCHR Type System Specification

> **Audience:** readers annotating a program with types, and anyone
> working on the checker itself.
> **You will:** find the type language, the consistency rules, overload
> resolution, and bounded polymorphism, in specification detail.
> **Skip if:** you just want to add a few annotations — the how-to
> [Add types to a program](../how-to/add-types.md) and tutorial
> [Functions, types, and lambdas](../tutorials/04-functions-and-types.md)
> cover the common cases.

This document specifies the YCHR static type system: a gradual,
consistency-based type checker for CHR programs. The type checker
operates on the desugared AST. Types are erased at runtime; the
checker produces errors without transforming the program.


## Overview

The type system catches type inconsistencies statically while
remaining optional: programs that omit type annotations are accepted
without errors. One uniform type language covers constraints and
functions. The checker takes a `Desugared.Program` and produces a list
of type errors; type errors prevent compilation from proceeding.


## Types

The type language is defined by the following grammar:

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
- **`any`** — the dynamic type. Consistent with every other type.
  Serves as the escape hatch for gradually typed code.

The `bool` type is not built-in. It is an algebraic type declared in
the prelude as `bool ---> true ; false`.

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
eliminated only by (host-backed) functions. It is declared with a
dedicated `:- opaque_type` directive and has **no data constructors**:

```prolog
:- opaque_type set(X).
:- opaque_type handle.
```

An opaque type definition introduces a type constructor name with zero
or more type parameters and nothing else. Because it has no data
constructors, a value of an opaque type cannot be built or
pattern-matched structurally within CHR source; it can only be produced
as the declared return of a function and consumed by passing it to a
function whose parameter has that type:

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
- The parameters need not appear anywhere — *phantom* parameters are
  allowed (an opaque type has no fields in which a parameter could
  occur).
- A constructor body (`---> ...`) is a syntax error
  (`YCHR-15016`): opaque types cannot have data constructors.
- `T` must not collide with a base/reserved type name or another
  visible type.

**Consistency (nominal).** An opaque type `T(τ₁, ..., τₙ)` is just a
type constructor application, so it obeys the ordinary `[C-Con]`,
`[C-Any-L]`, `[C-Any-R]`, and `[Inconsistency]` rules below. Concretely,
`T` is consistent only with itself (parameters checked pairwise) and
with `any`; it is inconsistent with every other type constructor and
with every base or function type. This is exactly the nominal behavior
desired: distinct opaque types never unify, and an opaque type never
unifies with its representation.

**Abstraction.** An opaque type's name `T` is a *type-constructor* name,
not a data constructor — exactly like an algebraic type's name (`list`,
`option`). It is meaningful only in *type-expression* position (function
and constraint signatures, other type declarations). Writing `T(...)` in
*term* position — `X = set(1)`, or `set(X)` in a guard, head, or equation
pattern — is not a way to build an opaque value: `T` is an unknown data
constructor there, so the term is typed `any` and, like every unknown
constructor, draws an `UndeclaredDataConstructor` warning (`YCHR-20101`).
The intended way to obtain or consume an opaque value is to call a
function declared to return or accept `T(...)`. As with algebraic types,
the soundness of the typed fragment rests on the gradual guarantee, not
on a syntactic ban: a forged `set(1)` typed `any` can still flow into a
`set`-typed position, just as a nonsensical `list(1)` can flow into a
`list`-typed one.

**Visibility.** Opaque types obey the module type-export/import rules
(see [`language.md`](language.md)). They share the type namespace with
algebraic types, so they are exported and imported with the same
`type(T/n)` form (there is no separate opaque-export syntax). An opaque
type has no constructors, so the `type(T/n, [...])` allowlist form is not
useful for one — naming a constructor there is rejected as unknown
(`YCHR-20008`).

### Function types

Function types describe first-class callable values (lambdas and
function references):

```
fun(int, int) -> bool end
fun(A) -> A end
```

A function type `fun(τ₁, ..., τₙ) -> τᵣ` represents a callable
taking `n` arguments of types `τ₁, ..., τₙ` and returning a value of
type `τᵣ`.

In *concrete* syntax a function type is closed by an `end` keyword —
`fun(int, int) -> bool end` — mirroring lambda syntax; the `end`
delimits the return type and is not part of the abstract grammar
above. This document writes types in abstract syntax (no `end`)
except inside program examples.

### Type variables

Type variables (written as uppercase identifiers in CHR source) are
implicitly universally quantified over the enclosing declaration
(constraint or function). There is no explicit quantification and no
rank-n polymorphism.

Each use of a declared constraint or function in a rule or equation
instantiates its type variables with fresh unification variables.


## Defaults

Missing type annotations default to `any`:

- A constraint declared as `name/arity` (without type annotations)
  has all argument types defaulting to `any`.
- A function declared as `name/arity` (without type annotations) has
  all argument types and the return type defaulting to `any`.

For example, `:- chr_constraint leq/2` is equivalent to
`:- chr_constraint leq(any, any)`. The equivalence is semantic —
type checking treats the two forms identically. For the one place
where an untyped declaration is *not* interchangeable with its
all-`any` form (declaration grouping for overloaded classes), see
§Signature Overloading.


## Consistency

The type system is based on *consistency checking* in the style of
gradual typing. Two types are consistent (written `τ₁ ~ τ₂`) if they
could be the same type up to the presence of `any`. This is weaker
than equality: consistency allows `any` to stand in for any type
without committing to a specific choice.

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

For the purposes of this rule, a base type counts as a nullary type
constructor, and the function-type former `fun/n` counts as a type
constructor distinct from every base type and every other
constructor. For example, `int ~ bool`, `option(int) ~ list(int)`,
and `int ~ fun(int) -> int` are all errors.

Type variables are deliberately absent from these rules: which types
bind them and how they interact with `any` is defined by the meet
table in §Type states below.


## Type Propagation and Consistency

The type checker infers types for source variables by propagating
type information through constraints. Types flow into variables from
declarations (head constraints, function signatures) and between
variables through unification and `is` expressions. When two types
meet, the checker performs a *consistency check*, per the rules of
the previous section.

### Type states

Every type the checker manipulates is in exactly one of four states:

- **`any`** — the dynamic type. A *variable* is typed `any` only
  when a declaration says so (an `any`-annotated or untyped argument
  position). Certain *expressions* are also typed `any`; the
  complete list of `any`-introduction forms is in §Soundness.
- **Concrete** — a base type, an algebraic or opaque constructor
  application, or a function type.
- **Flexible** — an unsolved unification variable. Instantiating a
  declared signature at a use site allocates fresh flexible
  variables for its type parameters, and a source variable with no
  declaration-derived type is likewise typed by a fresh flexible
  variable. There is no separate "unknown" state.
- **Rigid** — a function's own type parameter while that function's
  equations are checked (§Rigid and flexible type variables). A
  rigid variable behaves as an opaque type constant (a skolem): it
  stands for an arbitrary caller-chosen type about which nothing may
  be assumed.

When two types meet — through unification, argument checking, or any
other consistency check — the outcome is:

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
flexible variables; `any` binds nothing. The single principle behind
the table:

> **`any` never binds a type variable and never propagates; it is
> only checked against. A variable's type is `any` only when a
> declaration says so.**

A variable typed by several declaration positions keeps the most
informative source: if any source is concrete or a type parameter,
that source determines the variable's type and the `any` positions
are merely checked successfully. The variable is typed `any` only
when every source is `any`.

There is one directed exception to the inertness of `any`, described
in the next subsection: `R is e` refines an `any`-typed `R` when
`e`'s type is concrete.

### The role of `any`

The `any` type is the escape hatch for gradual typing. It is
consistent with every other type, but it is inert in propagation:

- A variable whose declaration positions all use `any` (e.g. an
  argument of a constraint declared `foo(any)`, or of an untyped
  constraint) is typed `any`. If the same variable also has a
  concrete or polymorphic declaration source, that source wins and
  the `any` positions are merely checked (§Type states).
- When a variable with a known concrete type meets `any` through
  unification or a consistency check, the variable **retains** its
  concrete type. The check succeeds but the concrete type is not
  replaced by `any`.
- When `any` meets a flexible or rigid type variable, the check
  succeeds and the variable is **not** bound. This prevents `any`
  from leaking through shared type parameters — or through chains of
  local variables — and masking real inconsistencies. (See §Type
  variables and instantiation.)

The key consequence: `any` stops type propagation. A variable typed
as `any` will not carry type information from one position to
another, and `any` never overwrites a type established elsewhere.

Exactly one construct replaces `any` with something more precise:
`R is e`. Because `is` *evaluates* its right-hand side, the inferred
type of `e` is authoritative for `R`'s value, so a concrete RHS type
refines an `any`-typed `R` to that type. The reverse never happens —
an `any`-typed RHS leaves the LHS's type untouched (an `any`-typed
variable stays `any`; a flexible variable stays flexible). Plain
unification (`=`) has no such power: it checks against `any` without
binding anything (§Sources of Type Information §5).

### Example: propagation through a shared variable

```prolog
:- chr_constraint foo(int), bar/1.
rule @ foo(X) <=> bar(X).
```

- `X : int` (from `foo(int)` in the head).
- Body `bar(X)`: `X` is `int`, so `bar` is called with an `int`
  argument. The type propagated from the head to the body through
  the shared variable `X`.

### Example: `any` stops propagation

```prolog
:- chr_constraint foo(any), bar(int), baz(bool).
foo(X), bar(Y), baz(Z) <=> X = Y, X = Z.
```

- `X : any` (from `foo`), `Y : int` (from `bar`), `Z : bool`
  (from `baz`).
- `X = Y`: `any ~ int` → succeeds. `Y` remains `int`.
- `X = Z`: `any ~ bool` → succeeds. `Z` remains `bool`.

No error. The `any` in `foo` makes both checks involving `X`
succeed. Note that `Y` and `Z` retain their declared types — the
`any` from `X` does not propagate to them. If the rule also
contained `Y = Z`, the checker would report an error for
`int ~ bool`.

### Example: inference through `is`

```prolog
:- chr_constraint result/1.
:- function double(int) -> int.
rule @ result(R) <=> R is double(1).
```

- `R : any` (from the untyped `result/1`, i.e. `result(any)`).
- `double(1)`: argument `1` has type `int`, consistent with the
  declared parameter type. Return type is `int`.
- `R is double(1)`: the RHS type is concrete, so the `is` refines
  `R` from `any` to `int` (see The role of `any`).
- `result(R)`: `R` is `int`; the declared argument type is `any`, so
  the check succeeds trivially.

`R is e` flows the inferred type of `e` into `R` regardless of `e`'s
syntactic shape. In particular, when `e` is a bare variable the LHS
picks up that variable's inferred type:

```prolog
:- chr_constraint go(A, A).
go(R, S) <=> Sum is 1 + 1, R is Sum, S = "hello".
```

- `Sum is 1 + 1`: the RHS is an evaluated position, so `1 + 1` is
  typed by the declared signature of `+`, giving `int`. `Sum` is a
  local variable — a fresh flexible — and binds to `int`.
- `R is Sum`: `R` acquires type `int` from `Sum`. Because the head
  ties `R` and `S` to the same type parameter `A`, `S` is now `int`
  too.
- `S = "hello"`: `int ~ string` fails consistency.

Note the `is`, not `=`, in the first goal. `=` is structural
(§Expression Typing): `Sum = 1 + 1` binds `Sum` to the symbolic
compound `prelude:+(1, 1)`, whose type *as a term* is `any` — and
`any` does not propagate, so `Sum` would stay flexible and no error
would be reported. Use `is` when you want the arithmetic — and the
type.

The cross-argument flow above depends on the polymorphic signature:
if `go/2` were untyped, `R` and `S` would each independently be
typed `any`, with no shared type parameter linking them. `R is Sum`
would still refine `R` to `int`, but nothing would carry that type
to `S`, and `S = "hello"` would pass. A typed or polymorphic
signature is what keeps the cross-argument channel open.

Note that a well-typed expression can still fail at runtime. A
function call type-checks against the function's declared return
type, but the runtime raises `YCHR-60001` if no equation matches the
actual arguments. For example, given a partial function

```prolog
:- function half(int) -> int.
half(0) -> 0.
```

`R is half(5)` type-checks with `R : int` (the declared return
type), yet at runtime it raises `YCHR-60001` ("no matching
equation") because no equation covers `5`. The type checker doesn't
model which inputs an equation set actually covers; that is only
enforced at evaluation time.


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
  consistency checks. These are solved as a set by ordinary
  unification under the meet table of §Type states.
- **Residual checks** — overload resolutions (§Signature Overloading
  §Resolution) and bound checks (§Bounded Polymorphism §Use-site
  checking). A residual check is *pending* until it can act, under
  the following discipline:

  1. A pending overload resolution **fires** — commits to a declared
     signature, unifying argument types and propagating the return
     type — only when all of its surviving candidate signatures are
     equal after substitution (in the common case: exactly one
     candidate survives). Firing adds information and may enable
     other pending checks; solving repeats until no pending check
     can fire.
  2. A pending check whose candidate set becomes empty reports an
     error (`NoMatchingOverload` for resolutions, `BoundUnsatisfied`
     for bound checks) whenever that happens.
  3. A pending check that is still ambiguous when solving ends
     succeeds silently — the gradual behavior. Its result type stays
     flexible and nothing is propagated.
  4. A fired commitment is never retracted; if later information
     contradicts it, the contradiction surfaces as an ordinary
     inconsistency error.

  Bound checks are the propagation-free special case: they never
  modify the substitution, so for them "firing" is merely the
  existence check of §Use-site checking.

Solving is order-independent in the following precise sense: the set
of accepted programs and the final type assignment do not depend on
the order in which constraints are gathered or pending checks are
examined; only error attribution (which check reports first) may
vary. The reason is monotonicity: solving only ever adds
information, so a pending check's candidate set only shrinks. A set
can never grow back from one candidate to several, so the signature
a check fires on is uniquely determined no matter when it fires; and
if a check's chosen candidate would later have been eliminated,
every examination order rejects the program — early firing surfaces
the contradiction through the propagated types, late examination
through an empty candidate set.

### Type variables and instantiation

When a declared constraint or function is used, the checker
instantiates its declared type with fresh unification variables. For
example, if `member(A, list(A))` is used twice in a rule, each use
gets independent fresh variables (`a₁, list(a₁)` and `a₂, list(a₂)`).

Type variables unify normally via substitution. When a type variable
meets `any`, the consistency check succeeds but the type variable is
**not bound**. Only *solid* types — concrete types and rigid
variables — bind flexible type variables; `any` binds nothing (see
the meet table in §Type states). This prevents `any` from leaking
through shared type variables and masking real inconsistencies.

For example, given `:- chr_constraint foo(A, A).` and a use
`foo(X, Y)` where `X : any` and `Y : int`:

- Fresh `α` for `A`.
- `α ~ any` (from X): succeeds, `α` unchanged.
- `α ~ int` (from Y): `α = int`.

The concrete type `int` is preserved despite the `any` input.

Unconstrained type variables remaining after solving are not errors.
They represent genuinely polymorphic usage.

#### Rigid and flexible type variables

The checker distinguishes two flavors of unsolved type variable:

- A **flexible** type variable is a fresh unification variable
  allocated at a use site of a declared constraint or function. It
  acts as a normal HM unification variable: it can be bound to a
  concrete type by later constraints, it succeeds silently in
  overload resolution when its declared counterpart is also unbound
  (see §When arguments are not yet resolved), and it satisfies the
  gradual guarantee.

- A **rigid** type variable is a *function*'s own type parameter,
  in scope while checking that function's equations. A rigid
  variable behaves as an opaque type constant (a skolem): it is
  consistent with itself, with `any` (nothing binds), and with
  flexible variables — which it *binds*, so rigidity travels through
  intermediate flexibles (calling `id(A) -> A` at a rigid `T` yields
  a result of type `T`, not an unconstrained variable). It is
  inconsistent with every concrete type and with every distinct
  rigid variable; it never silently matches a declared concrete
  type. A polymorphic
  function-equation body that uses an overloaded operation at a
  rigid tvar must therefore resolve through an ambient signature
  contributed by the function's `requiring` clause — without one
  the call fails with `NoMatchingOverload` (YCHR-60006).

Rigidity applies only to **function equations**. Constraint head
occurrences use flexible type variables, even when the constraint
itself is polymorphic: multi-head rules like transitivity of a
polymorphic `leq(T, T)` rely on cross-head type-variable
unification, which rigidity would prevent. The resulting soundness
gap for polymorphic constraints, and why it is accepted, is
discussed in §Soundness.

Rigidity is local to the function's own equation check. At every
use site of the same function, fresh *flexible* variables are
allocated by `copy_term`-style refresh, so callers retain the
gradual guarantee unchanged.


## Sources of Type Information

The following constructs generate type constraints within a rule or
function equation:

### 1. Constraint head positions

A constraint appearing in a rule head constrains its argument
variables. If `leq(int, int)` is declared and a rule head contains
`leq(X, Y)`, then `X : int` and `Y : int`.

### 2. Function equation parameters

A function's declared argument types constrain the parameter
variables. If `sign(int) -> result` is declared and an equation is
`sign(N) -> ...`, then `N : int`.

### 3. Function return type

The declared return type of a function constrains the right-hand side
of each equation. If `sign(int) -> result`, then the RHS of each
equation must be consistent with `result`.

### 4. `is` expressions (RHS to LHS flow)

In `R is expr`, the type of `expr` flows to `R`. This is a directed
assignment: the return type of the RHS expression determines the
type of the LHS variable. Concrete types flow; `any` does not — an
`any`-typed RHS leaves the LHS's type unchanged. When the LHS is
typed `any` by declaration, a concrete RHS type refines it (see The
role of `any`).

### 5. Unification (bidirectional)

In `X = Y` (body unification), type information flows
bidirectionally, following the meet table of §Type states: a
flexible variable binds to the other side's concrete (or rigid)
type, two flexible variables alias, and `any` on either side is
checked against without binding anything — a variable never becomes
`any` through unification, and an `any`-typed variable never loses
its `any`. If both sides have known concrete types, the checker
verifies they are consistent. Non-variable operands are typed
structurally (§Expression Typing).

### 6. Body constraint calls

A constraint call in a rule body constrains its argument expressions.
If `leq(int, int)` is declared and the body contains `leq(X, Z)`,
then `X` and `Z` must be consistent with `int`.

### 7. Body function calls

A function call in a rule body (or guard) constrains its argument
expressions and produces a result type. If `sign(int) -> result` and
the body contains `R is sign(X)`, then `X` must be consistent with
`int` and `R` gets type `result`.

### 8. Desugared guards (HNF synthetic guards)

Head Normal Form desugaring introduces synthetic guards:

- **`GuardMatch term functor arity`**: constrains `term` to be
  consistent with the algebraic type containing the given constructor
  (looked up via constructor typing, see below).
- **`GuardGetArg var term index`**: the extracted variable gets the
  type of the constructor's field at the given index. A `GuardGetArg`
  always follows a `GuardMatch` on the same term; the preceding match
  establishes which constructor (and therefore which field types) to
  use.
- **`GuardEqual term1 term2`**: both terms must be consistent (like
  body unification, via consistency check).
- **`GuardExpr term`**: a general boolean guard expression (e.g.,
  `N > 0`). The type of `term` must be consistent with
  `prelude:bool`.

These guards carry the same type information as the original pattern
the user wrote.

Body goals not listed above (such as `true`) generate no type
constraints.


## Expression Typing

Expression typing follows evaluation. Positions the runtime
*evaluates* — function, constructor, and tell-side constraint
arguments, `is` right-hand sides, guards — are typed by the
signatures of the functions involved. Positions the runtime treats
*structurally* — the operands of `=`, head and equation patterns,
`GuardEqual` operands, `quote`d terms — are typed by constructor
typing alone (§Constructor Typing). In a structural position, a
compound whose functor names a declared function or class is *not* a
call: the functor is not a data constructor, so the term is typed
`any` (an *evaluable-headed* term; see §Constructor Typing). Thus
`Sum = 1 + 1` binds `Sum` to a symbolic compound typed `any`, while
`Sum is 1 + 1` gives `Sum : int`.

The type of a compound expression is determined by its outermost form:

- **Literal**: `3` has type `int`, `"hi"` has type `string`.
- **Known constructor**: looked up via constructor typing (see below).
- **Unknown constructor**: type `any`. All argument expressions are
  also typed as `any`.
- **Variable**: determined by the constraints on that variable.
- **Function call `f(e₁, ..., eₙ)`**: the declared type variables are
  instantiated with fresh unification variables. Each argument `eᵢ`
  must be consistent with the corresponding declared parameter type.
  The type of the call expression is the declared return type (with
  type variables instantiated by the same substitution). The
  implementation's RHS type is only checked for consistency with the
  declaration — callers never see through to the implementation.
- **Host call**: all argument types and the return type are `any`.


## Constructor Typing

When the checker encounters an atom or compound term, it looks up the
constructor in the set of visible type definitions to determine its
type.

### Known constructors

If `some` is a constructor of `option(A)` with field type `A`, then
`some(X)` has type `option(A)` (with `A` fresh), and `X` gets type
`A`.

A constructor's arity is part of its identity: `some/1` and `some/2`
are not two arity-overloaded constructors, they are a duplicate
declaration. Consequently, using a known constructor with the wrong
number of arguments is a type error, not a fall-through to `any`.

### Unknown constructors

If a constructor is not found in any visible type definition, it is
typed as `any` and an `UndeclaredDataConstructor` warning
(`YCHR-20101`, severity *warning*) is reported. No error is
produced:

- If the context expects a concrete type, the unknown constructor is
  consistent (because `any ~ τ` for all `τ`) — the checker cannot
  verify the constructor is correct, but it also cannot prove it is
  wrong.
- If the context expects a specific algebraic type and the constructor
  is *known to belong to a different type*, that is an error via
  normal consistency checking.

### Evaluable-headed terms

A compound in structural position whose functor names a declared
function or class — e.g. `+(1, 1)` as an operand of `=` — is also
typed `any`, but draws **no** warning: the functor is known, it is
simply not a data constructor, and building symbolic terms over
evaluable functors is a deliberate feature of the language. Like
every other `any`-typed expression, such a term is an
`any`-introduction form (§Soundness): it type-checks against any
context, and the checker makes no promise about what happens when it
is later consumed as a value.

### Constructor disambiguation

Constructors are disambiguated via module qualification, following the
existing module system. If `red` is a constructor of both `color` and
`traffic_light` (in different modules), the user must qualify:
`color:red` vs `traffic_light:red`.


## Exhaustiveness checking

The compiler warns (`YCHR-20103`, severity *warning*) when a function's
pattern-matching equations cannot match some value of a declared
algebraic type. For example:

```prolog
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
  type variables, `any`, or unknown types cannot be enumerated, so they
  are never the source of a warning (they are treated as always
  covered). A nested constructor field is checked under the same rule,
  using the field's declared type.
- Only **closed, single-signature** functions are checked. `:- open_function`
  and `:- open_class` may gain equations in other modules, so a local
  gap might be filled elsewhere; multi-signature `:- class` functions
  have no single column type to enumerate.
- An equation carrying a **user guard** does not count as covering its
  pattern: the guard may fail at runtime, so the pattern is not
  guaranteed to match. A variable or wildcard pattern covers a position
  exhaustively.

Exhaustiveness uses Maranget's matrix/usefulness algorithm, so it
handles multiple arguments and nested constructor patterns, and reports
a concrete unmatched example. Because it is a warning, a non-exhaustive
function still compiles and runs (raising a runtime error only if an
unmatched value actually reaches it); `--Werror` promotes it to a
hard error.


## Host Calls

Host language calls (`host:f(args)`) have all argument types and
return type as `any`. The type checker does not look inside host calls.

CHR library functions that wrap host calls (such as `+`, `-`, `>` in
the prelude) may have declared type signatures. Type checking occurs
at the CHR function call boundary, not at the host call level. For
example:

```prolog
:- function '+'(int, int) -> int.
X + Y -> host:'+'(X, Y).
```

A call to `X + Y` is checked against the signature `(int, int) -> int`.
The internal `host:'+'(X, Y)` call is unchecked (all `any`).


## First-Class Functions

Lambdas and function references are first-class values with function
types.

### Lambdas

A lambda `fun(X, Y) -> expr end` gets a function type inferred from
its context. If the lambda appears where a `fun(int, int) -> bool end` is
expected, then `X : int`, `Y : int`, and `expr` must be consistent
with `bool`.

A lambda in a position where no function type is expected (for
example, passed to an `any`-typed parameter, or unified with a fresh
variable) is typed by inference alone: each parameter is typed by a
fresh flexible variable, the body is checked normally, and the
lambda's type is `fun(α₁, ..., αₙ) -> τ` where `τ` is the body's
inferred type and the `αᵢ` are whatever those variables were bound
to (possibly still flexible).

A lambda cannot carry a `requiring` clause: `requiring` attaches only
to `:- function` and `:- open_function` declarations. A lambda whose
body uses bounded operations is type-checked against its expected
function type, and any unresolved bounds discharge through the same
residual-constraint mechanism that handles function references
(§Function references).

### Function references

A reference `fun name/arity` is type-checked against the expected
function type at its use site. The checker instantiates the
referenced function's declared signature with fresh unification
variables, unifies it with the expected type, and — if the
referenced function carries a `requiring` clause — emits a bound
check at the resulting substitution (§Bounded Polymorphism, §Use-site
checking). The bound check is a residual constraint: it is solved
together with the surrounding equation's other type constraints.

If `double(int) -> int` is declared (no bound), then `fun double/1`
has type `fun(int) -> int end` at every use site.

A reference `fun name/arity` where `name/arity` is a
multi-signature class is itself a residual overload resolution
(§Type Checking Procedure): the expected function type at the use
site filters the class's signatures, and the reference commits when
all surviving candidates are equal after substitution. If the
resolution is still ambiguous when solving ends, it succeeds
silently and the reference's type stays flexible.

If `:- function max(T, T) -> T requiring '>'(T, T) -> bool.` is
declared, `fun max/2` is well-typed wherever the surrounding context
allows the bound to discharge:

- In `apply2(fun max/2, 1, 2)`, the args constrain the substitution
  to `T := int`; the residual bound `'>'(int, int) -> bool` resolves
  against the declared signature.
- In `apply2(fun max/2, "a", "b")`, the same mechanism produces
  `'>'(string, string) -> bool`, which has no consistent declared
  signature; error `BoundUnsatisfied` (YCHR-60012).
- In `apply2(fun max/2, X, Y)` where `X` and `Y` carry no concrete
  type information, the substitution leaves `T` free; the bound
  succeeds silently per the gradual guarantee, exactly as ordinary
  overload resolution does under unresolved arguments.

To export a polymorphic value that refers to a bounded function and
propagates the bound to its callers, the enclosing declaration must
hoist the bound onto its own signature with a `requiring` clause of
its own (mirroring how a Haskell signature must include the
constraint when partially applying an overloaded operator). Without
the hoisted bound, what happens depends on the enclosing
declaration. If it is polymorphic, its type parameters are rigid
during equation checking, so the un-hoisted residual bound finds no
consistent candidate and fails with `BoundUnsatisfied` — hoisting is
mandatory, exactly as the missing constraint would be an error in
Haskell. If the enclosing position is untyped or `any`-typed, there
are no rigid variables in play: the bound discharges silently and is
not visible to callers — the usual gradual-typing tradeoff.

### `call`

The prelude provides a typed wrapper for first-class function
application:

```prolog
:- function call(fun(A) -> B end, A) -> B.
call(F, X) -> '$call'(F, X).
```

The internal `$call` primitive is a host-level operation typed as
`any`. Type checking occurs at the `call` boundary, not at the
`$call` level.


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
   declaration has parameters; `bar(list)` is an error if `list` is
   declared as `list(A)`.

Forward references and mutual recursion between type definitions are
allowed; declaration order is irrelevant.


## Signature Overloading

A *class* may be declared with multiple type signatures. Each
signature specifies a distinct set of argument types and a return
type. The class has a single implementation; only the type checking
is overloaded.

Signature overloading is enabled explicitly by the `:- class` /
`:- open_class` directives. A `:- function` / `:- open_function`
declaration with more than one typed signature is rejected
(`MultiSigOnFunction`, YCHR-16011) — the two forms are intentionally
distinct: `:- function` advertises a single signature (and may carry
a `requiring` clause for bounded polymorphism), while `:- class`
advertises an overload set. Mixing the two forms for the same
name+arity is `MixedDeclKinds` (YCHR-16012).

A `:- class` with a single signature is permitted — verbose but
legal. Idiomatic single-signature code uses `:- function`.

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

An untyped declaration (e.g. `:- function size/1.`) desugars to the
all-`any` signature for type checking (§Defaults), but — as a
deliberate carve-out from that equivalence — it does not count as a
*typed* signature for declaration grouping: it contributes nothing
to the "more than one signature" rule that distinguishes
`:- function` from `:- class`. A program may mix an untyped
`:- function f/1.` with a typed `:- function f(int) -> int.` for the
same name and arity without triggering `MultiSigOnFunction`; only
two or more *typed* declarations would.

### Resolution

When the checker encounters a call to an overloaded class, it
filters the declared signatures by consistency with the known
argument types:

- If all surviving signatures are **equal after substitution** — in
  the common case, exactly one is consistent: the checker applies
  that signature, unifying argument types and propagating the return
  type. This is the "narrow when unambiguous" behavior.
- If **no** signature is consistent: the checker reports a
  `NoMatchingOverload` (YCHR-60006) error.
- If **multiple distinct** signatures are consistent (ambiguous): the
  checker succeeds silently without propagating type information.

Filtering uses consistency (not equality): an argument typed as `any`
or an unbound *flexible* type variable is consistent with any
declared type. Filtering considers argument types only; the call's
expected result type never disambiguates an overload (this is
deliberate).

Resolution is a residual check in the sense of §Type Checking
Procedure: it fires — commits to the surviving signature and
propagates — only when all surviving candidates are equal after
substitution, it is retried as solving adds information, a check
that is still ambiguous when solving ends succeeds silently, and an
empty candidate set is an error whenever it occurs.

### When arguments are not yet resolved

The check's behavior depends on the variable's flavor (see §Type
variables and instantiation):

- **Flexible** type variables (use-site fresh variables, no concrete
  type assigned yet) are consistent with every declared type; the
  check succeeds silently. This preserves the gradual guarantee:
  unannotated code produces no errors.

- **Rigid** type variables (a function's own type parameters, in
  scope while checking its equations) are inconsistent with every
  declared concrete type (§Rigid and flexible type variables). If no
  declared signature is consistent with the rigid tvar — and no
  ambient signature contributed by a `requiring` clause covers it —
  the call fails with `NoMatchingOverload` (YCHR-60006). This closes the soundness gap that would
  otherwise let `foo(T, T) -> bool` silently type-check while
  calling an overloaded `>` at `T` in its body. Rigidity applies
  only at function equations, not at constraint rule heads — see
  §Rigid and flexible type variables.

### Equation checking

For overloaded classes, each equation is checked against the set of
declared signatures: the equation is accepted if it type-checks
under at least one of them, with its parameters typed by that
signature's argument types and its RHS checked against that
signature's return type. An equation that type-checks under no
declared signature is reported as `NoMatchingOverload`
(YCHR-60006).

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

The text below describes the mechanism in terms of functions.
§Bounded constraints collects the adaptations needed for
`:- chr_constraint` declarations.

Bounded polymorphism gives YCHR a form of ad-hoc polymorphism without
elaboration. The checker verifies that the required operations exist
at the inferred type, but never modifies the program or threads any
runtime evidence. Dispatch remains dynamic: the runtime selects a
matching equation by pattern matching, exactly as it does for
unbounded functions.

The "type-class" abstracted over by `requiring` is implicit. (YCHR
*does* have a `:- class` keyword, but it serves a different purpose
— explicit multi-signature overloading; see §Signature Overloading.
The `:- class` keyword is unrelated to bounded polymorphism and
there is no `:- instance` declaration.) The implicit class name is
the required-function name itself: `requiring '>'(T, T) -> bool`
plays the role that `Ord T` plays in classical type-class systems,
and the declared signatures of `>` play the role that `Ord`
instances play.

### Declaration syntax

A function declaration may carry an optional `requiring` clause whose body
is a comma-separated list of *bound signatures* of the form
`name(τ₁, ..., τₙ) -> τᵣ`:

```prolog
:- function max(T, T) -> T requiring '>'(T, T) -> bool.

:- function clamp(T, T, T) -> T requiring
    '>'(T, T) -> bool,
    '<'(T, T) -> bool.

:- function lookup(K, list(pair(K, V))) -> option(V) requiring
    '=='(K, K) -> bool.
```

The `requiring` clause is allowed on `:- function` and
`:- open_function` declarations only. It is *not* allowed on
`:- class` / `:- open_class` (rejected as `RequiringOnClass`,
YCHR-15005) and *not* allowed on `:- extend_class_type` (rejected
as `RequiringOnExtendClassType`, YCHR-15006). The two features are
intentionally orthogonal: `:- function` for bounded single-signature
declarations, `:- class` for explicit multi-signature overloading.

A bounded `:- open_function` already has an extensibility story:
its instance set is determined by what its bound-named functions are
declared for. To extend the set of types at which a bounded open
function works, declare new instances of its bound-named functions —
not new ground signatures of the bounded function itself. A user
who attempts a type extension on a bounded open function will see
*two* diagnostics co-fire on the offending `:- extend_class_type`:
`ExtendClassTypeOnFunction` (YCHR-16013, because type extensions
must target an `:- open_class`) and `ExtendTypeOnBoundedFunction`
(YCHR-16007, because the target's instance set is determined by
its bound). Both messages are accurate; the redundancy is
intentional so each individual rule fails loudly on its own terms.

Equation extensions via `:- extend_function` *are* allowed on bounded
open functions. The new equation is type-checked under the same bound
as the original equations: the bound's required signatures are
ambient in the extension's checking context exactly as they are in
the original module's checking context. No additional declaration is
needed in the extending module.

A `:- chr_constraint` declaration may also carry a `requiring`
clause. The clause shape is identical:

```prolog
:- chr_constraint sorted(list(T)) requiring '<'(T, T) -> bool.
```

Bounds always name *functions*, never constraints.

Every function named in a `requiring` clause must be declared (or
imported); a bound naming an undeclared function is rejected as
`UnknownBoundFunction` (YCHR-16009). A bound may name an *untyped*
declaration: per §Defaults it desugars to the all-`any` signature,
so such a bound is vacuously satisfied at every substitution — it
opts callers out of bound discipline for that function, exactly like
an explicit `g(any, ..., any) -> any` signature.

### Type-variable scoping

Type variables in a `requiring` clause refer to the same variables as
in the enclosing declaration's signature (function or constraint),
with the same implicit quantification. Every variable mentioned in
the clause must also appear in the declaration's primary signature.
A variable that appears only on the clause side is rejected as
`UnboundBoundVariable` (YCHR-16008).

The bound clause does not introduce its own quantifier; the bound
signatures are not first-class types and cannot be referenced
elsewhere.

A `requiring` clause containing no type variables at all is
permitted. Use-site checking runs with `σ` as the identity, so the
bound is effectively a one-shot check that the named declarations
exist; it adds no per-call cost beyond a single overload-resolution
lookup per bound.

### Bound graph

The *bound graph* of a program has one vertex per declared function
and constraint, and an edge from `f` to `g` whenever `g` appears in
`f`'s `requiring` clause. Edges always point at functions. The
bound graph must be acyclic. A cycle is rejected at declaration time
as `BoundCycle` (YCHR-16010).

### Instances

A *substitution* σ for a bounded declaration is a mapping from each
of its type variables to a (possibly polymorphic) type. σ is
**admissible** when, for every bound signature
`gᵢ(σᵢ₁, ..., σᵢₖᵢ) -> ρᵢ` in the clause, the substituted form
`gᵢ(σ(σᵢ₁), ..., σ(σᵢₖᵢ)) -> σ(ρᵢ)` is consistent with at least one
declared signature of `gᵢ` (after fresh-renaming that signature's
own type variables).

The relevant notion of "consistent with" is the one defined in
§Consistency, extended with the type-variable rules of §Type
variables and instantiation: structural consistency on type
constructors, the absorbing rules for `any`, and unification of
type variables under the standard "concrete types bind, `any` does
not" discipline. Both the substituted bound and the (fresh-renamed)
candidate signature may contain free variables; consistency between
them is unification under those rules. As consequences:

- A declared signature of `gᵢ` that uses `any` is consistent with
  every shape, so it admits every substitution. Declaring
  `g(any, ..., any) -> any` opts every caller bounded by `g` out of
  bound discipline for `g`.
- Type variables in declared signatures of `gᵢ` are quantified per
  signature and freshly renamed at each consistency check.
- The instance set is *not* materialized by the checker. It is a
  conceptual set used to define when a use site is well-typed.

### Use-site checking

When the checker encounters a call `f(e₁, ..., eₙ)` to a bounded
function with parametric signature `f(τ₁, ..., τₙ) -> τᵣ` and bound
clause `g₁(...) -> ρ₁, ..., gₘ(...) -> ρₘ`:

1. Compute argument types `A₁, ..., Aₙ` from the call's expressions.
2. Instantiate `f`'s declared type variables with fresh unification
   variables, yielding a substitution σ.
3. For each `i`, check `Aᵢ ~ σ(τᵢ)` and propagate.
4. For each bound `gⱼ(σⱼ₁, ..., σⱼₖⱼ) -> ρⱼ`, check whether at
   least one declared signature of `gⱼ` is consistent with the
   substituted bound `gⱼ(σ(σⱼ₁), ..., σ(σⱼₖⱼ)) -> σ(ρⱼ)`. This is an
   *existence check*, not a propagating overload resolution: it
   asks "does there exist a substitution under which the candidate
   declared signature and the substituted bound are consistent (per
   §Consistency, extended with the rules of §Type variables and
   instantiation)?" Any unifier that the check produces is
   discarded; σ is not modified by a successful bound check, even
   when exactly one candidate matches. If no declared signature of
   `gⱼ` is consistent with the substituted bound, the checker
   reports `BoundUnsatisfied` (YCHR-60012).

   When this check happens during the equation checking of an
   enclosing bounded function, "declared signature" includes the
   ambient signatures contributed by the enclosing function's bound
   (see §Equation checking).
5. The call's result type is `σ(τᵣ)`.

Bound checks are residual checks in the sense of §Type Checking
Procedure — the propagation-free special case. They are solved
together with the equation's other type constraints, so each bound
discharges as soon as σ becomes ground enough to identify (or rule
out) a consistent declared signature. Because a bound check does not
modify σ on success (step 4), it is trivially covered by the
order-independence argument of §Type Checking Procedure: its
discharge order relative to other constraints cannot affect the
final type assignment.

If a bound's substitution is still partial at end of solving — that
is, the bound contains free type variables that no other constraint
pinned down — the bound succeeds silently per the gradual guarantee.
This matches the rest of the gradual-typing story: a check that lacks
the information to fail is not a failure.

### Equation checking

This subsection describes the rule for function equations. The
analogous rule for constraints — head-only ambient signatures during
rule type-checking — is described in §Bounded constraints.

Equations of a bounded function are checked under an extended
declaration context: each bound signature `gᵢ(...) -> ρᵢ` is treated
as if it were an additional declared signature of `gᵢ`, available
*only while checking the equations of this function*. The checker
then runs the standard equation-checking procedure described in
§Type Checking Procedure.

Concretely, for each equation:

1. Fresh **rigid** type variables are allocated for each declared
   type variable of the function (§Rigid and flexible type
   variables).
2. The equation's parameters are typed under the substituted parameter
   types and the equation's RHS under the substituted return type.
3. Calls to bound-named functions inside the equation see the bound's
   signatures as available declarations and resolve against them
   (alongside any other declared signatures of those functions).
   The ambient signature's type variables are *not* fresh-renamed
   at each call: they share identity with the enclosing function's
   declared type variables (the same fresh variables allocated in
   step 1). Fresh renaming applies only to the *other* declared
   signatures of `gᵢ` participating in resolution.
4. Calls to non-bound functions resolve through their ordinary
   declared signatures.

The ambient signatures introduced by the bound are visible to *every*
overload-resolution and bound-check performed while checking this
function's equations — including the use-site bound checks triggered
by calls to other bounded functions in the body. In other words,
"declared signature" in §Use-site checking is to be read as "declared
signature, plus any ambient signature contributed by the enclosing
equation's bound." This ensures that a bounded function whose body
calls another bounded function at its own type variables remains
polymorphic: the inner bound check sees the ambient sig and does not
force the outer type variables to a concrete instance.

If an equation fails to type-check under this extended context, the
failure is reported with the same error code that the ordinary
checker would have produced (typically a constructor mismatch or
`NoMatchingOverload` (YCHR-60006)). No new error code is introduced for
equation-level failures; the bound's contribution to the equation
context simply enlarges the set of valid programs.

This mirrors how a type-class method body is checked under its class
constraints in classical formulations, but without producing the
dictionary-passing translation that classical formulations would
emit. The bound's "evidence" is purely a checker-time enlargement of
the available signatures; nothing flows from the bound into the
emitted code.

### Bounded constraints

A bounded `:- chr_constraint` declaration uses the same syntax,
§Type-variable scoping rules, §Bound graph membership, and §Instances
semantics as a bounded function. The differences are confined to two
places: where use-site checking discharges, and what replaces
§Equation checking.

#### Use sites

A bounded constraint emits a bound check at every position in which
it occurs: **body tell** and **rule head occurrence**. Each
occurrence allocates its own fresh substitution σ for the
constraint's declared type variables (per §Use-site checking step 2)
and discharges the bound as a residual constraint over that σ. There
is no return type, so step 5 of §Use-site checking is dropped.

- **Body tell** `... <=> ..., sorted(L).` — σ is refined by unifying
  the tell's argument expressions against the constraint's declared
  argument types (§Use-site checking step 3). The bound discharges
  whenever σ becomes ground enough to identify (or rule out) a
  consistent declared signature.
- **Head occurrence** `sorted(L) <=> ...` — σ is refined by unifying
  the head pattern against the constraint's declared argument types,
  which establishes the types of the head's variables (§Sources of
  Type Information §1). Whether σ later becomes ground enough to
  discharge the bound depends on what other heads, guards, and body
  goals in the same rule contribute through those variables.

Each occurrence — including multiple occurrences of the same bounded
constraint in one rule — gets its own fresh type variables.
Order-independence and the silent-success-on-partial-σ behavior carry
over verbatim.

#### Rule-level ambient signatures (replacing §Equation checking)

Constraints have no equations. The analogous "implementation site"
is the set of rules whose **head** mentions the bounded constraint.
While type-checking such a rule, every bound carried by a bounded
constraint in the rule's head contributes its required signatures to
the ambient declaration context for the duration of that rule's
checking. Body tells of the same bounded constraint do **not**
contribute — body tells are use sites that discharge the bound, not
implementations that assume it. The asymmetry mirrors §Equation
checking. For functions: equation body sees the bound as ambient,
call site discharges it. For constraints: rule head sees the bound
as ambient, body tell discharges it.

Type checking operates on the desugared AST, where every rule has
the uniform shape `kept + removed + guards + body`. "Head" here
means the constraints in `kept ∪ removed`; both kept and removed
head constraints contribute their bounds as ambient. Guards and body
goals do not.

The rule exists because a rule body is entitled to *assume* the
bound, exactly as a function equation is. Consider

```prolog
:- chr_constraint str(string).
weird @ sorted([X | _]), str(S) <=> X < S | true.
```

The second head pins `S : string`, so the guard calls `<` at
`(T, string)`. Without ambient signatures, the guard's overload
resolution would end with an empty candidate set whenever no
`<(string, string)` signature is declared, and report a spurious
*rule-level* `NoMatchingOverload`. But under the bound's contract
the rule may assume `'<'(T, T) -> bool` exists; whether it actually
exists at `T = string` is a question about *use sites*, and
use-site checking already answers it: `BoundUnsatisfied` at any
ordinary use site that pins `T := string` (a use site *inside* a
rule whose head carries the bound instead discharges against the
ambient signature — part of the flexible-head laxity documented in
§Soundness). With the ambient signature in scope,
the guard resolves against `<(T, T) -> bool` (binding
`T := string`), the rule checks under its contract, and instance
errors fire where they belong — mirroring how a type-class method
body defers instance selection to its callers.

A secondary effect: when exactly one signature of the bound-named
function happens to be declared, the ambient signature prevents the
guard's resolution from silently narrowing `T` to that sole instance
(a resolution fires only when all surviving candidates are equal,
§Type Checking Procedure). A rule like

```prolog
sorted([X, Y | Rest]) <=> X < Y | sorted([Y | Rest]).
```

is thus checked parametrically in `T` rather than at an accidental
single declared instance.

When the bounded constraint occurs in both head and body of the same
rule (as in the recursive `sorted` case above), the body occurrence
is still a use site and discharges its own bound. If the rule leaves
σ partial (as here), the discharge succeeds silently per the gradual
rule; if other constraints pin σ, it discharges against the ambient
signature contributed by the head occurrence.

When multiple bounded constraints appear in the same rule's head, all
their bound signatures are ambient; the ambient set is the union.
Each head occurrence's type variables are freshly allocated (see
§Use sites), so two occurrences of the same bounded constraint
contribute structurally identical bounds at distinct variable
identities and cannot collide.

#### Worked example — polymorphic `sorted`

```prolog
:- open_class ('<'(int, int) -> bool), ('<'(float, float) -> bool).
:- chr_constraint sorted(list(T)) requiring '<'(T, T) -> bool.

sorted([]) <=> true.
sorted([_]) <=> true.
sorted([X, Y | Rest]) <=> X < Y | sorted([Y | Rest]).
```

Rule checking: each rule's head mentions `sorted`, so the bound's
ambient signature `<(T, T) -> bool` is in scope. The third rule's
guard `X < Y` sees three candidate signatures — the two declared
ones and the ambient bound — and remains ambiguous (`T` is never
pinned in this rule), so the resolution succeeds silently and the
guard's result type is checked against `bool` as usual. The body
tell `sorted([Y | Rest])` is a use site of `sorted` and discharges
its bound silently: its σ is still partial. Had the rule pinned `T`,
the bound would have discharged against the ambient signature.

Use site `sorted([1, 2, 3])` (in another rule's body, or as a
top-level goal): σ = (T := int); the substituted bound
`<(int, int) -> bool` is consistent with the declared signature.

Use site `sorted(["a", "b"])`: σ = (T := string); no consistent
declared signature; error `BoundUnsatisfied` (YCHR-60012).

Use site `sorted(L)` where `L : list(any)` or `L : list(α)` with `α`
free: σ leaves `T` partial; the bound succeeds silently per the
gradual guarantee.

A later module that extends the open class with
`:- extend_class_type ('<'(string, string) -> bool).` automatically
extends the admissible instance set of `sorted` — no edit to
`sorted`'s declaration required. This is the open-set property of
bounded polymorphism at the constraint level. (The bound-named class
must be `:- open_class` for cross-module extension; a closed
`:- class` fixes the instance set at its declaration.)

### Coexistence with multi-signature overloading

Multi-signature overloading (`:- class` / `:- open_class`, see
§Signature Overloading) and bounded polymorphism are exclusive:
`:- class` cannot carry a `requiring` clause (rejected as
`RequiringOnClass`, YCHR-15005). The two have overlapping expressive
power for finite instance sets, but their checker behavior differs:
a class's signatures are checked independently at use sites, and an
equation that types under any one signature is accepted; a bounded
function has a single parametric signature — equations are checked
once, with the bound enlarging the available context, and use sites
verify the bound at the inferred substitution.

The same applies to constraints: a `:- chr_constraint` declaration
may carry `requiring`, but there is no multi-signature form for
constraints.

### Errors

The bounded-polymorphism error codes — `YCHR-16007` through
`YCHR-16010` and `YCHR-60012` — are catalogued in
[errors.md](errors.md). The equation-checking path introduces no new
codes (equations either check under the enlarged context or fail
with existing ones), and the constraint case shares the function
case's codes.

### Worked examples

**Example 1 — Polymorphic `max`.**

```prolog
:- class ('>'(int, int) -> bool), ('>'(float, float) -> bool).
:- function max(T, T) -> T requiring '>'(T, T) -> bool.

max(X, Y) | X > Y -> X.
max(_, Y)         -> Y.
```

Equation checking: `T` is rigid; `X : T`, `Y : T`. The guard `X > Y`
calls `>`; the declared `int` and `float` signatures are
inconsistent with the rigid `T`, so the bound's ambient signature
`>(T, T) -> bool` is the sole surviving candidate; the resolution
fires and the call types as `bool`. The RHS `X : T` matches the
return type `T`. Both equations check.

Use site `R is max(3, 4)`: σ = (T := int); the substituted bound
`>(int, int) -> bool` is consistent with the declared signature;
result type `int`; `R : int`.

Use site `R is max("a", "b")`: σ = (T := string); the substituted
bound `>(string, string) -> bool` has no consistent declared
signature; error `BoundUnsatisfied` (YCHR-60012).

**Example 2 — Multi-variable bound.**

```prolog
:- function '=='(int, int) -> bool.
:- function lookup(K, list(pair(K, V))) -> option(V) requiring
    '=='(K, K) -> bool.

lookup(_, [])                            -> none.
lookup(K, [pair(K2, V) | _]) | K == K2  -> some(V).
lookup(K, [_ | Rest])                    -> lookup(K, Rest).
```

Equations are checked parametrically over `K` and `V`. The recursive
call `lookup(K, Rest)` is itself a use site; the recursion's σ is
the same as the outer equation's, so the inner bound is the bound
under that σ — trivially consistent during equation checking because
the bound's signatures are ambient.

Use site `R is lookup(3, L)` where `L : list(pair(int, string))`:
σ = (K := int, V := string); substituted bound
`==(int, int) -> bool` is consistent with the declared signature;
result type `option(string)`.

Use site `R is lookup(0.5, M)` where `M : list(pair(float, int))`
and no `==(float, float) -> bool` has been declared: error
`BoundUnsatisfied` (YCHR-60012) for the substituted bound at K := float.

### Interaction with `any`

`any` interacts with bounds the same way it interacts with ordinary
overloading:

- A use site whose argument types are `any` makes σ partial; the
  bound check succeeds silently and the call's result type remains a
  fresh flexible variable (the `any` arguments bind nothing), exactly
  as in ordinary overload resolution under unresolved arguments.
- A bound that names a function with an all-`any` declared signature
  is satisfied by every substitution: declaring `g(any, ..., any) ->
  any` opts every caller bounded by `g` out of bound discipline for
  that specific `g`.
- A type variable that meets `any` does not bind (per §Type variables
  and instantiation). A bound depending on such a variable remains
  unresolved until concrete information arrives, at which point the
  bound is checked.

### Soundness

Bounded polymorphism preserves the gradual guarantee of §Soundness:

- **Conservativity over signature overloading.** Replacing a bounded
  declaration with an enumerated multi-signature declaration over
  the same instance set produces a program with the same set of
  accepted use sites at those instances.
- **Conservativity over `any`.** Replacing every type variable in a
  bounded declaration with `any` (and consequently every bound with
  the all-`any` form of its named function) produces a program that
  type-checks unchanged. This is the standard "more `any` never adds
  errors" property.
- **No elaboration.** The checker does not modify the AST. The
  bound is verified at each use site; once verified, no residual
  evidence is required at runtime, because dispatch is dynamic
  (pattern matching across equations).

Bound checking is expressed as ordinary use-site overload resolution
and inherits its confluence and gradual properties.

The same properties hold for bounded constraints. No new soundness
argument is required: rule-level ambient signatures are a structural
mirror of equation-level ambient signatures, and the use-site
mechanism is shared. The union of multiple bounded constraints'
ambient signatures within a single rule is sound because each
occurrence's type variables are freshly allocated per rule
(§Use sites), so contributed signatures cannot collide on shared
variable identities.


## Soundness

The type system is a gradual type system in the sense of Siek & Taha.
The relevant correctness properties are:

1. **Soundness of the fully-typed fragment**: if no expression in a
   program is typed `any` and the program type-checks, then at
   runtime no operation will receive a value of an unexpected type.
   (Standard progress + preservation, restricted to that fragment.)
   The *`any`-introduction forms* — an `any`-annotated or untyped
   declaration position, a host call, an unknown constructor, an
   evaluable-headed term in structural position (§Expression Typing)
   — therefore delimit exactly where the guarantee stops: a program
   that binds a symbolic `1 + 1` with `=`, calls the host, or forges
   an unknown constructor has left the fragment at that expression.

2. **The gradual guarantee**: replacing any type annotation with `any`
   (making the program less precise) never introduces new type errors.
   Conversely, making types more precise can only add errors, never
   remove them. This ensures that adding type annotations is always
   safe and never breaks a working program.

Rigid type variables (§Type variables and instantiation §Rigid and
flexible type variables) are what make property 1 hold for
polymorphic *functions* whose equation bodies use overloaded
operations: a declaration like `:- function foo(T, T) -> bool.`
whose equation body calls an overloaded operator at the type
variable cannot type-check without a `requiring` clause covering
that operation. Without rigidity, such a program type-checked
silently (every declared signature filtered as "consistent" against
the unbound flexible variable representing T), but it could fail
at runtime when called at a type for which no equation of the
overloaded operator existed. Rigidity does not constrain
unannotated programs: in code without type annotations, the
enclosing declaration has no type variables of its own to allocate
as rigid, so the gradual guarantee continues to hold.

An analogous gap remains for polymorphic *constraints* whose rule
bodies use overloaded operations at the constraint's type
parameter (e.g. `:- chr_constraint foo(T, T). foo(X, Y) <=> X > Y.`
silently type-checks even though `>` is not defined at all `T`).
The cost of closing this gap with rigidity at rule heads is
rejecting common multi-head rule idioms that rely on cross-head
type-variable unification (e.g. transitivity of a polymorphic
`leq(T, T)`), so the constraint case is intentionally left lax;
users who need stronger checking can add an explicit `requiring`
clause to the constraint declaration.

Since YCHR erases types completely (no runtime casts, no blame
tracking), the checker cannot guarantee that programs using `any` are
type-safe at runtime. It catches inconsistencies where it has enough
information, and is silent where it does not. This is the standard
trade-off of gradual typing without runtime enforcement.

The key ingredients behind these properties are:

- The consistency relation is reflexive and symmetric (but not
  transitive — this is expected for gradual typing).
- Consistency with `any` is absorbing: `any ~ τ` always succeeds.
- Constraint solving is order-independent in the precise sense of
  §Type Checking Procedure: acceptance and the final type assignment
  do not depend on solving order; only error attribution may vary.
- The fully-typed fragment reduces to standard HM with algebraic
  data types.
