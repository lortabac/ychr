# YCHR Type System Specification

This document specifies the YCHR static type system: a gradual,
consistency-based type checker for CHR programs. The type checker
operates on the desugared AST. Types are erased at runtime; the
checker produces errors without transforming the program.


## Overview

The type system has four goals:

1. Catch type inconsistencies statically, before compilation.
2. Remain optional -- programs that omit type annotations are accepted
   without errors.
3. Provide a uniform type language for constraints and functions.
4. Be simple enough to implement quickly, but extensible toward
   refinement types in the future.

The checker takes a `Desugared.Program` and produces a list of type
errors. It does not modify the AST. Type errors prevent compilation
from proceeding.


## Types

The type language is defined by the following grammar:

```
τ  ::=  int                          -- integers
     |  string                       -- strings
     |  any                          -- the dynamic type
     |  α                            -- type variable
     |  C(τ₁, ..., τₙ)              -- algebraic type constructor
     |  fun(τ₁, ..., τₙ) -> τᵣ      -- function type
```

### Built-in types

- **`int`** -- integer values.
- **`string`** -- string values.
- **`any`** -- the dynamic type. Consistent with every other type.
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

### Function types

Function types describe first-class callable values (lambdas and
function references):

```
fun(int, int) -> bool
fun(A) -> A
```

A function type `fun(τ₁, ..., τₙ) -> τᵣ` represents a callable
taking `n` arguments of types `τ₁, ..., τₙ` and returning a value of
type `τᵣ`.

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
`:- chr_constraint leq(any, any)`.


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
  B ~ B                       (B a base type: int, string)

  τ₁ ~ σ₁   ...   τₙ ~ σₙ                         [C-Con]
  ────────────────────────────
  C(τ₁,...,τₙ) ~ C(σ₁,...,σₙ)

  τ₁ ~ σ₁   ...   τₙ ~ σₙ   τᵣ ~ σᵣ              [C-Fun]
  ────────────────────────────────────
  fun(τ₁,...,τₙ) -> τᵣ ~ fun(σ₁,...,σₙ) -> σᵣ
```

Two distinct type constructors (neither being `any`) are
**inconsistent**:

```
  C ≠ D                                             [Inconsistency]
  ────────────────────────────
  C(...) ~ D(...)  is an error
```

This applies to all constructors: base types, algebraic types, and
function types. For example, `int ~ bool`, `option(int) ~ list(int)`,
and `int ~ fun(int) -> int` are all errors.


## Type Propagation and Consistency

The type checker infers types for source variables by propagating
type information through constraints. Each source variable starts
with an unknown type. As the checker processes the rule, types flow
into variables from declarations (head constraints, function
signatures) and between variables through unification and `is`
expressions.

When two types meet, the checker performs a *consistency check*:

- `τ ~ τ` succeeds for identical types.
- `C(τ⃗) ~ C(σ⃗)` succeeds if all arguments are pairwise consistent.
- `C(...) ~ D(...)` where C ≠ D is an error.
- `any ~ τ` always succeeds, for any `τ` (see below).

When a variable with an unknown type meets a concrete type, the
variable acquires that type. When two variables with known concrete
types meet, the checker verifies they are consistent.

### The role of `any`

The `any` type is the escape hatch for gradual typing. It is
consistent with every other type. However, `any` does **not**
propagate through variables the way concrete types do:

- When a variable's type is determined solely by a declaration that
  uses `any` (e.g., a constraint declared as `foo(any)`), the
  variable acquires type `any`.
- When a variable with a known concrete type meets `any` through
  unification or a consistency check, the variable **retains** its
  concrete type. The check succeeds but the concrete type is not
  replaced by `any`.
- When `any` meets a declared type parameter (from a polymorphic
  declaration), the type parameter is **not** bound to `any`. This
  prevents `any` from leaking through shared type parameters and
  masking real inconsistencies. (See the Type Variables section.)

The key consequence: `any` stops type propagation. A variable typed
as `any` will not carry type information from one position to
another, and `any` does not overwrite concrete types already
established on other variables.

### Example: propagation through `=`

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
succeed. Note that `Y` and `Z` retain their declared types -- the
`any` from `X` does not propagate to them. If the rule also
contained `Y = Z`, the checker would report an error for
`int ~ bool`.

### Example: inference through `is`

```prolog
:- chr_constraint result/1.
:- function double(int) -> int.
rule @ result(R) <=> R is double(1).
```

- `double(1)`: argument `1` has type `int`, consistent with the
  declared parameter type. Return type is `int`.
- `R is double(1)`: `R` acquires type `int` from the return type.
- `result(R)`: `R` is `int`, which constrains the argument of
  `result`.


## Type Checking Procedure

Type checking operates on each rule and function equation
independently. For each rule or equation, the checker:

1. Collects type constraints from all positions (see below).
2. Solves the constraints together using unification and consistency.
3. Reports all inconsistencies as type errors.

Constraint solving is order-independent: all constraints are gathered
first and solved as a set.

### Type variables and instantiation

When a declared constraint or function is used, the checker
instantiates its declared type with fresh unification variables. For
example, if `member(A, list(A))` is used twice in a rule, each use
gets independent fresh variables (`a₁, list(a₁)` and `a₂, list(a₂)`).

Type variables unify normally via substitution. When a type variable
meets `any`, the consistency check succeeds but the type variable is
**not bound**. Only concrete types bind type variables. This prevents
`any` from leaking through shared type variables and masking real
inconsistencies.

For example, given `:- chr_constraint foo(A, A).` and a use
`foo(X, Y)` where `X : any` and `Y : int`:

- Fresh `α` for `A`.
- `α ~ any` (from X): succeeds, `α` unchanged.
- `α ~ int` (from Y): `α = int`.

The concrete type `int` is preserved despite the `any` input.

Unconstrained type variables remaining after solving are not errors.
They represent genuinely polymorphic usage.


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
assignment: the return type of the RHS expression determines the type
of the LHS variable.

### 5. Unification (bidirectional)

In `X = Y` (body unification), type information flows
bidirectionally. If `X` has a known concrete type and `Y` does not,
`Y` acquires `X`'s type (and vice versa). If both have known
concrete types, the checker verifies they are consistent. If one
side is `any` and the other has a concrete type, the check succeeds
and the concrete side retains its type. If one side is `any` and
the other is unknown, the unknown side becomes `any`.

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
  declaration -- callers never see through to the implementation.
- **Host call**: all argument types and the return type are `any`.


## Constructor Typing

When the checker encounters an atom or compound term, it looks up the
constructor in the set of visible type definitions to determine its
type.

### Known constructors

If `some` is a constructor of `option(A)` with field type `A`, then
`some(X)` has type `option(A)` (with `A` fresh), and `X` gets type
`A`.

### Unknown constructors

If a constructor is not found in any visible type definition, it is
typed as `any`. This means:

- If the context expects a concrete type, the unknown constructor is
  consistent (because `any ~ τ` for all `τ`). No error is produced --
  the checker cannot verify the constructor is correct, but it also
  cannot prove it is wrong.
- If the context expects a specific algebraic type and the constructor
  is *known to belong to a different type*, that is an error via
  normal consistency checking.

### Constructor disambiguation

Constructors are disambiguated via module qualification, following the
existing module system. If `red` is a constructor of both `color` and
`traffic_light` (in different modules), the user must qualify:
`color:red` vs `traffic_light:red`.


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
its context. If the lambda appears where a `fun(int, int) -> bool` is
expected, then `X : int`, `Y : int`, and `expr` must be consistent
with `bool`.

### Function references

A reference `name/arity` has the function type derived from the
function's declared signature. If `double(int) -> int` is declared,
then `double/1` has type `fun(int) -> int`.

### `call`

The prelude provides a typed wrapper for first-class function
application:

```prolog
:- function call(fun(A) -> B, A) -> B.
call(F, X) -> '$call'(F, X).
```

The internal `$call` primitive is a host-level operation typed as
`any`. Type checking occurs at the `call` boundary, not at the
`$call` level.


## Type Definition Validation

The checker validates type definitions themselves:

1. **Bound variables**: all type variables appearing in constructor
   fields must be bound by the type definition header. For example,
   `type foo(A) ---> bar(B)` is an error because `B` is not bound.

2. **Recursive types**: recursive type definitions are well-formed.
   For example, `type list(A) ---> cons(A, list(A))` is valid.

3. **Defined types**: types referenced in constructor fields must be
   defined. For example, `type foo ---> bar(undefined_type)` is an
   error.


## Signature Overloading

A function may be declared with multiple type signatures. Each
signature specifies a distinct set of argument types and a return
type. The function has a single implementation; only the type
checking is overloaded.

### Declaration syntax

```prolog
:- function
    ('+'(int, int) -> int),
    ('+'(float, float) -> float).
```

Multiple comma-separated typed declarations with the same name and
arity are grouped into a single overloaded function definition.

### Resolution

When the checker encounters a call to an overloaded function, it
filters the declared signatures by consistency with the known
argument types:

- If **exactly one** signature is consistent: the checker applies it,
  unifying argument types and propagating the return type. This is the
  "narrow when unambiguous" behavior.
- If **no** signature is consistent: the checker reports a
  `no_matching_overload` error.
- If **multiple** signatures are consistent (ambiguous): the checker
  succeeds silently without propagating type information.

Filtering uses consistency (not equality): an argument typed as `any`
or an unbound type variable is consistent with any declared type.

### When arguments are not yet resolved

If argument types are not yet ground (still unbound type variables
with no concrete type), all signatures are trivially consistent, and
the check succeeds silently. This preserves the gradual guarantee:
unannotated code produces no errors.

### Equation checking

For overloaded functions, each equation is checked via the same
overload resolution mechanism. The equation's parameter types and
return type are matched against the set of declared signatures.

### Example

```prolog
:- chr_type color ---> red ; green ; blue.

:- function
    (size(int) -> int),
    (size(string) -> int).

size(N) | integer(N) -> N.
size(S) | string(S) -> string_length(S).

:- chr_constraint foo(color).
foo(X) <=> R is size(X).   %% Error: no matching overload
                            %% (color is not int or string)
```


## Extensibility

The type system is designed to accommodate future extensions:

- **Predicate-based refinement types**: guards like `integer(X)` could
  narrow the type of `X` from `any` to `int`.

- **Advanced refinement types**: the consistency-based framework and
  constraint-gathering approach can be extended with subtyping or
  predicate constraints without changing the overall architecture.

- **Float support**: once float is added as a built-in type, the
  existing signature overloading mechanism (see below) enables typing
  arithmetic operators over both int and float.


## Soundness

The type system is a gradual type system in the sense of Siek & Taha.
The relevant correctness properties are:

1. **Soundness of the fully-typed fragment**: if a program uses no
   `any` and type-checks, then at runtime no operation will receive
   a value of an unexpected type. (Standard progress + preservation,
   restricted to the fully-annotated sublanguage.)

2. **The gradual guarantee**: replacing any type annotation with `any`
   (making the program less precise) never introduces new type errors.
   Conversely, making types more precise can only add errors, never
   remove them. This ensures that adding type annotations is always
   safe and never breaks a working program.

Since YCHR erases types completely (no runtime casts, no blame
tracking), the checker cannot guarantee that programs using `any` are
type-safe at runtime. It catches inconsistencies where it has enough
information, and is silent where it does not. This is the standard
trade-off of gradual typing without runtime enforcement.

A semi-formal paper proof of these properties is sufficient for this
system, given that the core is a well-understood construction. The
key ingredients are:

- The consistency relation is reflexive and symmetric (but not
  transitive -- this is expected for gradual typing).
- Consistency with `any` is absorbing: `any ~ τ` always succeeds.
- Constraint gathering is confluent (order-independent).
- The fully-typed fragment reduces to standard HM with algebraic
  data types.


## Summary

| Aspect | Decision |
|--------|----------|
| Nature | Static, types erased at runtime |
| Pipeline position | After desugaring, before compilation |
| Effect on AST | None -- errors only, prevents compilation |
| Built-in types | `int`, `string`, `any` |
| User-defined types | Algebraic types via `:- chr_type` |
| Function types | `fun(τ₁,...,τₙ) -> τᵣ` |
| Polymorphism | Parametric, implicitly quantified, no rank-n |
| Overloading | Signature overloading (multiple sigs per function) |
| Defaults | Missing annotations default to `any` |
| Core relation | Consistency (gradual typing) |
| Type merging | Consistency check, `any` absorbs |
| Solving | Constraint gathering, order-independent |
| Inline annotations | Not supported; types only in declarations |
| Host calls | All `any`; operators typed via library signatures |
| Constructors | Looked up in type definitions; unknown → `any` |
| Disambiguation | Module qualification |
| Soundness | Gradual guarantee; paper proof sufficient |
