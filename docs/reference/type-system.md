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
     |  float                        -- floating-point numbers
     |  string                       -- strings
     |  any                          -- the dynamic type
     |  α                            -- type variable
     |  C(τ₁, ..., τₙ)              -- algebraic type constructor
     |  fun(τ₁, ..., τₙ) -> τᵣ      -- function type
```

### Built-in types

- **`int`** -- integer values.
- **`float`** -- floating-point values.
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

A constructor's arity is part of its identity: `some/1` and `some/2`
are not two arity-overloaded constructors, they are a duplicate
declaration. Consequently, using a known constructor with the wrong
number of arguments is a type error, not a fall-through to `any`.

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
has type `fun(int) -> int` at every use site.

If `:- function max(T, T) -> T requiring '>'(T, T) -> bool.` is
declared, `fun max/2` is well-typed wherever the surrounding context
allows the bound to discharge:

- In `apply2(fun max/2, 1, 2)`, the args constrain the substitution
  to `T := int`; the residual bound `'>'(int, int) -> bool` resolves
  against the declared signature.
- In `apply2(fun max/2, "a", "b")`, the same mechanism produces
  `'>'(string, string) -> bool`, which has no consistent declared
  signature; error `bound_unsatisfied`.
- In `apply2(fun max/2, X, Y)` where `X` and `Y` carry no concrete
  type information, the substitution leaves `T` free; the bound
  succeeds silently per the gradual guarantee, exactly as ordinary
  overload resolution does under unresolved arguments.

To export a polymorphic value that refers to a bounded function and
propagates the bound to its callers, the enclosing declaration must
hoist the bound onto its own signature with a `requiring` clause of
its own (mirroring how a Haskell signature must include the
constraint when partially applying an overloaded operator). Without
the hoisted bound, the enclosing declaration's type-checking
discharges the bound silently, and the bound is not visible to
callers — the same gradual-typing tradeoff that applies elsewhere in
this system.

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

Untyped declarations (e.g. `:- function size/1.`) contribute no
signature and so do not count toward the "more than one signature"
rule that distinguishes `:- function` from `:- class`. A program
may mix an untyped `:- function f/1.` with a typed
`:- function f(int) -> int.` for the same name and arity without
triggering `MultiSigOnFunction`; only two or more *typed*
declarations would.

### Resolution

When the checker encounters a call to an overloaded class, it
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

For overloaded classes, each equation is checked via the same
overload resolution mechanism. The equation's parameter types and
return type are matched against the set of declared signatures.

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

### Type-variable scoping

Type variables in a `requiring` clause refer to the same variables as
in the enclosing declaration's signature (function or constraint),
with the same implicit quantification. Every variable mentioned in
the clause must also appear in the declaration's primary signature.
A variable that appears only on the clause side is rejected as
`unbound_bound_variable`.

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
as `bound_cycle`.

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
   reports `bound_unsatisfied`.

   When this check happens during the equation checking of an
   enclosing bounded function, "declared signature" includes the
   ambient signatures contributed by the enclosing function's bound
   (see §Equation checking).
5. The call's result type is `σ(τᵣ)`.

Bound checks are emitted as residual type constraints, not resolved
inline with the surrounding statements. They are solved together with
the equation's other type constraints by the order-independent solver
(§Type Checking Procedure), so each bound discharges as soon as σ
becomes ground enough to identify (or rule out) a consistent declared
signature. Because a bound check does not modify σ on success
(step 4), the discharge order of bounds relative to other constraints
cannot affect the final type assignment — the order-independence
claim holds without auxiliary argument.

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

1. Fresh unification variables are allocated for each declared type
   variable of the function.
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
`no_matching_overload`). No new error code is introduced for
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

Without this rule, a sensible rule like

```prolog
sorted([X, Y | Rest]) <=> X < Y | sorted([Y | Rest]).
```

would force `T` to a concrete instance at the `X < Y` guard call,
defeating the polymorphic declaration of `sorted`. With the rule,
`X < Y` resolves against the ambient bound `<(T, T) -> bool` and
remains polymorphic in `T`.

When the bounded constraint occurs in both head and body of the same
rule (as in the recursive `sorted` case above), the body occurrence
is still a use site and discharges its own bound. The discharge is
trivially satisfied because the head occurrence has contributed the
same bound's signatures as ambient.

When multiple bounded constraints appear in the same rule's head, all
their bound signatures are ambient; the ambient set is the union.
Each head occurrence's type variables are freshly allocated (see
§Use sites), so two occurrences of the same bounded constraint
contribute structurally identical bounds at distinct variable
identities and cannot collide.

#### Worked example — polymorphic `sorted`

```prolog
:- function ('<'(int, int) -> bool), ('<'(float, float) -> bool).
:- chr_constraint sorted(list(T)) requiring '<'(T, T) -> bool.

sorted([]) <=> true.
sorted([_]) <=> true.
sorted([X, Y | Rest]) <=> X < Y | sorted([Y | Rest]).
```

Rule checking: each rule's head mentions `sorted`, so the bound's
ambient signature `<(T, T) -> bool` is in scope. The third rule's
guard `X < Y` resolves through the ambient bound and types as `bool`;
the body tell `sorted([Y | Rest])` is a use site of `sorted` and
discharges the bound at the same σ — trivially consistent because the
bound's signatures are ambient.

Use site `sorted([1, 2, 3])` (in another rule's body, or as a
top-level goal): σ = (T := int); the substituted bound
`<(int, int) -> bool` is consistent with the declared signature.

Use site `sorted(["a", "b"])`: σ = (T := string); no consistent
declared signature; error `bound_unsatisfied`.

Use site `sorted(L)` where `L : list(any)` or `L : list(α)` with `α`
free: σ leaves `T` partial; the bound succeeds silently per the
gradual guarantee.

A later module that declares `<(string, string) -> bool` automatically
extends the admissible instance set of `sorted` — no edit to
`sorted`'s declaration required. This is the open-set property of
bounded polymorphism at the constraint level.

### Coexistence with multi-signature overloading

Multi-signature overloading lives behind the `:- class` /
`:- open_class` keywords (see §Signature Overloading) and is
enforced as exclusive with bounded polymorphism: `:- class` cannot
carry a `requiring` clause (rejected as `RequiringOnClass`,
YCHR-15005). The two forms occupy disjoint syntactic slots:

- `:- class` (multi-signature) `(f(int) -> int), (f(float) -> float)`
  enumerates instances explicitly. It is the right tool when the
  instance set is small, fixed, and unrelated, or when the
  implementation differs perceptibly per instance.
- `:- function ... requiring ...` (bounded single-signature)
  `f(T) -> T requiring ...` describes an open instance set implicitly.
  It is the right tool when the instance set is large, growing (e.g.,
  users may declare new instances of `>` after importing `max`), or
  naturally captured by an operation.

The two forms have overlapping expressive power for finite,
enumerated instance sets, but their checker behavior differs:

- `:- class`: each declared signature is checked independently
  at use sites; any equation that types under any one signature is
  accepted.
- Bounded `:- function`: the function has a single parametric
  signature; equations are checked once, parametrically, with the
  bound enlarging the available context; use sites verify the bound
  at the inferred substitution.

The same rule applies to constraints: a `:- chr_constraint`
declaration may carry `requiring`, but no comma-separated
multi-signature form for constraints exists in the surface today.

### Errors

Bounded polymorphism introduces five new error codes (final numbers
assigned in the type-system error range during implementation). The
first four apply uniformly to functions and constraints; the fifth
concerns `:- extend_class_type`, which has no constraint analog:

- **`unbound_bound_variable`** — a type variable appears in a `requiring`
  clause but not in the enclosing declaration's primary signature.
- **`unknown_bound_function`** — a `requiring` clause references a
  function that has not been declared. Function identity is
  name-plus-arity, so `requiring foo(int, int) -> bool` when only
  `foo/3` is declared (or no `foo` at all) raises this error.
- **`bound_cycle`** — the bound graph (see Bound graph) contains a
  cycle of any length: a function that requires itself directly, or
  any longer chain of `requiring`-clause edges that returns to its
  starting function.
- **`bound_unsatisfied`** — a use site of a bounded function infers
  argument types whose substitution does not satisfy the bound:
  for some `gⱼ`, no declared signature of `gⱼ` is consistent with
  the substituted bound.
- **`extend_type_on_bounded_function`** — `:- extend_class_type`
  targets a bounded `:- open_function`. The instance set of a
  bounded open function is determined by its bound's named
  functions, not by enumerated extensions. Note that the
  kind-mismatch check (`ExtendClassTypeOnFunction`, YCHR-16013)
  also fires on this combination, since a `:- extend_class_type`
  must target an `:- open_class`.

No new error code is introduced for the equation-checking path;
equations either type-check under the enlarged context or fail with
existing error codes. Likewise, no new error code is introduced for
the constraint case: the existence check, cycle detection, and
unbound-variable check are structurally identical to the function
case and share their error codes.

### Worked examples

**Example 1 — Polymorphic `max`.**

```prolog
:- function ('>'(int, int) -> bool), ('>'(float, float) -> bool).
:- function max(T, T) -> T requiring '>'(T, T) -> bool.

max(X, Y) | X > Y -> X.
max(_, Y)         -> Y.
```

Equation checking: `T` is fresh; `X : T`, `Y : T`. The guard `X > Y`
calls `>`; the bound provides `>(T, T) -> bool` as an ambient
signature; the call types as `bool`. The RHS `X : T` matches the
return type `T`. Both equations check.

Use site `R is max(3, 4)`: σ = (T := int); the substituted bound
`>(int, int) -> bool` is consistent with the declared signature;
result type `int`; `R : int`.

Use site `R is max("a", "b")`: σ = (T := string); the substituted
bound `>(string, string) -> bool` has no consistent declared
signature; error `bound_unsatisfied`.

**Example 2 — Multi-variable bound.**

```prolog
:- function ('=='(int, int) -> bool).
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
`bound_unsatisfied` for the substituted bound at K := float.

**Example 3 — Bounded function as a single point of truth.**

```prolog
:- function ('+'(int, int) -> int).
:- function double(T) -> T requiring '+'(T, T) -> T.

double(X) -> X + X.
```

Equation checks parametrically: `X : T`; `X + X` resolves through
the ambient bound `+(T, T) -> T` to `T`; RHS type `T` matches return
`T`.

`double(3)` succeeds at σ = (T := int); declared `+(int, int) -> int`
satisfies the bound. `double("hi")` fails as `bound_unsatisfied`
because no `+(string, string) -> string` has been declared.

A later module that declares `+(float, float) -> float` automatically
extends the admissible instance set of `double` — no edit to
`double`'s declaration is needed. This is the open-set property of
bounded polymorphism.

### Interaction with `any`

`any` interacts with bounds the same way it interacts with ordinary
overloading:

- A use site whose argument types are `any` makes σ partial; the
  bound check succeeds silently and the call's result type
  substitutes through to `any` or to a fresh variable, exactly as in
  ordinary overload resolution under unresolved arguments.
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

The semi-formal paper-proof methodology described in §Soundness
extends straightforwardly: bound checking is itself expressed as
ordinary use-site overload resolution, and inherits those rules'
confluence and gradual properties.

The same properties hold for bounded constraints. No new soundness
argument is required: rule-level ambient signatures are a structural
mirror of equation-level ambient signatures, and the use-site
mechanism is shared. The union of multiple bounded constraints'
ambient signatures within a single rule is sound because each
occurrence's type variables are freshly allocated per rule
(§Use sites), so contributed signatures cannot collide on shared
variable identities.


## Extensibility

The type system is designed to accommodate future extensions:

- **Predicate-based refinement types**: guards like `integer(X)` could
  narrow the type of `X` from `any` to `int`.

- **Advanced refinement types**: the consistency-based framework and
  constraint-gathering approach can be extended with subtyping or
  predicate constraints without changing the overall architecture.


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
| Built-in types | `int`, `float`, `string`, `any` |
| User-defined types | Algebraic types via `:- chr_type` |
| Function types | `fun(τ₁,...,τₙ) -> τᵣ` |
| Polymorphism | Parametric, implicitly quantified, no rank-n |
| Overloading | Multi-signature overloading via `:- class` / `:- open_class` |
| Defaults | Missing annotations default to `any` |
| Core relation | Consistency (gradual typing) |
| Type merging | Consistency check, `any` absorbs |
| Solving | Constraint gathering, order-independent |
| Inline annotations | Not supported; types only in declarations |
| Host calls | All `any`; operators typed via library signatures |
| Constructors | Looked up in type definitions; unknown → `any` |
| Disambiguation | Module qualification |
| Soundness | Gradual guarantee; paper proof sufficient |
