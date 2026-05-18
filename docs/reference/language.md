# YCHR Language Reference

YCHR accepts standard CHR with Prolog-compatible syntax: constraint
declarations, simplification rules (`<=>`), propagation rules (`==>`),
simpagation rules (`\`), guards, and rule bodies. This document
describes the ways YCHR diverges from the K.U.Leuven CHR-in-Prolog
dialect.

For the surface grammar (lexical conventions, the full directive
table, the rule and expression forms), see
[syntax.md](syntax.md). For the optional static type checker see
[type-system.md](type-system.md).

## Modules

Every program is organized into modules. A module declares its name
and its export list, and may import other modules:

```
:- module(order, [leq/2]).
:- use_module(library(lists)).
:- chr_constraint leq/2.

reflexivity   @ leq(X, X) <=> true.
antisymmetry  @ leq(X, Y), leq(Y, X) <=> X = Y.
idempotence   @ leq(X, Y) \ leq(X, Y) <=> true.
transitivity  @ leq(X, Y), leq(Y, Z) ==> leq(X, Z).
```

A module may also be declared without an export list:

```
:- module(order).
```

This form exports every constraint, function, type, and operator
declared in the module. It does not re-export imports.

Constraint and function names are qualified with their defining
module; unqualified references in source are resolved against the
module's imports. The same qualification applies to data
constructors and atoms: `palette:red` names the `red` constructor of
the `palette` module. If two imports both export an identifier of
the same name and arity, an unqualified use is rejected and the user
must disambiguate.

`:- use_module(M)` and `:- use_module(library(M))` are equivalent: the
`library(...)` wrapper is accepted as a Prolog-source compatibility
shim and resolves to the same module. There is no separate library
search path.

### Type and constructor exports

A user-defined type is declared with `:- chr_type` (see
[type-system.md](type-system.md) for the full spec):

```
:- chr_type col ---> red ; green ; blue.
```

The type is exported with `type(Name/Arity)`, where *Arity* is the
number of type parameters (not the number of constructors). By default
this also exports every data constructor of the type. To export the
type while restricting which constructors are visible to importing
modules, use the two-argument form
`type(Name/Arity, [Con1, Con2, ...])`:

```
:- module(palette, [type(col/0)]).         % all constructors of col
:- module(palette, [type(col/0, [red])]).  % only `red`
:- module(palette, [type(col/0, [])]).     % type but no constructors
```

The same form is accepted in `use_module` import lists, where it
intersects with the exporter's allowlist:

```
:- use_module(palette, [type(col/0, [red])]).
```

If a constructor named in either list is not declared on the type (or,
on the import side, is not in the exporter's allowlist), the program is
rejected with `YCHR-20008`.

## Constraints

Constraints are declared with `:- chr_constraint`. The arity-only
form is the standard CHR shape:

```
:- chr_constraint leq/2.
```

When the type checker is in use, the same declaration can carry
argument types — the arity is then inferred from the number of
positions:

```
:- chr_constraint leq(int, int).
:- chr_constraint sorted(list(T)) requiring lt(T, T) -> bool.
```

The `requiring` clause attaches *bounds* — required function
signatures that must be in scope at the concrete instantiation of a
type variable. See [type-system.md](type-system.md) for what bounds
mean and when they are discharged.

Multiple declarations may share one directive:
`:- chr_constraint a/1, b/2.`

## Functions

When CHR is embedded in Prolog, guards rely on predicate success or
failure. In YCHR, guards are functional expressions that return a
boolean. They can call host-language procedures (see
[Host calls](#host-calls) below) or user-defined *functions*.

Functions are declared with `:- function` and defined with Erlang-style
equations using `->`, evaluated top-to-bottom by pattern matching:

```
:- function member/2.

member(_, [])     -> false.
member(X, [X|_])  -> true.
member(X, [_|Xs]) -> member(X, Xs).
```

Equation patterns match exactly like rule heads: the same
head-normal-form machinery normalizes both. Repeated variables become
implicit equality guards, nested compound patterns and literal
patterns become explicit match-and-extract steps. A pattern with
literal `0` matches only the integer 0; a pattern with `[X | Xs]`
matches only a non-empty cons cell.

Guard clauses on equations are written with `|`, and use the same
ask-semantics as rule guards (no variable binding, comma-separated
boolean expressions, may call any function in scope):

```
:- function factorial/1.

factorial(0)              -> 1.
factorial(N) | N > 0      -> N * factorial(N - 1).
```

Functions are callable everywhere an expression evaluates — see
[Tell-side evaluation](#tell-side-evaluation) for the full list. If
no equation matches, a runtime error is raised.

### `:- function` vs `:- class`

`:- function` declares a single-signature function. To overload a
function across multiple types, use `:- class`:

```
:- class
    (size(int) -> int),
    (size(string) -> int).

size(N) | integer(N) -> N.
size(S) | string(S) -> string_length(S).
```

Each `size` equation is part of the single shared equation set;
top-to-bottom pattern-and-guard matching picks one at evaluation time.
The signature list tells the type checker which `(arg-types,
return-type)` combinations are legal; the equations are not
partitioned per-signature.

A `:- function` declaration with more than one typed signature is an
error (`MultiSigOnFunction`, YCHR-16011); use `:- class` instead. A
`:- class` may also carry a single signature — verbose, but legal.
The cross-module pair `:- open_function` / `:- open_class` mirrors
the closed forms: only `:- open_class` accepts new type signatures
(via `:- extend_class_type`); `:- open_function` accepts only
new equations (via `:- extend_function`).

Bounded polymorphism (`requiring`) is reserved for `:- function` and
`:- open_function`; combining it with `:- class` / `:- open_class` is
rejected as `RequiringOnClass` (YCHR-15005).

```
:- function pick(T, T) -> T requiring '>'(T, T) -> bool.
```

### Declaration placement

All declarations for one name must live in a single module, and the
declaration group plus its equations must be a contiguous block of
module items. Splitting declarations across the module is
`DiscontiguousFunctionDecls` (YCHR-15004); interleaving equations
with unrelated items is `DiscontiguousEquations` (YCHR-15001). For
extension across modules, use `:- open_function` / `:- open_class`
plus `:- extend_function` / `:- extend_class` / `:- extend_class_type`.

## Tell-side evaluation

YCHR evaluates expressions in many positions that standard CHR
treats symbolically. A compound term whose head names a declared
function becomes a function call and runs at that point; a compound
term whose head names a data constructor becomes a value of that
constructor.

**Evaluating positions:**

- Rule body constraints (tell-side): `c(1 + 2)` stores `c(3)`.
- Top-level goals.
- Function and constructor arguments inside any of the above.
- The right-hand side of `is` and `=`.
- Rule guards and equation guards.
- Function equation right-hand sides.

**Non-evaluating positions:**

- Rule heads and equation patterns: these match on data shapes; a
  pattern like `f(g(X))` matches a compound whose argument is itself
  a compound, regardless of what `g` resolves to.
- Inside `term(...)` (see below).

For instance, given:

```
:- chr_constraint store/1, ask/1.
store(X), ask(R) <=> R = X.
```

calling `store(1 + 2), ask(R)` stores `store(3)` (not `store(1 + 2)`),
and the second rule then unifies `R = 3`. The same applies to
function calls: `store(member(1, [0, 1, 2]))` stores `store(true)`.

### The `term/1` quoting form

The opt-out for users who want to pass an unevaluated data term is the
`term(...)` quoting form:

```
store(term(plus(2, 3)))   % stored as store(plus(2, 3))
```

`term` is a reserved name — you cannot declare `:- function term/1.`
or `:- chr_constraint term/1.`. The form may appear in any
evaluating position (constraint arguments, `is` RHS, function-call
arguments, …) and may nest: an expression inside `term(...)` is
itself parsed as a surface term, and unbound logical variables inside
become part of the resulting term value without erroring.

In head and equation patterns `term(X)` is treated like any other
compound — heads never evaluate, so the quoting form has no
additional effect there.

### Tell-time evaluation errors

Evaluation is eager. There is no auto-suspension or symbolic
fallback: an unbound logical variable flows through user-defined
function calls as an ordinary value, but the moment something
demands a concrete value (most commonly a host-language operation
like arithmetic or comparison) the evaluation runtime-errors. The
Haskell interpreter surfaces this as `YCHR-60001`. Use `term(...)`
to keep an expression symbolic until something else binds the
variables.

## The `is` operator

`is` is generalized to accept any expression on the RHS, including
calls to user-defined functions and host-language functions.

```
ychr> R is member(1, [0, 1, 2]).
R = true.
```

Unlike standard Prolog (where `is` shares priority 700 with the
comparison operators), YCHR's `is` and `=` sit at priority 750 (still
`xfx`). This places them just above the comparisons, so a comparison
on the RHS no longer needs parentheses:

```
ychr> B is 1 < 2.
B = true.
```

## Lambdas and function references

Anonymous functions use Erlang-style syntax with `end` delimiting the
body, so lambdas can appear inside compound-term arguments without
extra parentheses:

```
:- function apply/2.
apply(F, X) -> call(F, X).

result(R) <=> R is apply(fun(X) -> X + 1 end, 5).
```

Lambda parameters are restricted to variables and wildcards. Pattern
matching on lambda arguments is not supported; if you need pattern
dispatch, use a named function declared with `:- function` and
multiple equations.

Lambdas are first-class values: they can be passed as arguments,
returned from functions, and called via the prelude's `call/N`. They
capture free variables from the enclosing scope *by value* (the
captured values are taken at the moment the lambda expression is
evaluated, then passed as extra hidden parameters to a lifted
top-level function):

```
:- function make_adder/1.
make_adder(N) -> fun(X) -> X + N end.
```

Named functions are referenced by `fun name/arity` (e.g.
`fun member/2`) and become first-class values the same way.

### `call` and `'$call'`

The prelude exports a typed `call/N` family that is the everyday way
to invoke a lambda or function reference:

```
R is call(fun(X) -> X + 1 end, 5).
R is call(fun double/1, 10).
```

`call` is itself defined as a thin wrapper over the wired-in primitive
`'$call'(F, A1, ..., An)`. `'$call'` is recognized directly by the
renamer; the `'$'` prefix is not part of any naming convention and `$`
is not reserved for other primitives. Reach for `'$call'` only when
working below the typed `call` wrapper.

## Host calls

YCHR programs reach into the host language with the `host:` qualifier:

```
X + Y -> host:'+'(X, Y).
```

`host:` is a wired-in qualifier, not a real module; the resolver
intercepts it and dispatches to whatever host-language function the
name denotes. Host calls may appear in any evaluating position —
function equation bodies (as above), `is` right-hand sides, guards,
and constraint arguments. Argument values are evaluated normally
before they reach the host; the host return value flows back as an
ordinary YCHR value.

The prelude already wraps every host arithmetic, comparison, and
string operation it relies on, so most programs never need to write
`host:` directly.

## Optional static type checking

Programs may annotate constraints and functions with type signatures.
The type checker is gradual: programs without annotations are accepted
unchanged. See [type-system.md](type-system.md) for the full
specification, including the type language, bounded polymorphism, and
inference rules.
