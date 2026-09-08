# YCHR Language Reference

> **Audience:** readers who know CHR and want to know where YCHR
> departs from it.
> **You will:** find the feature-level rules for modules, constraints,
> functions, evaluation, and host calls.
> **Skip if:** you are learning CHR itself — start with the
> [CHR primer](../tutorials/02-chr-primer.md).

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

A YCHR program is organized into modules. A module *may* declare its
name and its export list, and may import other modules:

```prolog
:- module(order, [leq/2]).
:- use_module(library(lists)).
:- chr_constraint leq/2.

reflexivity   @ leq(X, X) <=> true.
antisymmetry  @ leq(X, Y), leq(Y, X) <=> X = Y.
idempotence   @ leq(X, Y) \ leq(X, Y) <=> true.
transitivity  @ leq(X, Y), leq(Y, Z) ==> leq(X, Z).
```

A module may also be declared without an export list:

```prolog
:- module(order).
```

This form exports every constraint, function, type, and operator
declared in the module. It does not re-export imports.

The `:- module(...)` directive itself is optional. A file with no
module header forms an *unnamed* module that exports every constraint,
function, type, and operator it declares — the same visibility rule
as `:- module(Name).` without the name. Diagnostics refer to such a
module by its file basename in angle brackets (`<a>` for `a.chr`).
This form is intended for single-file programs and ad-hoc scripts;
combining multiple header-less files in one program is supported,
but unqualified references to a name declared in more than one
unnamed module are ambiguous and rejected.

Constraint and function names are qualified with their defining
module; unqualified references in source are resolved against the
module's imports. The same qualification applies to data
constructors and atoms: `palette:red` names the `red` constructor of
the `palette` module. If two imports both export an identifier of
the same name and arity, an unqualified use is rejected and the user
must disambiguate.

Qualifying a name does *not* bypass the import requirement: a
reference `m:name` is valid only if the current module imports `m`
(via `:- use_module(m)`) and `m` exports `name`. Referencing an
unimported but existing module is rejected as `YCHR-20014`
(`ModuleNotImported`); referencing a module that does not exist at all
is rejected as `YCHR-20015` (`UnknownModule`); referencing an imported
module that lacks the export is `YCHR-20009` (`NotExportedByModule`).

`:- use_module(M)` and `:- use_module(library(M))` are equivalent: the
`library(...)` wrapper is accepted as a Prolog-source compatibility
shim and resolves to the same module. There is no separate library
search path.

### Type and constructor exports

A user-defined type is declared with `:- chr_type` (see
[type-system.md](type-system.md) for the full spec):

```prolog
:- chr_type col ---> red ; green ; blue.
```

The type is exported with `type(Name/Arity)`, where *Arity* is the
number of type parameters (not the number of constructors). By default
this also exports every data constructor of the type. To export the
type while restricting which constructors are visible to importing
modules, use the two-argument form
`type(Name/Arity, [Con1, Con2, ...])`:

```prolog
:- module(palette, [type(col/0)]).         % all constructors of col
:- module(palette, [type(col/0, [red])]).  % only `red`
:- module(palette, [type(col/0, [])]).     % type but no constructors
```

The same form is accepted in `use_module` import lists, where it
intersects with the exporter's allowlist:

```prolog
:- use_module(palette, [type(col/0, [red])]).
```

If a constructor named in either list is not declared on the type, the
program is rejected with `YCHR-20008`. On the import side, a constructor
that is declared on the type but excluded by the exporter's allowlist is
rejected with `YCHR-20011` (a separate code so users can distinguish
"misspelled or unknown" from "declared but not visible").

The allowlist also governs qualified references: writing `palette:green`
in a rule, guard, or expression is rejected with `YCHR-20010` when
`green` is declared on `col` but not in `palette`'s export allowlist.
Bare and qualified syntax see the same view of the module.

### Opaque types

An *opaque type* is a nominal type with no data constructors, declared
with `:- opaque_type` and introduced or eliminated only by the
functions declared over it — see
[type-system.md](type-system.md#opaque-types) for the declaration form
and typing rules. Opaque types share the type namespace with algebraic
types, so they are exported (and imported) with the same
`type(Name/Arity)` form. Since there are no constructors, the
`type(Name/Arity, [...])` allowlist form is not useful for one (a
named constructor is rejected as unknown, `YCHR-20008`).

## Constraints

Constraints are declared with `:- chr_constraint`. The arity-only
form is the standard CHR shape:

```prolog
:- chr_constraint leq/2.
```

When the type checker is in use, the same declaration can carry
argument types — the arity is then inferred from the number of
positions:

```prolog
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

```prolog
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

```prolog
:- function factorial/1.

factorial(0)              -> 1.
factorial(N) | N > 0      -> N * factorial(N - 1).
```

Functions are callable everywhere an expression evaluates — see
[Tell-side evaluation](#tell-side-evaluation) for the full list. If
no equation matches, a runtime error is raised.

### Sequencing in function bodies

A function body may also be a comma-separated sequence. The last item
is the return expression; earlier items run for their effect or to
bind a value before the return is computed:

```prolog
:- function factorial/1.

factorial(0)         -> 1.
factorial(N) | N > 0 ->
    host:print(N),
    Prev is factorial(N - 1),
    N * Prev.
```

Items are evaluated strictly left-to-right. A non-final item must be
one of:

- An `is` binding `X is E`. The left-hand side must be a variable
  (function bodies have no unification machinery); a non-variable LHS
  is rejected (`NonVariableIsInFunctionBody`, YCHR-30004).
- A host call `host:f(args)`. Its return value is discarded.
- A function call `f(args)` or `'$call'(F, args)`. The return value
  is discarded.

Anything else — including `=` unification, a CHR tell, `true`, or a
bare expression like `(A, B)` — is rejected
(`NonPreludeFunctionBodyItem`, YCHR-30003) with a hint pointing at the
offending item. The single-expression body (the form without commas)
is the degenerate case and continues to work unchanged.

Comma at the top of the body is always a sequencer, even when written
in functor form (`','(A, B)`); both surface forms parse to the same
compound. To return a `,/2` constructor value, wrap it in `quote/1`:
`f() -> quote(','(foo, bar)).`

An `is` binding may shadow a parameter or an earlier binding of the
same name. The RHS sees the *old* value; subsequent statements and the
return expression see the new one. This is lexical shadowing — there
is no unification with the previous slot — so `f(X) -> X is X + 1, X.`
is well-typed even when `X` and `X + 1` have different types.

Lambdas (`fun(X) -> ... end`) accept the same sequenced form:

```prolog
make_doubler() -> fun(X) -> Y is X + 1, Y * 2 end.
```

### `:- function` vs `:- class`

`:- function` declares a single-signature function; giving it more
than one typed signature is rejected (YCHR-16011). To overload a name
across several type signatures, declare it with `:- class`; the
equations still form one shared, top-to-bottom matched set. The
cross-module pair `:- open_function` / `:- open_class` mirrors the
closed forms. Bounded polymorphism (`requiring`) is allowed on
`:- function` / `:- open_function` / `:- chr_constraint`, but never
on the class forms (YCHR-15005 on a class). See
[type-system.md](type-system.md#signature-overloading) for the
overloading rules and examples.

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
- The right-hand side of `is`.
- Rule guards and equation guards.
- Function equation right-hand sides.

**Non-evaluating positions:**

- Operands of `=` — `=` is pure structural unification; see
  [The `=` operator](#the--operator).
- Rule heads and equation patterns: these match on data shapes; a
  pattern like `f(g(X))` matches a compound whose argument is itself
  a compound, regardless of what `g` resolves to.
- Inside `quote(...)` (see below).

For instance, given:

```prolog
:- chr_constraint store/1, ask/1.
store(X), ask(R) <=> R = X.
```

calling `store(1 + 2), ask(R)` stores `store(3)` (not `store(1 + 2)`),
and the second rule then unifies `R = 3`. The same applies to
function calls: `store(member(1, [0, 1, 2]))` stores `store(true)`.

### Constructor and function names must not collide

A compound's head is what chooses between the two readings above — a
function call or a constructor application — so a name may not mean
both. Concretely:

- Declaring a data constructor and a function with the same name in
  **one module** is `ConstructorFunctionCollision` (`YCHR-16020`).
  Both would spell as `mod:name`, so nothing could tell them apart.
- Referring to a name that is visible as a constructor from one module
  and as a function from another, **without qualifying it**, is
  `ConstructorFunctionAmbiguity` (`YCHR-20020`).

Arity is not part of the comparison on either side: data constructors
are name-only in the type system, so `foo/0` the constructor clashes
with `foo/1` the function. Every module imports the prelude in full,
so no constructor may be referred to bare under a name the prelude
declares as a function (`var`, `float`, `string`, `atom`, `not`, …).

The cross-module case has an escape hatch — qualifying the reference
names exactly one thing:

```prolog
:- use_module(node).   % declares the constructor leaf/1
:- use_module(grow).   % declares the function    leaf/1

build(N, R) <=> show(node:leaf(grow:leaf(N)), R).
```

Since the prelude's import cannot be narrowed (`YCHR-20019`), a clash
with a prelude function is resolved by renaming your own constructor.

A `fun name/arity` reference is not affected: that syntax names the
callable namespace outright, so `fun leaf/1` is the function whatever
constructors are in scope. Neither is `quote(...)`, whose contents are
opaque data throughout.

A constraint may share a name with a data constructor. Nothing is
ambiguous there: a compound is never read as a constraint call, so the
two never compete for the same reading.

### The `quote/1` quoting form

`quote(...)` passes a term unevaluated:

```prolog
store(quote(plus(2, 3)))   % stored as store(plus(2, 3))
```

`quote` is a reserved name — you cannot declare `:- function quote/1.`
or `:- chr_constraint quote/1.`. The form may appear in any
evaluating position (constraint arguments, `is` RHS, function-call
arguments, …) and may nest: an expression inside `quote(...)` is
itself parsed as a surface term, and unbound logical variables inside
become part of the resulting term value without erroring.

In a *tell* argument, a quoted subtree may also introduce a variable
the enclosing rule has not bound, exactly as an `=` operand does:

```prolog
h(X) <=> store(quote(pair(X, Y))).   % Y is a fresh logical variable
```

A tell argument is where a term is built to be stored, so a name
appearing in one for the first time is a new slot rather than a
mistake. Elsewhere — an `is` right-hand side, a function-call
argument, a guard — an unbound name is still `YCHR-40002`.

In head and equation patterns `quote(X)` is treated like any other
compound — heads never evaluate, so the quoting form has no
additional effect there.

The body of `quote(...)` is also opaque to module-visibility checks:
qualified atoms inside are not validated against the per-module
constructor allowlist or any other namespace, so the form is the
supported way to construct synthetic qualified atoms (e.g. as
type-tag values) when no corresponding exported declaration exists.
Outside `quote(...)`, a qualified reference `M:n` must resolve to a
visible value-level identifier — function, constraint, or data
constructor — in `M` (see §Type and constructor exports).

### Tell-time evaluation errors

Evaluation is eager. There is no auto-suspension or symbolic
fallback: an unbound logical variable flows through user-defined
function calls as an ordinary value, but the moment something
demands a concrete value (most commonly a host-language operation
like arithmetic or comparison) the evaluation runtime-errors. The
Haskell interpreter surfaces this as `YCHR-60001`. Use `quote(...)`
to keep an expression symbolic until something else binds the
variables.

Such failures come in two kinds, and the distinction is what the next
section builds on:

- an **instantiation failure** — the computation reached a point where
  it had to know the value of a variable that is still unbound, so no
  verdict was possible;
- a **general failure** — everything else: a definite mismatch, a type
  error, division by zero, an arity mismatch.

Selecting a function equation is one such demand, and it reports the
inconclusive case separately from a definite mismatch: a pattern test
reached with an unbound variable at the position it inspects raises
"argument *K* of `M:f/N` is not sufficiently instantiated to select an
equation" (an instantiation failure), where a fully instantiated
argument that no equation covers raises "no matching equation in
`M:f/N`" (a general failure). `'$call'` makes the same distinction for
an unbound closure operand. A *user-written* equation guard that is
decided on values already in hand is a definite mismatch — failing
`pos(N) | N > 0` on `pos(0)` is a general mismatch, and dispatch moves
on to the next equation.

Dispatch stops at an equation's first failing test, so the argument the
message names is the first one that blocked, not necessarily the only
one that would have.

Outside a rule guard both kinds are hard errors; only the diagnosis
differs. Inside a rule guard an instantiation failure is caught and
turned into a silent "not now" — see the next section.

### Soft guard failure

A **rule guard** — the conjunction between `|` and the rule body in a
simplification, propagation or simpagation rule — is evaluated with
instantiation failures caught. If evaluating the guard raises an
instantiation failure, the guard evaluates to **false**: the rule does
not fire for that combination of constraints, no diagnostic is
produced, and solving carries on. When the missing variable is bound
later, the ordinary constraint-reactivation mechanism re-activates the
stored constraint and the occurrence is tried again — this time with a
value in hand.

```prolog
:- chr_constraint c(int), mk(int), out(int), later(int).

m @ mk(_)    <=> c(E), later(E).   % c is stored while E is unbound
l @ later(E) <=> E = 1.
r @ c(N)     <=> N > 0 | out(N).   % N unbound at the first activation
```

Rule `r` is tried while `N` is free. `>` demands a value, raises an
instantiation failure, and the guard yields false — so `r` does not
fire and `c(E)` stays stored. Rule `l` then binds `E`, which
reactivates `c`, and `r` is retried with `N = 1`: the guard succeeds
and `out(1)` is told.

This is default-on for every rule guard; there is no opt-in or opt-out
syntax, and no new surface form. It gives guards a logic-language-like
delaying behaviour without a mode system.

#### The demand-driven principle

Instantiation failures are **demand-driven**: one is raised only when a
computation actually demands the value of an unbound variable, never
from the mere presence of an unbound variable in an argument list.

Concretely, an unbound variable that is only carried around does not
delay anything:

- a *pass-through* function argument (`id(X) -> X.`) flows freely;
- an *ignored* argument (`fst(pair(A, _)) -> A.` applied to
  `pair(1, U)` with `U` unbound) flows freely;
- data construction (`quote(...)`, constructor application, `=`)
  never demands a value;
- primitives that are total on unbound values — `==`, `unifiable`, the
  type predicates (`var`, `nonvar`, `ground`, `integer`, `atom`, …),
  `term_variables`, `copy_term` — answer normally and never raise.

A demand point is one of:

| Demand point | Example |
|---|---|
| Function-equation dispatch inspecting an unbound argument position | `length([1\|T])` with `T` unbound |
| `'$call'` on an unbound closure operand | `'$call'(F, 1)` with `F` unbound |
| A strict host primitive reaching its failure path with an unbound argument | `N > 0`, `X + 1`, `string_length(S)` |
| A host function whose marshalling reports `UnboundValue` | `host:f(X)` with `X` unbound |
| A rule guard that evaluates to an unbound variable | `c(B) <=> B \| body.` with `B` unbound |

The host primitives below are strict scalar operations with no ignored
arguments, which is why "an unbound argument on the failure path" is a
sound reading of "the value was demanded" for them specifically:

| Primitives | On an unbound argument |
|---|---|
| `+`, `-`, `*` | instantiation failure |
| `div`, `mod`, `rem` | instantiation failure |
| `/` | instantiation failure |
| `<`, `>`, `=<`, `>=` | instantiation failure |
| `int_to_float`, `float_to_int` | instantiation failure |
| `string_concat`, `string_length`, `string_upper`, `string_lower` | instantiation failure |
| `write`, `writeln` | instantiation failure |
| `compound_to_list`, `list_to_compound` | instantiation failure |
| `name_base` | instantiation failure |
| `==`, `unifiable` | answers normally (never raises) |
| `var`, `nonvar`, `ground`, `integer`, `float`, `atom`, `boolean`, `string` | answers normally (never raises) |
| `term_variables`, `copy_term` | answers normally (never raises) |

**Precedence.** When a call is both under-instantiated and ill-typed —
`X + "foo"` with `X` unbound — the instantiation diagnosis wins. In a
rule guard that means the rule delays; once `X` is bound, the type
error surfaces as a hard general failure.

**Unbound guard result.** A guard position demands a boolean, so a
guard whose value is an unbound variable is an instantiation failure
and delays:

```prolog
r @ c(B) <=> B | out(1).      % B unbound: delays; B bound to true: fires
```

A guard that evaluates to a *bound* non-boolean (an integer, say)
is a general failure and stays a hard error ("guard did not evaluate
to a boolean").

#### The catch boundary

The catch is placed at exactly one point: the rule-guard residual of a
rule occurrence. It is not a general handler.

- It is **not** applied inside function bodies. Within a function, an
  instantiation failure raised by an equation guard, or by a nested
  call, propagates out immediately; later equations are *not* tried.
  Dispatch is monotonic: a definite mismatch moves to the next
  equation, a cannot-decide aborts the call. The failure then travels
  out to whatever demanded the function's value — and if that was a
  rule guard, it is caught there.
- Because the boundary is the whole guard, a failure raised deep
  inside a recursive call is caught the same as one raised at the top
  level. `r @ c(L) <=> length(L) > 0 | body.` on a partial list
  `[1|T]` delays, even though the failure comes from `length`'s
  recursive dispatch.
- `is` expressions, rule bodies and top-level goals are *not* guard
  positions. An instantiation failure there is a hard `YCHR-60001`.
- `run_chr_session/1` keeps its own boundary: it runs an isolated
  sub-session and already reports *any* failure as `false`.

A guard never tells. `=`, constraint additions and the rest of the
body forms are not guard syntax, and a function called from a guard
cannot tell either — so abandoning a half-evaluated guard leaves the
constraint store, the propagation history and the reactivation queue
exactly as it found them. That is what makes catching sound.

The one thing a guard can do that outlives it is call a host function
that binds a variable it was handed — `run_chr_session/1` does this
deliberately, as its result channel. Those bindings persist, but they
persist equally when a guard simply evaluates to false, so this is a
property of putting an effectful host call in a guard rather than
anything the delaying introduces. If the distinction matters to you,
keep effectful host calls in rule bodies, where they run once and only
when the rule fires.

#### Interaction with reactivation and the propagation history

A retry is possible because of two properties of the generated code:

- the propagation history is consulted *after* the guard, so a guard
  that delayed leaves no history entry to block a later firing;
- the active constraint is only killed inside the fire block, so a
  delayed rule leaves the constraint stored and observing its
  variables.

A stored constraint that has occurrences to run is registered as an
observer of every unbound variable reachable from its arguments,
including variables nested inside compound terms, so binding the
variable pushes the constraint onto the reactivation queue and its
occurrences run again.

#### Non-guarantees

Soft guard failure delays a rule; it does not implement coroutining.
In particular:

- **No retry without an observer.** The retry comes from constraint
  reactivation, so some *stored* constraint must observe the variable
  that was missing. A guard that delays on a variable reachable only
  from, say, a global or a value constructed inside the guard is never
  retried.
- **Passive occurrences are not retried.** Occurrences the compiler
  proved can never fire are not generated, and reactivation only runs
  the generated ones.
- **No failure is reported.** A rule that delays for ever is
  indistinguishable from a rule whose guard was simply false. If a
  query silently produces fewer bindings than expected, an unbound
  variable at a guard is a candidate explanation.
- **A delayed rule is not fair.** The retry happens on the next
  activation, in ordinary ωr order; there is no separate wake-up
  queue or priority.

## Disjunction in rule bodies

`;` separates two alternative body conjunctions. It is an infix
operator at priority 1100, `xfy`, so it binds looser than `,`:

```prolog
h(X) <=> p(X), (b(X) ; c(Y), d(X, Y)), q(X).
```

The module must import `library(search)`; otherwise the disjunction is
rejected as `YCHR-20021`. `;` records a choice point rather than
branching where it is written — in the rule above, `q(X)` is told
before either alternative is picked, and the choice is made at
quiescence by the search driver.

`;` is a rule-body form only. In a guard, an `is` right-hand side, or a
function body it is rejected (`YCHR-20022`), and at the top level of a
query it is rejected (`YCHR-30006`). Inside `quote/1` it stays ordinary
data, and the search driver reads it as a choice at run time.

The full semantics — how disjuncts are lifted, which variables they
share, and why `=` inside a disjunct is still a hard error — are in
[the search reference](search.md#disjunction-).

## The `=` operator

`=` is pure structural unification — neither operand evaluates. A
compound on either side is treated as data, even when its head names
a declared function or host call. Variables appearing anywhere in
either operand are unification slots: if the name is not already in
scope it is introduced as a fresh logical variable and the unifier
binds it.

```prolog
test(R) <=> Y = 10, R = Y.                       % Y introduced by '='
test(R1, R2) <=> pair(X, Y) = pair(1, 2),        % X, Y introduced under ctor
                 R1 = X, R2 = Y.
test(R) <=> R = 1 + 1.                           % R bound to compound '+(1, 1)'
test(R) <=> R = double(YY).                      % R bound to compound 'double(YY)';
                                                 % YY allocated as a fresh var
```

Use `is` when you want to evaluate arithmetic, call a function for
its return value, or otherwise reduce an expression — see
[The `is` operator](#the-is-operator). The same `=` policy applies
in rule bodies and queries.

## The `is` operator

`is` is generalized to accept any expression on the RHS, including
calls to user-defined functions and host-language functions.

```ychr-repl
ychr> R is member(1, [0, 1, 2]).
R = true.
```

Unlike standard Prolog (where `is` shares priority 700 with the
comparison operators), YCHR's `is` and `=` sit at priority 750 (still
`xfx`). This places them just above the comparisons, so a comparison
on the RHS no longer needs parentheses:

```ychr-repl
ychr> B is 1 < 2.
B = true.
```

## Lambdas and function references

Anonymous functions use Erlang-style syntax with `end` delimiting the
body, so lambdas can appear inside compound-term arguments without
extra parentheses:

```prolog
:- function apply/2.
apply(F, X) -> call(F, X).

result(R) <=> R is apply(fun(X) -> X + 1 end, 5).
```

Lambda parameters are restricted to variables and wildcards. Pattern
matching on lambda arguments is not supported; if you need pattern
dispatch, use a named function declared with `:- function` and
multiple equations. A lambda must declare at least one parameter;
use `:- function` for a no-arg helper.

Lambdas are first-class values: they can be passed as arguments,
returned from functions, and called via the prelude's `call/N`. They
capture free variables from the enclosing scope *by value* (the
captured values are taken at the moment the lambda expression is
evaluated, then passed as extra hidden parameters to a lifted
top-level function):

```prolog
:- function make_adder/1.
make_adder(N) -> fun(X) -> X + N end.
```

Named functions are referenced by `fun name/arity` (e.g.
`fun member/2`) and become first-class values the same way.

### `call` and `'$call'`

The prelude exports a typed `call/N` family that is the everyday way
to invoke a lambda or function reference:

```prolog
R is call(fun(X) -> X + 1 end, 5).
R is call(fun double/1, 10).
```

`call` is itself defined as a thin wrapper over the wired-in primitive
`'$call'(F, A1, ..., An)`. `'$call'` is recognized directly by the
renamer; the `'$'` prefix is not part of any naming convention and `$`
is not reserved for other primitives. Use `'$call'` directly only when
working below the typed `call` wrapper.

## Host calls

YCHR programs reach into the host language with the `host:` qualifier:

```prolog
X + Y -> host:'+'(X, Y).
```

`host:` is a wired-in qualifier, not a real module; the resolver
intercepts it and dispatches to whatever host-language function the
name denotes. Host calls may appear in any evaluating position —
function equation bodies (as above), `is` right-hand sides, guards,
and constraint arguments. Argument values are evaluated normally
before they reach the host; the host return value flows back as an
ordinary YCHR value.

Because `host:` is wired in, `host` itself is reserved and cannot be
used as a user module name (`YCHR-16019`).

The prelude already wraps every host arithmetic, comparison, and
string operation it relies on, so most programs never need to write
`host:` directly.
