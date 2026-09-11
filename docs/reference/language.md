# YCHR Language Reference

YCHR accepts standard CHR with Prolog-compatible syntax: constraint
declarations, simplification (`<=>`), propagation (`==>`) and
simpagation (`\`) rules, guards, bodies. Below: where YCHR diverges
from the K.U.Leuven CHR-in-Prolog dialect. The optional
static type checker is specified in [type-system.md](type-system.md).

## Lexical syntax

- Comments: `%` to end of line. No block comments.
- Atoms: a lowercase letter, then letters, digits, `_`. `__` is
  reserved (the compiled-name separator). Prefix word operators
  (`chr_constraint`, `function`, `class`, …) must be quoted to be used
  as atoms. Quoted atoms are `'…'`: `''` for a quote, escapes `\\`,
  `\'`, `\n`, `\t`; any other `\c` is `c`. `__` and `%%u` are rejected
  inside quotes too.
- A bare atom and a 0-arity data constructor are the same value.
- Variables: an uppercase letter or `_`, then letters, digits, `_`.
  `_` alone is the wildcard; each occurrence is distinct.
- Integers: decimal digits, optional `-`, arbitrary precision. No `_`
  separators, no hex/octal/binary.
- Floats: `digits.digits`, optional `-`. No exponent.
- Strings: `"…"`, escapes `\"`, `\\`, `\n`, `\t`. Type `string`, not
  code lists.
- `:` qualifies a name with its module: `lists:append`.
- `[]`, `[a, b]`, `[H | T]` are `'.'/2` cells.

## Directives

| Directive | See |
|---|---|
| `:- module(Name, Exports).` / `:- module(Name).` | [Modules](#modules) |
| `:- use_module(M).` / `:- use_module(M, Imports).` | [Modules](#modules) |
| `:- chr_constraint Decls.` | [Constraints](#constraints) |
| `:- chr_type T ---> Cs.` / `:- opaque_type T.` | [Type and constructor exports](#type-and-constructor-exports), [type-system.md](type-system.md) |
| `:- function` / `:- open_function` / `:- class` / `:- open_class` | [Functions](#functions) |
| `:- extend_function` / `:- extend_class` / `:- extend_class_type` | [Declaration placement](#declaration-placement) |

Declaration directives take comma-separated lists:
`:- chr_constraint a/1, b/2.` Unknown directives are dropped silently
(Prolog-source compatibility, not an extension point).

## Rules

```
[Name @] Head <=> [Guard |] Body.            % simplification
[Name @] Head ==> [Guard |] Body.            % propagation
[Name @] Kept \ Removed <=> [Guard |] Body.  % simpagation
```

Heads are comma-separated constraint applications. Guards are
comma-separated boolean expressions with ask semantics (no binding);
they are expressions, not Prolog predicates, and may call
[host functions](#host-calls) or user-defined functions. Bodies are
comma-separated tells.

## Modules

A module may declare its name, its exports and its imports:

```prolog
:- module(order, [leq/2]).
:- use_module(library(lists)).
:- chr_constraint leq/2.

reflexivity   @ leq(X, X) <=> true.
antisymmetry  @ leq(X, Y), leq(Y, X) <=> X = Y.
idempotence   @ leq(X, Y) \ leq(X, Y) <=> true.
transitivity  @ leq(X, Y), leq(Y, Z) ==> leq(X, Z).
```

Without an export list:

```prolog
:- module(order).
```

This exports every constraint, function, type and operator the module
declares, and re-exports no imports. A file with no `:- module` header
is an *unnamed* module with the same visibility; diagnostics call it
`<a>` for `a.chr`. Several header-less files may be combined, but an
unqualified reference to a name declared in more than one of them is
ambiguous and rejected.

Names are qualified with their defining module; unqualified references
resolve through the module's imports. Data constructors and atoms are
qualified the same way: `palette:red`. If two imports export the same
name and arity, an unqualified use is rejected (`YCHR-20001`;
`YCHR-20012` for a data constructor). Qualify it, or, when the clash is
with the prelude, rename yours.

Qualifying does not bypass imports: `m:name` is valid only if the
current module imports `m` and `m` exports `name`. Unimported module:
`YCHR-20014` (`ModuleNotImported`). Unknown module: `YCHR-20015`
(`UnknownModule`). Imported module without that export: `YCHR-20009`
(`NotExportedByModule`).

`:- use_module(M)` and `:- use_module(library(M))` are equivalent;
there is no library search path. `:- use_module` directives come
before everything else in the file (`YCHR-20007`). The bundled
libraries `lists`, `maybe`, `pairs`, `strings`, `meta` and `search`
([`libraries/`](../../libraries/)) need an explicit import outside the
REPL. The prelude is always imported, in full; an import list on it is
rejected (`YCHR-20019`).

Operators are declared with `op(Priority, Type, Name)` entries in an
export or import list. There is no `:- op` directive.

### Type and constructor exports

A user-defined type is declared with `:- chr_type`
([type-system.md](type-system.md)):

```prolog
:- chr_type col ---> red ; green ; blue.
```

Export it with `type(Name/Arity)`, where *Arity* counts type
parameters, not constructors. That exports every constructor too;
`type(Name/Arity, [Con1, Con2, ...])` restricts which are visible:

```prolog
:- module(palette, [type(col/0)]).         % all constructors of col
:- module(palette, [type(col/0, [red])]).  % only `red`
:- module(palette, [type(col/0, [])]).     % type but no constructors
```

The same form in a `use_module` import list intersects with the
exporter's allowlist:

```prolog
:- use_module(palette, [type(col/0, [red])]).
```

A constructor named in either list but not declared on the type:
`YCHR-20008`. On the import side, a constructor declared on the type
but excluded by the exporter's allowlist: `YCHR-20011` ("declared but
not visible", distinct from "unknown"). A qualified reference
`palette:green` to a constructor outside `palette`'s allowlist:
`YCHR-20010`. Bare and qualified syntax see the same view of the module.

### Opaque types

`:- opaque_type` declares a nominal type with no data constructors,
introduced and eliminated only by the functions declared over it
([type-system.md](type-system.md#opaque-types)). Opaque types share
the type namespace with algebraic types and use the same
`type(Name/Arity)` export/import form. Naming a constructor in the
allowlist form is `YCHR-20008`.

## Constraints

The arity-only form is standard CHR:

```prolog
:- chr_constraint leq/2.
```

With the type checker, the declaration may carry argument types; the
arity is then the number of positions:

```prolog
:- chr_constraint leq(int, int).
:- chr_constraint sorted(list(T)) requiring lt(T, T) -> bool.
```

`requiring` attaches *bounds*: function signatures that must be in
scope at the concrete instantiation of a type variable
([type-system.md](type-system.md)). A constraint may not share name
and arity with a function-like declaration in the same module
(`YCHR-16016`).

## Functions

A function is declared with `:- function` and defined by Erlang-style
`->` equations, tried top-to-bottom:

```prolog
:- function member/2.

member(_, [])     -> false.
member(X, [X|_])  -> true.
member(X, [_|Xs]) -> member(X, Xs).
```

Equation patterns match exactly like rule heads (the same
head-normal-form machinery): repeated variables become equality
guards, literal and compound patterns become match-and-extract steps.
`0` matches only the integer 0; `[X | Xs]` only a non-empty cons cell.

Equation guards follow `|` and have rule-guard ask semantics: no
binding, comma-separated booleans, any function in scope:

```prolog
:- function factorial/1.

factorial(0)              -> 1.
factorial(N) | N > 0      -> N * factorial(N - 1).
```

Functions are callable in every evaluating position
([Tell-side evaluation](#tell-side-evaluation)). No matching equation
is a runtime error.

### Sequencing in function bodies

A body may be a comma-separated sequence. The last item is the result;
earlier items run strictly left-to-right, for effect or to bind:

```prolog
:- function factorial/1.

factorial(0)         -> 1.
factorial(N) | N > 0 ->
    host:print(N),
    Prev is factorial(N - 1),
    N * Prev.
```

A non-final item must be one of:

- `X is E`. The LHS must be a variable (function bodies have no
  unification); otherwise `NonVariableIsInFunctionBody`, YCHR-30004.
- A host call `host:f(args)`; the result is discarded.
- A function call `f(args)` or `'$call'(F, args)`; the result is
  discarded.

Anything else — `=`, a CHR tell, `true`, a bare `(A, B)` — is
`NonPreludeFunctionBodyItem`, YCHR-30003, with a hint at the item. A
single-expression body is the degenerate case.

A top-level comma is always a sequencer, in functor form `','(A, B)`
too. To return a `,/2` value, quote it: `f() -> quote(','(foo, bar)).`

An `is` binding may shadow a parameter or an earlier binding. The RHS
sees the old value; later items and the result see the new one. This
is lexical shadowing, not unification, so `f(X) -> X is X + 1, X.` is
well-typed even when `X` and `X + 1` differ in type.

Lambdas accept the same form:

```prolog
make_doubler() -> fun(X) -> Y is X + 1, Y * 2 end.
```

### `:- function` vs `:- class`

`:- function` takes one typed signature; more is YCHR-16011. `:- class`
overloads a name across several signatures; the equations still form
one top-to-bottom set. `:- open_function` / `:- open_class` are the
cross-module counterparts. `requiring` is allowed on `:- function`,
`:- open_function` and `:- chr_constraint`, never on a class form
(YCHR-15005). Overloading rules:
[type-system.md](type-system.md#signature-overloading).

### Refinement predicates

A closed `:- function` with the signature `name(any) -> bool` may
carry a `refining` clause naming the type a successful call proves of
its argument, as in `:- function is_list(any) -> bool refining
list(A)`. A guard calling it on a bare variable then types that
variable. The clause is an axiom the checker trusts. On any other
function-like declaration it is YCHR-16021, on a `:- chr_constraint`
YCHR-15020, and combining it with `requiring` does not parse.
Rules and rationale:
[type-system.md](type-system.md#refinement-predicates).

### Declaration placement

All declarations of one name live in one module, and the declaration
group plus its equations form a contiguous block of module items.
Split declarations: `DiscontiguousFunctionDecls`, YCHR-15004.
Equations interleaved with unrelated items: `DiscontiguousEquations`,
YCHR-15001. To extend across modules, use `:- open_function` /
`:- open_class` with `:- extend_function` / `:- extend_class` /
`:- extend_class_type`. Extending a closed declaration is YCHR-16005;
the wrong kind, YCHR-16013/16014/16015; a free-floating equation
outside the declaring module, YCHR-16006.

## Expression forms

Every expression position parses the same terms; what a term *means* is
decided at resolution (see [Tell-side evaluation](#tell-side-evaluation)).

| Form | Meaning |
|---|---|
| `42`, `-3`, `3.14`, `"text"`, `foo`, `'a-b'` | Literals. |
| `X`, `_Tail`, `_` | Variable; `_` is the wildcard. |
| `f(A, B)` | Function call, constructor, or tell, depending on what `f` resolves to. |
| `[a, b]`, `[H \| T]`, `[]` | Lists. |
| `M:name`, `M:name(A)` | Module-qualified reference. |
| `host:name(A)` | [Host call](#host-calls). |
| `quote(E)` | `E` as data, unevaluated ([`quote/1`](#the-quote1-quoting-form)). |
| `fun(X, Y) -> Body end` | Lambda; parameters are variables or wildcards. |
| `fun name/arity` | Function reference. |
| `'$call'(F, A1, A2)` | Wired-in dynamic call; prefer the prelude's `call/N`. |
| `X is E`, `X = E`, `A == B` | Evaluation, unification (tell), structural equality (ask). |
| `A ; B` | [Disjunction](#disjunction-in-rule-bodies) in a rule body. |

## Tell-side evaluation

Many positions that standard CHR treats symbolically are evaluated. A
compound whose head names a declared function is a call and runs
there; one whose head names a data constructor is a value of that
constructor.

Evaluating positions:

- rule-body constraint arguments (tell-side): `c(1 + 2)` stores `c(3)`;
- top-level goals;
- function and constructor arguments inside the above;
- the right-hand side of `is`;
- rule guards and equation guards;
- equation right-hand sides.

Non-evaluating positions:

- operands of `=` ([The `=` operator](#the--operator));
- rule heads and equation patterns, which match on shape: `f(g(X))`
  matches a compound with a compound argument whatever `g` resolves to;
- inside `quote(...)`.

A variable in an evaluating position must be bound by the rule head or
the equation's parameters (`YCHR-40002`);
`test/golden/soft_guard_hard_positions` enumerates the positions.

```prolog
:- chr_constraint store/1, ask/1.
store(X), ask(R) <=> R = X.
```

`store(1 + 2), ask(R)` stores `store(3)`, then binds `R = 3`.
`store(member(1, [0, 1, 2]))` stores `store(true)`.

### Constructor and function names must not collide

A compound's head decides between call and constructor, so a name may
not mean both:

- A data constructor and a function of the same name in **one module**:
  `ConstructorFunctionCollision`, `YCHR-16020`. Both spell `mod:name`.
- An **unqualified** reference to a name that is a constructor in one
  import and a function in another: `ConstructorFunctionAmbiguity`,
  `YCHR-20020`.

Arity is not compared: constructors are name-only in the type system,
so constructor `foo/0` clashes with function `foo/1`. The prelude is
imported in full, so no constructor may be used bare under a prelude
function name (`var`, `float`, `string`, `atom`, `not`, …); the prelude
import cannot be narrowed (`YCHR-20019`), so rename the constructor.

Across modules, qualifying names exactly one thing:

```prolog
:- use_module(node).   % declares the constructor leaf/1
:- use_module(grow).   % declares the function    leaf/1

build(N, R) <=> show(node:leaf(grow:leaf(N)), R).
```

`fun name/arity` always names the function, and `quote(...)` contents
are opaque data, so neither is affected. A constraint may share a name
with a constructor: a compound is never read as a constraint call.

### The `quote/1` quoting form

`quote(...)` passes a term unevaluated:

```prolog
store(quote(plus(2, 3)))   % stored as store(plus(2, 3))
```

`quote` is reserved: `:- function quote/1.` and
`:- chr_constraint quote/1.` are rejected. The form is allowed in every
evaluating position and nests; its contents parse as a surface term,
and unbound logical variables inside become part of the value.

In a *tell* argument a quoted subtree may introduce a variable the rule
has not bound, exactly like an `=` operand:

```prolog
h(X) <=> store(quote(pair(X, Y))).   % Y is a fresh logical variable
```

Elsewhere — an `is` right-hand side, a function argument, a guard — an
unbound name is still `YCHR-40002`. In heads and equation patterns
`quote(X)` is an ordinary compound.

Quoted contents skip module-visibility checks: qualified atoms inside
are not validated against any allowlist or namespace, which is the
supported way to build synthetic qualified atoms (type tags, say) with
no exported declaration. Outside `quote(...)`, `M:n` must resolve to a
visible function, constraint or data constructor of `M`
(§Type and constructor exports).

### Tell-time evaluation errors

Evaluation is eager; there is no auto-suspension or symbolic fallback.
An unbound logical variable flows through user-defined function calls
as an ordinary value, but the moment something demands a concrete
value (typically a host operation such as arithmetic or comparison)
evaluation fails — `YCHR-60001` on the Haskell interpreter. Use
`quote(...)` to keep an expression symbolic.

Failures come in two kinds:

- an **instantiation failure** — a value was demanded of a variable
  that is still unbound, so no verdict was possible;
- a **general failure** — everything else: a definite mismatch, a type
  error, division by zero, an arity mismatch.

Equation selection is such a demand and reports the two separately: a
pattern test that meets an unbound variable at the position it
inspects raises "argument *K* of `M:f/N` is not sufficiently
instantiated to select an equation" (instantiation); a fully
instantiated argument no equation covers raises "no matching equation
in `M:f/N`" (general). `'$call'` does the same for an unbound closure
operand. A user-written equation guard decided on values in hand is a
definite mismatch: `pos(N) | N > 0` on `pos(0)` fails generally and
dispatch moves to the next equation.

Dispatch stops at the first failing test, so the argument named is the
first that blocked, not necessarily the only one that would have.

Outside a rule guard both kinds are hard errors; only the diagnosis
differs. Inside one, an instantiation failure is caught — next section.

### Soft guard failure

A **rule guard** — the conjunction between `|` and the body of a
simplification, propagation or simpagation rule — is evaluated with
instantiation failures caught. Such a failure makes the guard
**false**: the rule does not fire for that combination of constraints,
nothing is reported, and solving continues. When the missing variable
is bound later, constraint reactivation retries the occurrence with a
value in hand.

```prolog
:- chr_constraint c(int), mk(int), out(int), later(int).

m @ mk(_)    <=> c(E), later(E).   % c is stored while E is unbound
l @ later(E) <=> E = 1.
r @ c(N)     <=> N > 0 | out(N).   % N unbound at the first activation
```

`r` is tried while `N` is free: `>` raises an instantiation failure,
the guard is false, `c(E)` stays stored. `l` binds `E`, which
reactivates `c`; `r` is retried with `N = 1` and tells `out(1)`.

This holds for every rule guard. There is no opt-in or opt-out syntax.

#### The demand-driven principle

An instantiation failure is raised only when a computation demands the
value of an unbound variable, never from an unbound variable merely
being present in an argument list. A variable that is only carried
does not delay:

- a *pass-through* argument (`id(X) -> X.`);
- an *ignored* argument (`fst(pair(A, _)) -> A.` on `pair(1, U)`, `U`
  unbound);
- data construction (`quote(...)`, constructor application, `=`);
- primitives total on unbound values — `==`, `unifiable`, the type
  predicates (`var`, `nonvar`, `ground`, `integer`, `atom`, …),
  `term_variables`, `copy_term`.

A demand point is one of:

| Demand point | Example |
|---|---|
| Function-equation dispatch inspecting an unbound argument position | `length([1\|T])` with `T` unbound |
| `'$call'` on an unbound closure operand | `'$call'(F, 1)` with `F` unbound |
| A strict host primitive reaching its failure path with an unbound argument | `N > 0`, `X + 1`, `string_length(S)` |
| A host function whose marshalling reports `UnboundValue` | `host:f(X)` with `X` unbound |
| A rule guard that evaluates to an unbound variable | `c(B) <=> B \| body.` with `B` unbound |

The host primitives below are strict scalar operations with no ignored
arguments, so for them "an unbound argument on the failure path" means
"the value was demanded":

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

**Precedence.** Under-instantiated *and* ill-typed — `X + "foo"` with
`X` unbound — the instantiation diagnosis wins. In a rule guard the
rule delays; once `X` is bound, the type error is a hard general
failure.

**Unbound guard result.** A guard demands a boolean, so a guard whose
value is an unbound variable is an instantiation failure and delays:

```prolog
r @ c(B) <=> B | out(1).      % B unbound: delays; B bound to true: fires
```

A guard that evaluates to a *bound* non-boolean is a general failure
and stays a hard error ("guard did not evaluate to a boolean").

#### The catch boundary

The catch sits at exactly one point: the rule-guard residual of a rule
occurrence. It is not a general handler.

- **Not inside function bodies.** There, an instantiation failure from
  an equation guard or a nested call propagates out at once; later
  equations are not tried. Dispatch is monotonic: a definite mismatch
  moves to the next equation, a cannot-decide aborts the call. The
  failure reaches whatever demanded the function's value; if that was
  a rule guard, it is caught there.
- The boundary is the whole guard, so a failure deep inside a
  recursive call is caught like one at the top level:
  `r @ c(L) <=> length(L) > 0 | body.` on the partial list `[1|T]`
  delays even though `length`'s recursive dispatch raised it.
- `is` expressions, rule bodies and top-level goals are not guard
  positions. An instantiation failure there is a hard `YCHR-60001`.
- `run_chr_session/1` keeps its own boundary: it runs an isolated
  sub-session and reports *any* failure as `false`, rolling the
  sub-session back as it does.

A guard never tells. `=`, constraint additions and the other body forms
are not guard syntax, and a function called from a guard cannot tell
either, so abandoning a half-evaluated guard leaves the store, the
propagation history and the reactivation queue as it found them. That
is what makes the catch sound.

The one thing that outlives a guard is a host function that binds a
variable it was handed — `run_chr_session/1` does this as its result
channel. Those bindings persist, but equally when the guard
evaluates to false, so this is a property of effectful host calls in
guards, not of the delaying. If it matters, keep effectful host calls
in rule bodies, where they run once and only when the rule fires.

#### Interaction with reactivation and the propagation history

A retry is possible because:

- the propagation history is consulted *after* the guard, so a delayed
  guard leaves no history entry to block a later firing;
- the active constraint is killed only inside the fire block, so a
  delayed rule leaves it stored and observing its variables.

A stored constraint with occurrences to run observes every unbound
variable reachable from its arguments, including variables nested
inside compound terms; binding one pushes the constraint onto the
reactivation queue and its occurrences run again.

#### Non-guarantees

Soft guard failure delays a rule; it is not coroutining.

- **No retry without an observer.** Some *stored* constraint must
  observe the missing variable. A guard that delays on a variable
  reachable only from, say, a global or a value built inside the guard
  is never retried.
- **Passive occurrences are not retried.** Occurrences the compiler
  proved can never fire are not generated, and reactivation runs only
  generated ones.
- **No failure is reported.** A rule that delays for ever looks like a
  rule whose guard was false. A query with fewer bindings than
  expected: suspect an unbound variable at a guard.
- **A delayed rule is not fair.** The retry happens on the next
  activation, in ordinary ωr order; there is no wake-up queue or
  priority.

## Disjunction in rule bodies

`;` separates two alternative body conjunctions: infix, priority 1100,
`xfy`, looser than `,`:

```prolog
h(X) <=> p(X), (b(X) ; c(Y), d(X, Y)), q(X).
```

The module must import `library(search)` (`YCHR-20021`). `;` is a
rule-body form only: in a guard, an `is` right-hand side or a function
body it is `YCHR-20022`; at the top level of a query, `YCHR-30006`.
Semantics — choice points, lifting, shared variables, `quote/1` — are in
[search.md](search.md#disjunction-).

## The `=` operator

`=` is pure structural unification; neither operand evaluates. A
compound on either side is data, even when its head names a declared
function or host call. Every variable in either operand is a
unification slot; a name not yet in scope becomes a fresh logical
variable.

```prolog
test(R) <=> Y = 10, R = Y.                       % Y introduced by '='
test(R1, R2) <=> pair(X, Y) = pair(1, 2),        % X, Y introduced under ctor
                 R1 = X, R2 = Y.
test(R) <=> R = 1 + 1.                           % R bound to compound '+(1, 1)'
test(R) <=> R = double(YY).                      % R bound to compound 'double(YY)';
                                                 % YY allocated as a fresh var
```

Use [`is`](#the-is-operator) to evaluate. The same policy applies in
rule bodies and queries.

## The `is` operator

`is` accepts any expression on the RHS, including user-defined and
host function calls.

```ychr-repl
ychr> R is member(1, [0, 1, 2]).
R = true.
```

`is` and `=` sit at priority 750, `xfx` (Prolog: 700, shared with the
comparisons), so a comparison on the RHS needs no parentheses:

```ychr-repl
ychr> B is 1 < 2.
B = true.
```

The operator table is a built-in core (the directive keywords, `=`,
`is`, the rule operators, `requiring`, `refining`, …) plus the
prelude's `op/3` exports. `:list_operators` in the REPL prints it.

## Lambdas and function references

Lambdas are Erlang-style, delimited by `end`, so one fits inside a
compound argument without parentheses:

```prolog
:- function apply/2.
apply(F, X) -> call(F, X).

result(R) <=> R is apply(fun(X) -> X + 1 end, 5).
```

Parameters are variables and wildcards only; no pattern matching. Use
a named function with several equations for that. A lambda needs at
least one parameter; use `:- function` for a no-arg helper.

Lambdas are first-class: passed as arguments, returned, called via the
prelude's `call/N`. Free variables are captured *by value* when the
lambda expression is evaluated, then passed as hidden parameters to a
lifted top-level function:

```prolog
:- function make_adder/1.
make_adder(N) -> fun(X) -> X + N end.
```

`fun name/arity` (`fun member/2`) makes a named function a first-class
value the same way.

### `call` and `'$call'`

The prelude's typed `call/N` family is the everyday way to invoke a
lambda or function reference:

```prolog
R is call(fun(X) -> X + 1 end, 5).
R is call(fun double/1, 10).
```

`call` is a thin wrapper over the wired-in primitive
`'$call'(F, A1, ..., An)`, which the renamer recognizes directly. The
`'$'` prefix is not a naming convention and `$` is not reserved for
other primitives. Use `'$call'` only below the typed wrapper.

## Host calls

`host:` reaches into the host language:

```prolog
X + Y -> host:'+'(X, Y).
```

`host:` is a wired-in qualifier, not a module; the resolver dispatches
it to the host function the name denotes. Host calls are allowed in
every evaluating position: equation bodies, `is` right-hand sides,
guards, constraint arguments. Arguments are evaluated before the call;
the result flows back as an ordinary value. `host` is reserved and
cannot name a user module (`YCHR-16019`).

The prelude wraps every host arithmetic, comparison and string
operation it relies on, so most programs never write `host:`.

## Scheme backend portability

`print/1` and `name_base/1` work on both backends. Haskell-only:
`read_term_from_string/1`, `write_term_to_string/1`,
`write_store_to_list/0`, `print_store/0`, `run_chr_session/1`, and all
of `library(search)`. Details in `dev-docs/SCHEME_BACKEND_GAPS.md`.
