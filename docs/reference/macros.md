# YCHR Macro Specification

**Status:** implemented. Goal macros (`:- macro`) and declaration
macros (`:- macro_decls`) both work.

YCHR has two kinds of macro. Both are pure term rewriting.

- A *goal macro* is a named abbreviation for a list of head
  constraints or body goals. A use of it is replaced by its
  definition at compile time, before names are resolved:

  ```prolog
  :- macro in_degree(N, C) ---> [count(edge(_, N), C)].

  node(N), in_degree(N, C) ==> indeg(N, C).
  % is compiled as
  node(N), count(edge(_, N), C) ==> indeg(N, C).
  ```

- A *declaration macro* is a named abbreviation for a list of
  top-level clauses: declarations, rules and function equations. A
  use is a directive named after the macro:

  ```prolog
  :- macro_decls counter(Name) --->
      [ (:- chr_constraint Name/1, '$atom'([inc_, Name])/0),
        ('$compound'(Name, [N]), '$atom'([inc_, Name])
           <=> M is N + 1, '$compound'(Name, [M])) ].

  :- counter(clicks).
  % is compiled as
  :- chr_constraint clicks/1, inc_clicks/0.
  clicks(N), inc_clicks <=> M is N + 1, clicks(M).
  ```

A macro can do three things with its arguments:

- match them against head patterns, which chooses the clause that applies;
- copy them into the clause body;
- combine them with the two
  [construction primitives](#construction-primitives), which build a
  compound or an atom from parts. Prolog syntax has no way to write
  `F(X)` when `F` is a parameter, which is why they exist.

A clause body can use the macro again, so a macro can recurse over a
list or a tree. Expansion never runs user code, so a macro needs no
staging and can be used in the module that defines it.

Goal macros were first meant to give names to aggregate expressions
(`count/2`, `sum/3`, …), whose semantics belong to the compiler, not
to the macro layer. They are the counterpart of the `:- chr_expansion`
directive in Sneyers et al., *Aggregates in CHR* (2007).


## Defining a macro

A macro is defined by one or more *clauses*. A clause looks like a
function equation, with `--->` in place of `->`:

```prolog
Head ---> Body.
```

`--->` is the same operator `:- chr_type` uses (priority 1150, `xfx`).
`macro_decls` is a prefix operator at priority 1180, `fx`,
like `macro`.

### Single-clause form

```prolog
:- macro Name(V1, ..., Vn) ---> [Goal1, ..., Goalk].
:- macro_decls Name(V1, ..., Vn) ---> [Clause1, ..., Clausek].
```

A one-line definition declares the macro and gives its only clause.
Its head may use [patterns](#patterns), like any clause head. A use
that the pattern doesn't match is then an error, because there is no
other clause to try.

### Multi-clause form

```prolog
:- macro Name/N.              % or :- macro_decls Name/N.
Name(P1, ..., Pn) ---> Body1.
Name(Q1, ..., Qn) ---> Body2.
...
```

This has the same shape as a function definition: a declaration
(`:- macro Name/N` or `:- macro_decls Name/N`), then the clauses as
top-level clauses.

- Every clause must be in the module that declares the macro, after
  the declaration or before it, like equations. The clauses must form
  one contiguous block, as for a closed function
  (`DiscontiguousMacroClauses`), so the declaration can't sit between
  two of them. There are no open macros: another module can't add
  clauses.
- One declaration may declare several macros, as other declaration
  directives do: `:- macro all_of/1, any_of/1.`
- A clause whose `Name/N` is not declared as a macro in its module is
  `UndeclaredMacroClause`.
- A macro defined by the one-line form can't have further clauses
  (`DuplicateMacro`).

The declaration decides the kind of every clause, and so how the
elements of its body are read (see [Bodies](#bodies)).

A declaration with no clauses is allowed; every use of it is
`NoMatchingMacroClause`.

### Heads

- The head is an atom or a compound, named by an unqualified atom
  that is not a reserved symbol (`MalformedMacroHead`; the reserved
  symbols are listed under [Diagnostics](#diagnostics)).
- A declaration macro also may not have the name and arity of a
  built-in directive (`DeclMacroBuiltinDirective`), because its uses
  are directives (see
  [Using a declaration macro](#using-a-declaration-macro)). The
  reserved directives are `module/1,2`, `use_module/1,2`,
  `chr_constraint/1`, `chr_type/1`, `opaque_type/1`, `function/1`,
  `open_function/1`, `class/1`, `open_class/1`,
  `extend_function/1`, `extend_class/1`, `extend_class_type/1`,
  `inline/1`, `constraint_use/1`, `macro/1` and `macro_decls/1`.
  Other arities of those names are allowed.
- A goal macro also may not have the name and arity of one of the five
  aggregate forms — `aggregate/4`, `argmin/2`, `argmax/2`, `takemin/2`,
  `takemax/2` (it would always read as the aggregate form):
  `ReservedAggregateName`; see
  [aggregates.md](aggregates.md#reserved-names). A declaration macro
  is a directive, not a goal, so it is exempt, and other arities of
  these names are allowed.
- A head variable that occurs only once in its clause, in the head and
  not in the body, is a warning (`UnusedMacroParameter`): the
  corresponding argument is dropped. Write `_`, or a variable whose
  name starts with `_` (such as `_Unused`), to drop it silently.

### Bodies

The body of every clause, of either kind, is written as a **list
literal**: `[` … `]` with no tail variable (`MalformedMacroBody`
otherwise).

- The elements of a goal macro's body are goals; those of a
  declaration macro's body are clauses (see
  [Declaration macros](#declaration-macros)).
- `[]` is allowed and expands to nothing: no goals, or no clauses. It
  is the usual base case of a recursive macro.
- List elements are read at priority 999, so an element that contains
  an operator above 999 needs parentheses: a conjunction `(a, b)`, a
  disjunction `(a ; b)`, a directive `(:- …)`, a rule (named or not)
  or a function equation `(f(X) -> …)`.
- The body is not checked when the macro is defined, beyond the rules
  under [Names and modules](#names-and-modules) and, for declaration
  macros, [Output restrictions](#output-restrictions). Whether its
  expansion is valid depends on where it is used.

A list body gives both kinds one shape and gives a goal macro a way to
expand to **zero goals**, which a conjunction cannot express: `true`
is a goal, and it is not allowed in a rule head.

### Patterns

The arguments of a head are patterns, with the same syntax as the
arguments of a function equation's head: variables, `_`, atoms,
numbers, strings, lists (`[]`, `[H|T]`, `[A, B]`), compounds and
qualified names (`m:f`).

**Matching is syntactic and one-way.** It compares a pattern with the
argument *as the user wrote it*. Arguments are never expanded,
evaluated or resolved, so matching sees exactly the term at the use
site:

- A variable pattern matches any argument term, including a use-site
  variable, and binds to it. A variable repeated in one head matches
  only arguments that are *identical* terms: the same structure, the
  same atoms, the same variables. An argument that contains `_` is
  never identical to anything: matching sees each `_` as a distinct
  variable.
- `_` matches any argument and binds nothing.
- Any other pattern matches an argument with the same principal
  functor and arity, and with each argument matching recursively.
  An atom, number or string matches only the same constant.
  Lists are compounds, so they match structurally: the pattern
  `[A, B]` matches the argument `[a | [b]]`. A qualified pattern is
  matched part by part: `lib:F` matches `lib:x` and `lib:g(1)`,
  binding `F` to `x` and `g(1)`, and `M:F` matches any qualified
  argument.
- A use-site variable matches only a variable pattern or `_`. Matching
  never binds a use-site variable.

Two consequences:

- `f(1 + 1)` does not match a `2` pattern. `1 + 1` is the compound
  `+(1, 1)`, not a number.
- Names are compared as written, before name resolution. An argument
  `edge` does not match a pattern `graph:edge`, and the other way
  round.

**Clause selection.** A use is expanded with the first clause, top to
bottom, whose head matches. If no clause matches, the use is an error
(`NoMatchingMacroClause`). The diagnostic shows the use and the
expansion chain.

There are no guards. A function guard runs code, and running code at
expansion time would need staging. Distinguish cases with patterns
instead.

Example: a goal macro that turns a list of goals into a conjunction.

```prolog
:- macro all_of/1.
all_of([]) ---> [].
all_of([G|Gs]) ---> [G, all_of(Gs)].

r <=> all_of([p(1), q(2), s]).        % r <=> p(1), q(2), s.
all_of([a(X), b(X)]) ==> c(X).       % a(X), b(X) ==> c(X).
```

### Recursion and termination

A clause body may use the macro it belongs to, directly or through
other macros. Each expansion is a step. Two checks keep expansion
finite:

- **Repeated use.** Suppose a use is reached again while it is still
  being expanded, with the same macro and identical arguments up to
  renaming of variables. Then the expansion can never finish, and it
  is rejected with `MacroCycle` and the chain of macros involved.
  "The same macro" means the same resolved macro, however it is
  written: `lib:all_of(Gs)` and `all_of(Gs)` are the same if both
  resolve to `lib:all_of/1`. "Identical" compares terms, not their
  source locations.
- **Depth limit.** A chain of nested expansions deeper than 1000 is
  rejected with `MacroExpansionTooDeep`. The diagnostic shows the
  innermost uses of the chain. The chain is the nesting of expansions,
  the same chain [diagnostics](#diagnostics) report. A recursive macro
  therefore handles a list of at most about 1000 elements: `all_of`
  over a longer list hits the limit.
- **Size limit.** A use written in a rule, a query or a top-level
  directive may cause at most
  100000 expansions in total, nested ones included. More is rejected
  with `MacroExpansionTooLarge`. A clause that uses its macro twice
  doubles the work at every level, so the depth limit alone would let
  it run for `2^1000` steps.

The repeat check catches the common mistake, a recursive use with the
same arguments, with a precise message. The depth and size limits
catch everything else, such as an argument that grows at every step.
A single-clause macro that uses itself never finishes: one of the
checks stops it. After a depth or size error, or an expansion error
(such as `NoMatchingMacroClause`) in a nested use, the rest of that
use's expansion is abandoned, so the error is reported once.


## Goal macros

### Using a goal macro

A goal macro is recognized by name and arity in **goal positions**
only:

- a conjunct of a rule head, kept or removed;
- a goal of a rule body, at any depth of `,` and `;`;
- a goal of a top-level query (`ychr run -g`, the REPL, `runProgramWithGoal`).

Elsewhere a goal macro name is an error (`MacroOutsideGoalPosition`): in a
guard, inside an argument in an expression position, or as a function
reference. The exceptions are `quote/1` and rule-head or
equation-pattern *arguments*: all three are opaque data, so
`count(a, b)` there is an ordinary compound.

Function equations have no goal positions, so macros do not apply
inside them. A declaration macro's name outside a directive
is an ordinary name: in a guard or an argument it means whatever it
would mean if no macro existed.

Only goal macros are looked up in goal positions; a
declaration macro is invisible there. A goal-position name that matches
no constraint, function or goal macro, but does match a visible
declaration macro, is `MacroKindMismatch`.


### Expanding a goal macro

Expanding the use `Name(A1, ..., An)` of a goal macro:

1. Select the first clause whose head matches `Name(A1, ..., An)`
   (see [Patterns](#patterns)).
2. Take a copy of the clause body in which every variable not bound
   by the match is replaced by a fresh variable. Fresh variables
   cannot clash with any variable of the use site. Each `_` written in
   the body stays a distinct anonymous variable.
3. Replace each head variable with the argument term it was bound to,
   and evaluate the
   [construction primitives](#construction-primitives) written in the
   body. Every `_` in an argument becomes a fresh named variable,
   shared by every copy of that argument.
4. Splice the resulting goals into the enclosing conjunction, in list
   order, at the position of the use: kept head, removed head, or
   body. An element that is itself a conjunction is flattened into it.
   An empty list splices nothing (see [Zero goals](#zero-goals)).
5. Expand again any macro uses that the replacement put in goal
   positions.

A use is expanded before the renamer resolves any name in it. The rest
of the pipeline (renaming, desugaring, type checking, compilation)
sees only the expanded program, and a backend never sees a macro.

**Call-by-name.** An argument is copied once per occurrence of its
parameter. In a body, an argument that is an evaluated expression is
therefore evaluated once per occurrence, as if the user had written it
that many times:

```prolog
:- macro twice(X) ---> [p(X), p(X)].

r <=> twice(f(1)).   % calls f(1) twice: r <=> p(f(1)), p(f(1)).
```

A `_` argument is shared too: with
`:- macro both(X) ---> [k(X), j(X)].`, `both(_)` is `k(V), j(V)`, so
`count(both(_), N)` counts the pairs with equal arguments. Distinct
`_`s stay distinct: `both(f(_, _))` is `k(f(V1, V2)), j(f(V1, V2))`.

**Validity.** An expansion must be valid where it lands. A head
expansion that contains anything other than a conjunction of
constraints (for example a `;` or a `\`) is rejected, as are body
goals that are not allowed in a body. The diagnostic names the macro
(see [Diagnostics](#diagnostics)). Aggregates are valid head
conjuncts, and `?` guards are valid inside an aggregate goal
([aggregates.md](aggregates.md)). An aggregate goal is a goal position
too, so a macro use inside one expands there.

**Termination.** The checks under
[Recursion and termination](#recursion-and-termination) follow actual
expansions rather than a static call graph, because names in a macro
body are resolved at each use site (see below).

### Zero goals

A use that expands to no goals disappears from its conjunction:

- In a rule body, a disjunction branch or a query, a conjunction that
  loses all its goals means `true`. A query that expands to no goals
  succeeds with no bindings. The single-goal entry points still
  reject it (see [Pipeline placement](#pipeline-placement)).
- In a rule head, the kept and removed parts are each checked after
  expansion. A part that the rule's form requires but that expansion
  leaves empty is `MacroEmptyHead`. Examples: the head of a
  simplification or propagation rule, or either side of `\` in a
  simpagation rule. The rule is never silently turned into another
  kind of rule. A simpagation rule whose removed part vanished would
  otherwise become a propagation rule, which keeps a history and
  behaves differently.


## Declaration macros

### Clause elements

Each element of a declaration macro's [body](#bodies) is a clause of
any kind a module may contain: a directive `(:- …)`, a rule, a
function equation or a [nested use](#using-a-declaration-macro).
Whether an element is a valid clause is decided after expansion.

The body is read with the defining module's operator table and the
arguments with the using module's. Expansion then works on terms, so
operators affect only how each side is read.

Example: declare one constraint per name in a list, with a recursive
nested use.

```prolog
:- macro_decls unary_constraints/1.
unary_constraints([]) ---> [].
unary_constraints([C|Cs]) --->
    [ (:- chr_constraint C/1),
      (:- unary_constraints(Cs)) ].

:- unary_constraints([red, green, blue]).
% is compiled as
:- chr_constraint red/1.
:- chr_constraint green/1.
:- chr_constraint blue/1.
```


### Using a declaration macro

A use is a directive whose term is the macro applied to its arguments,
optionally qualified. A nullary macro is used as an atom:

```prolog
:- Name(A1, ..., An).
:- M:Name(A1, ..., An).
:- Name.          % n = 0
:- M:Name.
```

- A use may appear at the top level of any module. It may also appear
  as an element of a declaration macro's body list, where it is a
  *nested use*. A nested use is written as a directive too:
  `(:- inner(X))`. A bare `inner(X)` element is an ordinary clause, not
  a use.
- A use can't appear in a goal, a query or a REPL input.
- Uses don't depend on file order: a module can use a declaration
  macro it defines further down.
- Only declaration macros are looked up in a directive; a goal macro
  is invisible there. A directive that matches no built-in directive
  and no visible declaration macro, but does match a visible goal
  macro, is `MacroKindMismatch`. Because lookup is filtered by kind, a
  goal macro `foo/1` from one module and a declaration macro `foo/1`
  from another are never ambiguous.
- A directive that matches no built-in directive and no visible macro
  is an error (`UnknownDirective`), so a misspelled macro can't just
  vanish. Delete foreign Prolog
  directives like `:- dynamic` or `:- discontiguous`. A directive that
  isn't an atom or compound (a variable, number, string, or `M:foo`
  with a non-atom `M`) is `MalformedTopLevel` (YCHR-15014). A built-in
  directive with arguments of the wrong shape, like `:- module(42).`,
  is `MalformedDirective` (YCHR-15028).


### Expanding a declaration macro

Expanding the use `:- Name(A1, ..., An).`:

1. Select the first clause whose head matches `Name(A1, ..., An)`
   (see [Patterns](#patterns)).
2. Take a copy of its body in which every variable not bound by the
   match is replaced by a fresh variable, as for a goal macro.
3. Replace each head variable with the argument term it was bound to,
   and evaluate the
   [construction primitives](#construction-primitives) written in the
   body.
4. Splice the resulting clauses into the using module **in place of
   the directive**, in list order.
5. Expand again any nested use among the spliced clauses, subject to
   the checks under
   [Recursion and termination](#recursion-and-termination).

Each spliced clause is then an ordinary clause of the using module.
It is checked, renamed, resolved, type-checked and compiled as if the
user had written it at the directive's position. Goal macros inside a
generated rule are expanded there as usual.

**Position matters.** Generated rules take the directive's place in
the module's rule order, which ωr uses to number occurrences. A nested
use's clauses take the nested use's place, so the `unary_constraints`
example declares `red`, `green` and `blue` in list order. Contiguity
rules apply to the module as spliced. For example, the equations of a
closed function must be contiguous, so a declaration macro can
generate a whole function. A user can't add equations to it with
clauses written around the use.

**Variables.** Each generated clause is its own variable scope, as in
source text. A use-site argument that contains a variable `X` and lands
in two clauses becomes two unrelated clause variables named `X`, one in
each. Freshening (step 2) guarantees that a body variable never
captures a variable of the arguments. A freshened variable, such as `N`
or `M` in the `counter` example, appears in diagnostics under its fresh
name. A `_` in an argument works like a named variable (step 3):
`:- mk(_).` with `mk(X) ---> [(a(X), b(X) ==> c)]` gives
`a(_decl_0_1), b(_decl_0_1) ==> c.` In a type position it is a type
variable: `:- state(k, _).` means `:- state(k, T).`, which fails the
type checker ([state.md](state.md)).

**Generated names.** Generated declarations belong to the using
module. A generated `:- chr_constraint clicks/1` declares
`user_module:clicks/1`, not a name in the macro's module. Generated
names aren't exported automatically. A module with an export list must
list them like any other name. A module without one exports them along
with everything else.


### Output restrictions

An expansion may not contain any of the following clauses
(`MacroDeclsForbiddenClause`):

- `:- module(…)` and `:- use_module(…)`;
- macro definitions: `:- macro …`, `:- macro_decls …`, and macro
  clauses (`Head ---> Body`).

The first group keeps the module structure fixed before expansion. A
module's imports, exports and operators come from its header (operators
are declared only as `op(…)` items of the export list), and they decide
which macros are visible and how its text is read. If an expansion
could change them, its result would depend on itself. The second group
keeps the set of macros fixed during expansion, so no use's meaning
depends on the order in which other uses were expanded.

The check runs on the expansion, so it catches a forbidden clause
built with `'$compound'`. A forbidden clause that is visible in the
body as written is also reported when the macro is defined.


### Dumping the splices

Every command that compiles files (`run`, `compile`, `check`,
`gen-driver`, `repl`) takes `--dump-splices`: it prints the clauses the
declaration macros spliced, to stderr, and leaves stdout untouched. It
is a debugging aid for working out what a macro actually produced.

Each module that spliced something gets a `%` header, and a further
comment names the use a run of clauses came from — the outermost use,
so a nested use's clauses stay under it:

```prolog
% splices for counter.chr (module counter)
% counter:counter/1 at counter.chr:7:1
:- chr_constraint clicks / 1.
:- chr_constraint inc_clicks / 0.
clicks(N), inc_clicks <=> M is N + 1, clicks(M).
```

Clauses go through the same pretty-printer the diagnostics use, so an
operator like `/` comes out spaced (`clicks / 1`) even though the
source writes `clicks/1`.

Clauses the user wrote are not dumped, and neither is anything a goal
macro produced: goal macros expand later, in the renamer, and are out
of scope for the flag. A clause that a declaration macro spliced is
shown as spliced, so a goal macro it *uses* still reads as a name
(`a ==> g.`), not as its expansion. Only the files named on the command
line are dumped — a library's macros are expanded when the standard
library is parsed, before the CLI sees a program. A compile that fails
before it produces a program (parse, expansion, rename, resolve,
desugar) prints no dump, just the error; a later failure, like a type
error or a `--Werror` exit, happens after the dump. The flag is
explicit, so `--quiet` does not suppress it.


## Construction primitives

Two primitives build terms that Prolog syntax cannot write when parts
of them are parameters. They may be used in the body of either kind
of macro.

| Primitive | Result |
|---|---|
| `'$compound'(F, [A1, ..., An])` | The term `F(A1, ..., An)`; the atom `F` when `n = 0`. |
| `'$atom'([P1, ..., Pn])` | The atom whose text is the concatenation of the parts. |

**Operands.**

- `'$compound'`: `F` must be an atom, or a qualified name `M:f`, in
  which case the result is `M:f(A1, ..., An)`. The second operand must
  be a proper list. The arguments `Ai` may be any terms.
- `'$atom'`: the operand must be a proper, non-empty list. Each part
  must be an unqualified atom (`''` contributes nothing) or an integer,
  which contributes its decimal text, with a leading `-` if negative.
  The result must be non-empty and must not contain `__`, which is
  reserved for qualified-name mangling, or `%%u`, which is reserved
  for Unicode escapes, as in source atoms.

An operand that breaks these rules is `MalformedMacroPrimitive`. The
diagnostic names the primitive, the operand and the term it received.

**Evaluation.** A primitive is evaluated where it is **written in a
macro body**. Substitution and evaluation are one pass over the body
as written, the template. The pass replaces each head variable with
its argument term and never descends into that term. It evaluates
each primitive of the template once the primitive's own operands are
done, so primitives are evaluated innermost first and
`'$compound'('$atom'([get_, F]), [X])` works. The pass goes everywhere
in the template, `quote/1` included, because the template is not code.
A primitive that arrives through an argument is therefore never
evaluated.

A primitive is never evaluated in a macro clause's head, which is a
pattern. Patterns match the
arguments as written, so a primitive there is an error like any other
primitive left outside a body.

Any primitive left after expansion is `MacroPrimitiveOutsideMacro`.
That covers:

- one written in ordinary code, `quote/1` and patterns included;
- one written in a macro clause's head;
- one passed in as a macro argument;
- a declaration of a constraint or function named `'$compound'/2` or
  `'$atom'/1`. The two names are reserved.

The result of a primitive is an ordinary term. It is not checked when
it is built, only where it lands (a head, a goal, a declaration, …).
A macro use that the result puts in a goal position or a directive
expands like any other.

**Name resolution.** A name built by a primitive resolves at the use
site, like every other name in an expansion. `'$atom'([inc_, Name])`
with `Name = clicks` is the unqualified atom `inc_clicks`, as if the
user had written it.

Example: a goal macro that applies a constraint name to an argument.

```prolog
:- macro apply1(C, X) ---> ['$compound'(C, [X])].

r(X) <=> apply1(p, X).   % r(X) <=> p(X).
```


## Names and modules

A macro of either kind is a module-level name, like a constraint or a
function. Goal macros and declaration macros share one
namespace: a module may not define a goal macro and a declaration
macro with the same `Name/Arity` (`DuplicateMacro`).

**Export and import.** `macro(Name/Arity)` in an export list exports
the macro, with all its clauses, of either kind. A module with no
export list exports its macros along with everything else.
`:- use_module(M, [macro(Name/Arity)])` imports one by name. A macro
can be called qualified, as `M:Name(...)` or `:- M:Name(...).`, under
the usual rules: `M` must be imported and must export the macro.

**Collisions.** A goal macro may not share its name and arity with a
constraint or function declared in the same module
(`MacroNameCollision`). An unqualified use that matches a macro in
one visible module and a constraint or function in another is
ambiguous (YCHR-20001), as for any other name. A declaration
macro is used only in a directive, where no constraint or function can appear.
It may therefore share a name and arity with one. It may not share
them with a built-in directive (see [Heads](#heads)).

**Local use.** A macro is usable in the module that defines it. There
is no staging, because expansion runs no user code.

**Names in the body are resolved at the use site.** Expansion copies
terms. Renaming then resolves every name in the result, with the
using module's imports, as if the user had written it. That includes
the name of a nested declaration-macro use and of a recursive use.
Two consequences follow:

- A name that comes from an argument (`edge` in the `in_degree`
  example) means what the user meant by it.
- A name the macro body writes itself must be visible at the use site.
  A library macro should therefore refer to its own helpers by their
  *qualified* name, and must export them. That covers constraints,
  functions and macros, including the macro itself when it recurses.
  The user of the macro must import the library without excluding
  those helpers.

```prolog
:- module(aggregates, [macro(count/2), count_spec/0]).
:- macro count(G, N) ---> [aggregate(aggregates:count_spec, 1, G, N)].
```

A user who imports `library(aggregates)` in full can use `count/2`.
With `:- use_module(library(aggregates), [macro(count/2)])` the
expansion's reference to `aggregates:count_spec` fails
(YCHR-20009), and the diagnostic says that the reference came from
`count/2` and suggests widening the import list.

**Definition-time check.** A qualified name `M:x` in a macro body,
where `M` is the macro's own module, must name something `M` declares
and exports (`MacroBodyNotExported`). Without the check, every use of
the macro would fail. Unqualified names and names qualified with other
modules are only checked at use sites.

Prelude names, prelude macros included, are always visible. Prelude
imports cannot be narrowed (YCHR-20019), so a body that refers only to
core forms, the prelude and its own arguments resolves the same way at
every use site.


## Diagnostics

Every diagnostic raised while *expanding* a macro, or while
*renaming* or *converting* the code an expansion produced,
carries the chain of macro expansions that produced it. Each entry
gives the location of the use, innermost first:

```
/path/graph.chr:7:12: YCHR-20009
Module 'aggregates' does not export 'count_spec/0'
  Hint: check the spelling and the export list of 'aggregates'
  in the expansion of aggregates:count/2, used at /path/graph.chr:7:12
  in the expansion of graph:in_degree/2, used at /path/graph.chr:7:12
```

The chain covers:

- expansion-time errors (the ones below);
- renaming errors and warnings (`YCHR-20001`–`YCHR-20022`,
  `YCHR-20101`, `YCHR-20102`) reached while renaming expanded code: a
  goal-macro expansion, or a rule or equation a declaration macro
  generated (goal macros first, then declaration macros);
- errors in clauses a declaration macro generated (15xxx
  parse-validation errors, with that clause's chain).

Two kinds of error on generated code have no chain: module-wide checks
(contiguity of equations, declarations, macro clauses) and renaming
errors on a generated declaration (`:- chr_constraint`, `:- chr_type`,
…). Both point at the outermost use directive.

Every entry of a declaration-macro chain shows the outermost
directive's location. A nested use lives in a macro body, so it has no
location in the using module.

A recursive expansion can make the chain long. Consecutive entries for
the same macro are shown on one line, with a count and the innermost
use. At most ten such lines are shown, innermost first; one more line
counts the enclosing expansions left out:

```
  in 1000 nested expansions of m:grow/1, innermost used at /path/m.chr:5:10
  ... and 5 more enclosing expansions
```

Resolve, Desugar and the optional type checker have no per-goal
provenance to attach a chain to. A diagnostic from one of those phases
about expanded code carries no chain. It is anchored at the outermost
use site: for a goal macro, the location every pre-expansion
diagnostic there would have used; for a declaration macro, the
outermost directive.

Errors:

| Name | Code | Condition |
|---|---|---|
| `MalformedMacroHead` | YCHR-15021 | A head, or the name of a `:- macro Name/N` or `:- macro_decls Name/N` declaration, must be an atom or a compound named by an unqualified atom that is not a reserved symbol (`,`, `;`, `\`, `\|`, `->`, `=`, `is`, `true`, `quote`, `fun`, `$call`, `tell`, `$compound`, `$atom`). Head arguments may be any [patterns](#patterns). |
| `MalformedMacroBody` | YCHR-15022 | A clause body is not a list literal with no tail variable. |
| `UndeclaredMacroClause` | YCHR-15025 | A `Head ---> Body` clause whose `Name/N` is not declared as a macro in its module. |
| `DiscontiguousMacroClauses` | YCHR-15026 | A macro's clauses don't form one contiguous block. |
| `DuplicateMacro` | YCHR-20023 | Two definitions of the same `Name/Arity` in one module, of either kind, including further clauses for a macro defined by the one-line form. |
| `MacroNameCollision` | YCHR-20024 | A goal macro shares `Name/Arity` with a constraint or function of the same module. |
| `MacroOutsideGoalPosition` | YCHR-20025 | A goal macro name used outside a goal position (and outside `quote/1` and head/equation arguments). |
| `MacroCycle` | YCHR-20026 | A use is reached again while it is being expanded, with the same macro and identical arguments up to renaming of variables (see [Recursion and termination](#recursion-and-termination)). |
| `MacroBodyNotExported` | YCHR-20027 | A body names `M:x` in the macro's own module `M`, and `M` does not declare and export `x`. |
| `MacroInvalidInHead` | YCHR-20028 | A head expansion is not a conjunction of constraints (see [Validity](#expanding-a-goal-macro)). |
| `NoMatchingMacroClause` | YCHR-20032 | No clause of the macro matches the use (see [Patterns](#patterns)). |
| `MacroExpansionTooDeep` | YCHR-20033 | A chain of nested expansions exceeds the depth limit (see [Recursion and termination](#recursion-and-termination)). |
| `MacroEmptyHead` | YCHR-20034 | A part of a rule head that the rule's form requires is empty after expansion (see [Zero goals](#zero-goals)). |
| `MacroExpansionTooLarge` | YCHR-20038 | A use written in a rule, a query or a top-level directive causes more than 100000 expansions (see [Recursion and termination](#recursion-and-termination)). |
| `MalformedMacroPrimitive` | YCHR-20036 | An operand of `'$compound'` or `'$atom'` breaks the rules under [Construction primitives](#construction-primitives). |
| `MacroPrimitiveOutsideMacro` | YCHR-20037 | A primitive remains after expansion: it was not written in a macro body. |
| `ReservedAggregateName` | YCHR-20043 | A goal macro is declared at one of the five aggregate-form keys (see [Heads](#heads)). |

Declaration-macro errors. All 15xxx codes come before conversion:
`MacroDeclsForbiddenClause` and `UnknownDirective` from expansion (see
[Pipeline placement](#pipeline-placement)), `DeclMacroBuiltinDirective`
from parsing. 20xxx codes can come from either kind of expansion, so
they stay in the renamer's range, like `MacroCycle` and the other
expansion errors above.

| Name | Code | Condition |
|---|---|---|
| `MacroDeclsForbiddenClause` | YCHR-15023 | An expansion contains a clause listed under [Output restrictions](#output-restrictions); a forbidden clause visible in the body as written is also reported where the macro is defined, so it shows up there and at each use. |
| `UnknownDirective` | YCHR-15024 | A directive matches no built-in directive and no visible macro of either kind, including `:- M:Name(...)` where `M` is the module itself. |
| `MalformedDirective` | YCHR-15028 | A built-in directive with arguments of the wrong shape, e.g. `:- module(42).` |
| `DeclMacroBuiltinDirective` | YCHR-15027 | A declaration macro has the name and arity of a built-in directive (see [Heads](#heads)). The definition is dropped. |
| `MacroKindMismatch` | YCHR-20035 | A name matches only a macro of the other kind: a goal macro as a directive, or a declaration macro in a goal position. |

Warning: `UnusedMacroParameter` (YCHR-20105), for either kind: a head
variable that occurs only once in its clause, whose name does not
start with `_`.


## Pipeline placement

**Goal macros** are expanded by the renamer itself, at each of its goal
positions: a rule head conjunct, a rule-body or disjunction-branch
goal, a query goal. The renamer's per-module visibility tables
already answer "is this name a macro, and if so which module's", so a
standalone pre-pass would only duplicate them. Observably this is the
same as a pre-pass that runs between Collect and Rename and then
re-enters Rename on its output. An expansion's replacement is renamed
with the visibility of the module whose code it replaced. Nested macro
uses are expanded by the same mechanism before the renamer moves past
them. The rest of the pipeline (resolving, desugaring, type checking,
compilation) sees only the expanded program. A backend never sees a
macro.

Clause selection matches the argument terms before the
renamer touches them, so patterns see exactly what the user wrote, as
[Patterns](#patterns) requires.

The single-goal entry points (`ychr run -g`, `gen-driver`,
`YCHR.Run.runProgramWithGoal`) parse a goal as exactly one
`Constraint` rather than a conjunction. A macro used there is expanded
the same way; if the expansion is exactly one goal it runs as any
other goal would, and if it expands to more than one goal (or to
none) the goal is rejected with a hint to use the REPL or the
multi-goal query API instead.

**Declaration macros** are expanded on the p-expr terms that the term
reader produces, before any clause of the using module is converted to
the AST (`YCHR.Internal.DeclMacro`). Three facts make this possible:

- Expansion can't add or remove a `use_module`. The import graph,
  library closure included, is therefore known from the module headers
  before anything is expanded.
- Operator tables are built from the same headers, so every module's
  text can be read up front.
- A module's set of macros is fixed (see
  [Output restrictions](#output-restrictions)).

Each module is first scanned for its name, imports, exports and
macros (clauses may come before their declaration; the declaration
sets the kind). Then expansion runs once per module, with that module's
visibility. Generated clauses get the location of the outermost use
directive. Fresh variables are named `_decl_<n>_<Name>`, and an
argument's `_`s `_decl_<n>_1`, `_decl_<n>_2`, … (goal macros use
`_macro_` instead), so a goal macro inside a generated rule can't
capture them. Generated rules and equations remember the macro
chain, and renaming errors on them show it after any goal-macro chain.
Everything after conversion only sees the generated clauses; goal
macros in them are expanded by the renamer as usual.

The standard library is parsed once, before any user program (at build
time under MicroHs). `parseStdLib` reads all libraries with one merged
operator table and expands each library's uses with the macros it can
see through its imports (plus the prelude). Parsed libraries keep their
macros, so user modules can use the exported ones; that covers the
MicroHs-generated modules too. For a library, "the defining module's
operator table" under [Clause elements](#clause-elements) is that
merged table.

A program built with `YCHR.DSL` has no directives, so it can't use a
declaration macro.


## Not in this version

- **Term macros**: macros that expand to a term rather than to goals
  or clauses, usable inside other macro bodies. Without them a macro
  can iterate but can't compute a term to pass on. For example,
  `record(point, [x, y])` can generate one clause per field, but
  can't build the positional pattern `point(X, _)` that an accessor
  for `x` needs, because that requires list functions (map, append)
  at the term level. A term-macro kind can be added later, compatibly,
  and would still need no staging.
- **Guards** in macro clauses, and macros that call user functions at
  compile time. Both would run user code during expansion. That
  needs staging, because such a macro could only be used from
  importing modules, and it needs a term representation for
  variables.
- **Open macros**, extended with clauses from other modules.
- **A body tail variable** (`[E1 | Rest]`), which would splice a
  user-supplied list of goals or clauses. A recursive clause covers the
  same need: `all_of(Gs)` splices a user-supplied list of goals.
- **Generating imports, exports, operators or macro definitions**
  (see [Output restrictions](#output-restrictions)).
- **Guard and expression positions.** `:- inline` covers expression
  abbreviation.
- **Definition-site name resolution** (hygiene). It can be added
  compatibly, because a qualified name means the same under both
  schemes.
