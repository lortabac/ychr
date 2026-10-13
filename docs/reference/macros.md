# YCHR Macro Specification

**Status:** goal macros (`:- macro`) are implemented. Declaration
macros (`:- macro_decls`) and the construction primitives (`'$compound'/2`,
`'$atom'/1`) are a **draft, not implemented**; the sections that
describe them say so.

YCHR has two kinds of macro. Both are pure term rewriting.

- A *goal macro* is a named abbreviation for a conjunction of head
  constraints or body goals. A use of it is replaced by its
  definition at compile time, before names are resolved:

  ```prolog
  :- macro in_degree(N, C) ---> count(edge(_, N), C).

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

A macro can't compute, can't inspect its arguments, and can't branch.
The only computation is the two
[construction primitives](#construction-primitives), which build a
compound or an atom from parts. They exist because Prolog syntax has
no way to write `F(X)` when `F` is a parameter. Since expansion runs no user code, a macro needs no staging and can be
used in the module that defines it.

Goal macros were first meant to give names to aggregate expressions
(`count/2`, `sum/3`, …), whose semantics belong to the compiler, not
to the macro layer. They are the counterpart of the `:- chr_expansion`
directive in Sneyers et al., *Aggregates in CHR* (2007).


## Goal macros

### Defining a goal macro

```prolog
:- macro Name(V1, ..., Vn) ---> Body.
```

- The head `Name(V1, ..., Vn)` is an atom or a compound whose
  arguments are **distinct variables**. `_` is not allowed as a
  parameter. There is exactly one definition per `Name/n`: no patterns,
  guards or alternatives.
- `Body` is an arbitrary term: a single goal or a `,`-conjunction.
  It is not checked when the macro is defined, beyond the rules under
  [Names and modules](#names-and-modules); whether its expansion is
  valid depends on where it is used.
- A parameter that does not occur in `Body` is a warning: the
  corresponding argument is dropped at every use site.

`--->` is the same operator `:- chr_type` uses (priority 1150, `xfx`),
so a conjunction on the right needs no parentheses.


### Using a goal macro

A goal macro is recognized by name and arity in **goal positions**
only:

- a conjunct of a rule head, kept or removed;
- a goal of a rule body, at any depth of `,` and `;`;
- a goal of a top-level query (`ychr run -g`, the REPL, `runProgramWithGoal`).

Elsewhere a macro name is an error (`MacroOutsideGoalPosition`): in a
guard, inside an argument in an expression position, or as a function
reference. The exceptions are `quote/1` and rule-head or
equation-pattern *arguments*: all three are opaque data, so
`count(a, b)` there is an ordinary compound.

Function equations have no goal positions, so macros do not apply
inside them.

*(Draft)* Only goal macros are looked up in goal positions; a
declaration macro is invisible there. A goal-position name that matches
no constraint, function or goal macro, but does match a visible
declaration macro, is `MacroKindMismatch`.


### Expanding a goal macro

Expanding the use `Name(A1, ..., An)` of the macro
`Name(V1, ..., Vn) ---> Body`:

1. Take a copy of `Body` in which every variable that is not a
   parameter is replaced by a fresh variable. Fresh variables cannot
   clash with any variable of the use site. Each `_` stays a distinct
   anonymous variable.
2. Replace each parameter `Vi` with the argument term `Ai`. The
   arguments are not expanded, evaluated or resolved first. Evaluate
   the [construction primitives](#construction-primitives) written in
   `Body` (draft).
3. Flatten the resulting conjunction into the enclosing one, at the
   position of the use: kept head, removed head, or body.
4. Expand again any macro uses that the replacement put in goal
   positions.

A use is expanded before the renamer resolves any name in it. The rest of the
pipeline (renaming, desugaring, type checking, compilation) sees only
the expanded program, and a backend never sees a macro.

**Call-by-name.** An argument is copied once per occurrence of its
parameter. In a body, an argument that is an evaluated expression is
therefore evaluated once per occurrence, as if the user had written it
that many times:

```prolog
:- macro twice(X) ---> (p(X), p(X)).

r <=> twice(f(1)).   % calls f(1) twice: r <=> p(f(1)), p(f(1)).
```

**Validity.** An expansion must be valid where it lands. A head
expansion that contains anything other than a conjunction of
constraints (for example a `;` or a `\`) is rejected, as are body
goals that are not allowed in a body. The diagnostic names the macro
(see [Diagnostics](#diagnostics)). Aggregates, once implemented, are
valid head conjuncts, and `?` guards are valid inside an aggregate
goal ([aggregates.md](aggregates.md)).

**Cycles.** If expanding a use of `M` requires, directly or
transitively, expanding another use of `M`, the expansion has no
finite form. It is rejected (`MacroCycle`) with the chain of macros
involved. The check follows actual expansions rather than a static
call graph, because names in a macro body are resolved at each use
site (see below).


## Declaration macros

**Status: draft, not implemented.**

### Defining a declaration macro

```prolog
:- macro_decls Name(V1, ..., Vn) ---> [Clause1, ..., Clausek].
```

`macro_decls` is a prefix operator at priority 1180, `fx`, like
`macro`.

- The head follows the same rules as a goal macro's head
  (`MalformedMacroHead`). In addition, it may not have the name and
  arity of a built-in directive, because its uses are directives (see
  [Using a declaration macro](#using-a-declaration-macro)). The
  reserved directives are `module/1,2`, `use_module/1,2`,
  `chr_constraint/1`, `chr_type/1`, `opaque_type/1`, `function/1`,
  `open_function/1`, `class/1`, `open_class/1`,
  `extend_function/1`, `extend_class/1`, `extend_class_type/1`,
  `inline/1`, `constraint_use/1`, `macro/1` and `macro_decls/1`.
  Other arities of those names are allowed.
- The body is written as a **list literal**: `[` … `]` with no tail
  variable (`MalformedMacroDeclsBody` otherwise). `[]` is allowed and
  expands to nothing. Each element is a clause of any kind a module
  may contain, such as a directive `(:- …)`, a rule or a function
  equation. List elements are read at priority 999, so each clause
  except the simplest needs parentheses. Elements are not checked
  when the macro is defined, beyond the rules under
  [Names and modules](#names-and-modules) and
  [Output restrictions](#output-restrictions). Whether an element is
  a valid clause is decided after expansion.
- A parameter that does not occur in the body is a warning
  (`UnusedMacroParameter`), as for goal macros.

The body is read with the defining module's operator table and the
arguments with the using module's. Expansion then works on terms, so
operators affect only how each side is read.


### Using a declaration macro

A use is a directive whose term is the macro applied to its arguments,
optionally qualified. A nullary macro is used as an atom:

```prolog
:- Name(A1, ..., An).
:- M:Name(A1, ..., An).
:- Name.          % n = 0
:- M:Name.
```

- A use may appear at the top level of any module, and as an element of
  another declaration macro's body list (a *nested use*), written as a
  directive there too: `(:- inner(X))`. A bare `inner(X)` element is
  an ordinary clause, not a use. A use can't
  appear in a goal, a query or a REPL input.
- Uses don't depend on file order: a module can use a declaration
  macro it defines further down.
- Only declaration macros are looked up in a directive; a goal macro
  is invisible there. A directive that matches no built-in directive
  and no visible declaration macro, but does match a visible goal
  macro, is `MacroKindMismatch`. Because lookup is filtered by kind, a
  goal macro `foo/1` from one module and a declaration macro `foo/1`
  from another are never ambiguous.
- A directive that matches no built-in directive and no visible macro
  is an error (`UnknownDirective`). **This changes existing behavior.**
  Today such directives are silently ignored. Once directives can
  name macros, ignoring them would make a misspelled or non-imported
  macro vanish without a diagnostic.


### Expanding a declaration macro

Expanding the use `:- Name(A1, ..., An).` of
`Name(V1, ..., Vn) ---> [C1, ..., Ck]`:

1. Take a copy of the body in which every variable that is not a
   parameter is replaced by a fresh variable, as for a goal macro.
2. Replace each parameter `Vi` with `Ai`, and evaluate the
   [construction primitives](#construction-primitives) written in the
   body.
3. Splice the resulting clauses into the using module **in place of
   the directive**, in list order.
4. Expand again any nested use among the spliced clauses. Cycles are
   rejected with `MacroCycle`, as for goal macros.

Each spliced clause is then an ordinary clause of the using module.
It is checked, renamed, resolved, type-checked and compiled as if the
user had written it at the directive's position. Goal macros inside a
generated rule are expanded there as usual.

**Position matters.** Generated rules take the directive's place in
the module's rule order, which ωr uses to number occurrences.
Contiguity rules apply to the module as spliced. For example, the
equations of a closed function must be contiguous, so a declaration
macro can generate a whole function. A user can't add equations to
it with clauses written around the use.

**Variables.** Each generated clause is its own variable scope, as in
source text. A use-site argument that contains a variable `X` and lands
in two clauses becomes two unrelated clause variables named `X`, one in
each. Freshening (step 1) guarantees that a body variable never
captures a variable of the arguments.

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
- macro definitions, `:- macro …` and `:- macro_decls …`.

The first group keeps the module structure fixed before expansion. A
module's imports, exports and operators come from its header (operators
are declared only as `op(…)` items of the export list), and
they decide which macros are visible and how its text is read. If an
expansion could change them, its result would depend on itself. The
second group keeps the set of macros fixed during expansion, so no
use's meaning depends on the order in which other uses were expanded.

The check runs on the expansion, so it catches a forbidden clause
built with `'$compound'`. A forbidden clause that is visible in the
body as written is also reported when the macro is defined.


## Construction primitives

**Status: draft, not implemented.**

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
  reserved for qualified-name mangling, as it is in source atoms.

An operand that breaks these rules is `MalformedMacroPrimitive`. The
diagnostic names the primitive, the operand and the term it received.

**Evaluation.** A primitive is evaluated where it is **written in a
macro body**, during the parameter substitution of one expansion
(step 2 of either expansion). Primitives are evaluated innermost
first, so `'$compound'('$atom'([get_, F]), [X])` works. Evaluation
goes everywhere in the body, `quote/1` included, because the body is
a template and not code. Argument terms are never searched for
primitives: a primitive that arrives through an argument is not
evaluated.

Any primitive left after expansion is `MacroPrimitiveOutsideMacro`.
That covers one written in ordinary code (`quote/1` and patterns
included), one passed in as a macro argument, and a declaration of a
constraint or function named `'$compound'/2` or `'$atom'/1`. The two
names are reserved.

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
:- macro apply1(C, X) ---> '$compound'(C, [X]).

r(X) <=> apply1(p, X).   % r(X) <=> p(X).
```


## Names and modules

A macro of either kind is a module-level name, like a constraint or a
function. Goal macros and declaration macros share one namespace: a
module may not define a goal macro and a declaration macro with the
same `Name/Arity` (`DuplicateMacro`).

**Export and import.** `macro(Name/Arity)` in an export list exports
the macro of either kind. A module with no export list exports its
macros along with everything else.
`:- use_module(M, [macro(Name/Arity)])` imports one by name. A macro
can be called qualified, as `M:Name(...)` or `:- M:Name(...).`, under
the usual rules: `M` must be imported and must export the macro.

**Collisions.** A goal macro may not share its name and arity with a
constraint or function declared in the same module
(`MacroNameCollision`). An unqualified use that matches a macro in
one visible module and a constraint or function in another is
ambiguous (YCHR-20001), as for any other name. A declaration macro is
used only in a directive, where no constraint or function can appear.
It may therefore share a name and arity with one. It may not share
them with a built-in directive (see
[Defining a declaration macro](#defining-a-declaration-macro)).

**Local use.** A macro is usable in the module that defines it. There
is no staging, because expansion runs no user code.

**Names in the body are resolved at the use site.** Expansion copies
terms. Renaming then resolves every name in the result, with the
using module's imports, as if the user had written it. That includes
the name of a nested declaration-macro use. Two consequences follow:

- A name that comes from an argument (`edge` in the `in_degree`
  example) means what the user meant by it.
- A name the macro body writes itself must be visible at the use site.
  A library macro should therefore refer to its own helpers, whether
  constraints, functions or macros, by their *qualified* name, and
  must export them. The user of the macro must import the library
  without excluding those helpers.

```prolog
:- module(aggregates, [macro(count/2), count_spec/0]).
:- macro count(G, N) ---> aggregate(aggregates:count_spec, 1, G, N).
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
*renaming* (and, draft, *converting*) the code an expansion produced, carries the
chain of macro expansions that produced it. Each entry gives the
location of the use, innermost first:

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
  `YCHR-20101`, `YCHR-20102`) reached while renaming expanded code;
- *(draft)* errors from checking that a clause spliced by a
  declaration macro is well-formed.

Resolve, Desugar and the optional type checker have no per-goal
provenance to attach a chain to. A diagnostic from one of those phases
about expanded code carries no chain. It is anchored at the outermost
use site: for a goal macro, the location every pre-expansion
diagnostic there would have used; for a declaration macro, the
outermost directive.

Errors:

| Name | Code | Condition |
|---|---|---|
| `MalformedMacroHead` | YCHR-15021 | Head is not an atom or a compound of distinct variables, naming neither a reserved symbol (`,`, `;`, `\`, `\|`, `->`, `=`, `is`, `true`, `quote`, `fun`, `$call`, and, draft, `$compound`, `$atom`) nor a qualified name. *(Draft)* For a declaration macro, also a head with the name and arity of a built-in directive. |
| `DuplicateMacro` | YCHR-20023 | Two definitions of the same `Name/Arity` in one module, of either kind. |
| `MacroNameCollision` | YCHR-20024 | A goal macro shares `Name/Arity` with a constraint or function of the same module. |
| `MacroOutsideGoalPosition` | YCHR-20025 | A goal macro name used outside a goal position (and outside `quote/1` and head/equation arguments). |
| `MacroCycle` | YCHR-20026 | A macro's expansion requires expanding itself. |
| `MacroBodyNotExported` | YCHR-20027 | A body names `M:x` in the macro's own module `M`, and `M` does not declare and export `x`. |
| `MacroInvalidInHead` | YCHR-20028 | A head expansion is not a conjunction of constraints (see [Validity](#expanding-a-goal-macro)). |

Draft errors (declaration macros and construction primitives). The
15xxx codes are raised only by declaration-macro expansion, which runs
before conversion to the AST (see
[Pipeline placement](#pipeline-placement)). The 20xxx codes can be
raised by either expansion, so they keep the renamer's range, as
`MacroCycle` does when a cycle runs through declaration macros.

| Name | Code | Condition |
|---|---|---|
| `MalformedMacroDeclsBody` | YCHR-15022 | A declaration macro's body is not a list literal with no tail variable. |
| `MacroDeclsForbiddenClause` | YCHR-15023 | An expansion contains a clause listed under [Output restrictions](#output-restrictions). |
| `UnknownDirective` | YCHR-15024 | A directive matches no built-in directive and no visible macro of either kind. |
| `MacroKindMismatch` | YCHR-20029 | A name matches only a macro of the other kind: a goal macro as a directive, or a declaration macro in a goal position. |
| `MalformedMacroPrimitive` | YCHR-20030 | An operand of `'$compound'` or `'$atom'` breaks the rules under [Construction primitives](#construction-primitives). |
| `MacroPrimitiveOutsideMacro` | YCHR-20031 | A primitive remains after expansion: it was not written in a macro body. |

Warning: `UnusedMacroParameter` (YCHR-20105), for either kind.


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

The single-goal entry points (`ychr run -g`, `gen-driver`,
`YCHR.Run.runProgramWithGoal`) parse a goal as exactly one
`Constraint` rather than a conjunction. A macro used there is expanded
the same way; if the expansion is exactly one goal it runs as any
other goal would, and if it expands to more than one goal (or to
none) the goal is rejected with a hint to use the REPL or the
multi-goal query API instead.

**Declaration macros** *(draft)* are expanded on the p-expr terms that
the term reader produces, before any clause of the using module is
converted to the AST. Three facts make this possible:

- Expansion can't add or remove a `use_module`. The import graph,
  library closure included, is therefore known from the module headers
  before anything is expanded.
- Operator tables are built from the same headers, so every module's
  text can be read up front.
- A module's set of macros is fixed (see
  [Output restrictions](#output-restrictions)).

The standard library is parsed once, ahead of any user program (at
build time under MicroHs), so its modules reach a program already
converted. A library module's own declaration-macro uses are expanded
when the library is parsed, and the definitions it exports are kept in
its parsed module, with their bodies as p-expr terms, for user modules
to expand.

Expansion therefore runs once per module, with that module's macro
visibility, over the terms of every user module. Conversion
to the AST, Collect and Rename then see only spliced clauses. Goal
macros inside them are expanded by the renamer as above.


## Not in this version

- **Macros that compute**, such as a function over terms run at
  compile time. These would need staging, because they could only be
  used from importing modules, and a term representation for
  variables.
- **Patterns, guards and multiple clauses** in macro heads. Without
  them a declaration macro can't iterate over a list argument: a use
  produces a fixed number of clauses, so `record(point, [x, y])` can't
  generate one accessor per field. Pattern clauses with recursion, or
  an ellipsis-style template, would be compatible extensions.
- **A body tail variable** (`[C1 | Rest]`) in a declaration macro,
  which would splice a user-supplied list of clauses.
- **Generating imports, exports, operators or macro definitions**
  (see [Output restrictions](#output-restrictions)).
- **Guard and expression positions.** `:- inline` covers expression
  abbreviation.
- **Definition-site name resolution** (hygiene). It can be added
  compatibly, because a qualified name means the same under both
  schemes.
- **Aggregates.** The aggregate core form is specified separately,
  in [aggregates.md](aggregates.md) (draft, not implemented).
  That specification makes its goal argument a goal position, so
  nested aggregates such as
  `argmax(S, (client(C), sum(B, account(_, C, _, B), S)))` expand.
