# YCHR Macro Specification

**Status: implemented.**

A *macro* is a named abbreviation for a conjunction of head
constraints or body goals. A use of the macro is replaced by its
definition at compile time, before names are resolved:

```prolog
:- macro in_degree(N, C) ---> count(edge(_, N), C).

node(N), in_degree(N, C) ==> indeg(N, C).
% is compiled as
node(N), count(edge(_, N), C) ==> indeg(N, C).
```

Macros are pure term rewriting. A macro cannot compute, inspect its
arguments, or emit rules or declarations. Their first purpose is to
give names to aggregate expressions (`count/2`, `sum/3`, …), whose
semantics belong to the compiler, not to the macro layer. They are the
counterpart of the `:- chr_expansion` directive in Sneyers et al.,
*Aggregates in CHR* (2007).


## Defining a macro

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


## Using a macro

A macro is recognized by name and arity in **goal positions** only:

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


## Expansion

Expanding the use `Name(A1, ..., An)` of the macro
`Name(V1, ..., Vn) ---> Body`:

1. Take a copy of `Body` in which every variable that is not a
   parameter is replaced by a fresh variable. Fresh variables cannot
   clash with any variable of the use site. Each `_` stays a distinct
   anonymous variable.
2. Replace each parameter `Vi` with the argument term `Ai`. The
   arguments are not expanded, evaluated or resolved first.
3. Flatten the resulting conjunction into the enclosing one, at the
   position of the use: kept head, removed head, or body.
4. Expand again any macro uses that the replacement put in goal
   positions.

Expansion is complete before renaming begins. The rest of the
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
(see [Diagnostics](#diagnostics)).

**Cycles.** If expanding a use of `M` requires, directly or
transitively, expanding another use of `M`, the expansion has no
finite form. It is rejected (`MacroCycle`) with the chain of macros
involved. The check follows actual expansions rather than a static
call graph, because names in a macro body are resolved at each use
site (see below).


## Names and modules

A macro is a module-level name, like a constraint or a function.

**Export and import.** `macro(Name/Arity)` in an export list exports
it. A module with no export list exports its macros along with
everything else. `:- use_module(M, [macro(Name/Arity)])` imports one
by name. A macro can be called qualified, as `M:Name(...)`, under the
usual rules: `M` must be imported and must export the macro.

**Collisions.** A macro may not share its name and arity with a
constraint or function declared in the same module
(`MacroNameCollision`). An unqualified use that matches a macro in
one visible module and a constraint or function in another is
ambiguous (YCHR-20001), as for any other name.

**Local use.** A macro is usable in the module that defines it. There
is no staging, because expansion runs no user code.

**Names in the body are resolved at the use site.** Expansion copies
terms, and renaming then resolves every name in the result as if the
user had written it, with the user module's imports. Two consequences
follow:

- A name that comes from an argument (`edge` in the `in_degree`
  example) means what the user meant by it.
- A name the macro body writes itself must be visible at the use site.
  A library macro should therefore refer to its own helpers by their
  *qualified* name, and must export them. The user of the macro must
  import the library without excluding those helpers.

```prolog
:- module(aggregates, [macro(count/2), count_spec/0]).
:- macro count(G, N) ---> aggregate(aggregates:count_spec, G, N).
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

Prelude names are always visible (prelude imports cannot be narrowed,
YCHR-20019), so a body that refers only to core forms, the prelude
and its own arguments resolves the same way at every use site.


## Diagnostics

Every diagnostic raised while *expanding* a macro, or while *renaming*
the code an expansion produced, carries the macro-expansion chain that
produced it, with the location of each use, innermost first:

```
/path/graph.chr:7:12: YCHR-20009
Module 'aggregates' does not export 'count_spec/0'
  Hint: check the spelling and the export list of 'aggregates'
  in the expansion of aggregates:count/2, used at /path/graph.chr:7:12
  in the expansion of graph:in_degree/2, used at /path/graph.chr:7:12
```

The chain covers expansion-time errors (the ones below) and renaming
errors and warnings (`YCHR-20001`–`YCHR-20022`, `YCHR-20101`,
`YCHR-20102`) reached while renaming expanded code. Resolve, Desugar,
and the optional type checker have no per-goal provenance to attach a
chain to, so a diagnostic from one of those phases about expanded code
carries no chain — it is anchored at the outermost use site, the same
location every pre-expansion diagnostic there would have used.

New errors:

| Name | Code | Condition |
|---|---|---|
| `MalformedMacroHead` | YCHR-15021 | Head is not an atom or a compound of distinct variables, naming neither a reserved symbol (`,`, `;`, `\`, `\|`, `->`, `=`, `is`, `true`, `quote`, `fun`, `$call`) nor a qualified name. |
| `DuplicateMacro` | YCHR-20023 | Two definitions of the same `Name/Arity` in one module. |
| `MacroNameCollision` | YCHR-20024 | A macro shares `Name/Arity` with a constraint or function of the same module. |
| `MacroOutsideGoalPosition` | YCHR-20025 | A macro name used outside a goal position (and outside `quote/1` and head/equation arguments). |
| `MacroCycle` | YCHR-20026 | A macro's expansion requires expanding itself. |
| `MacroBodyNotExported` | YCHR-20027 | A body names `M:x` in the macro's own module `M`, and `M` does not declare and export `x`. |
| `MacroInvalidInHead` | YCHR-20028 | A head expansion is not a conjunction of constraints (see [Validity](#expansion)). |

New warning: `UnusedMacroParameter` (YCHR-20105).


## Pipeline placement

Expansion is driven from the renamer itself, at each of its goal
positions (a rule head conjunct, a rule-body or disjunction-branch
goal, a query goal): the renamer's existing per-module visibility
tables already answer "is this name a macro, and if so which module's,"
so building a separate visibility environment for a standalone
pre-pass would only duplicate them. Observably this is the same as a
pre-pass that runs between Collect and Rename and then re-enters
Rename on its output: an expansion's replacement is renamed with the
visibility of the module whose code it replaced, nested macro uses are
expanded by the same mechanism before the renamer moves past them, and
the rest of the pipeline (resolving, desugaring, type checking,
compilation) sees only the expanded program. A backend never sees a
macro.

The single-goal entry points (`ychr run -g`, `gen-driver`,
`YCHR.Run.runProgramWithGoal`) parse a goal as exactly one
`Constraint` rather than a conjunction. A macro used there is expanded
the same way; if the expansion is exactly one goal it runs as any
other goal would, and if it expands to more than one goal (or to
none) the goal is rejected with a hint to use the REPL or the
multi-goal query API instead.


## Not in this version

- **Macros that compute**, such as a function over terms run at
  compile time. These would need staging, because they could only be
  used from importing modules, and a term representation for
  variables. They would reuse the `:- macro` name with a different
  form.
- **Patterns, guards and multiple clauses** in macro heads.
- **Guard and expression positions.** `:- inline` covers expression
  abbreviation.
- **Definition-site name resolution** (hygiene). It can be added
  compatibly, because a qualified name means the same under both
  schemes.
- **Aggregates.** The aggregate core form is specified separately.
  Its goal argument will be a goal position for this specification,
  so nested aggregates such as
  `argmax(S, (client(C), sum(B, account(_, C, _, B), S)))` expand.
