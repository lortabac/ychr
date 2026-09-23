# CHR Compiler for Dynamically-Typed Procedural Languages

## Project Overview

This project implements a compiler for Constraint Handling Rules (CHR) that targets dynamically-typed procedural languages. The surface language is standard CHR with Prolog-compatible syntax. The compiler is implemented in Haskell and compiles CHR to an internal abstract VM. The abstract VM representation can then be compiled to JavaScript or Scheme, or interpreted directly in Haskell.

The compilation scheme follows Van Weert, Wuille, Schrijvers, and Demoen, "CHR for Imperative Host Languages" (K.U.Leuven), which describes a basic scheme based on the refined operational semantics (ωr) plus a catalogue of optimizations.


## Architecture

The system has three layers:

```
CHR source (Prolog-compatible syntax)
  │
  ▼
P-Expr Parser ──▶ Parser ──▶ Collect ──▶ Rename ──▶ Resolve ──▶ Desugar ──▶ TypeCheck (optional)
  │
  ▼
CHR-to-VM Compiler (Haskell)
  │
  ▼
Abstract VM Program
  │
  ┌──────────────┬──────────────┐
  ▼              ▼              ▼
  JavaScript     Scheme         Haskell
  backend        backend        interpreter
```

The `P-Expr Parser` is a generic, operator-table-driven Prolog term
parser (`YCHR.Internal.PExpr`); the `Parser` converts the flat p-expr terms it
produces into the surface AST. `Collect` resolves the library-import
closure and rewrites every import into a uniform `CollectedModule`
before renaming.

### Frontend

Parses standard CHR with Prolog-compatible syntax. Produces an internal representation of CHR handlers: constraint declarations, rule definitions (simplification, propagation, simpagation), with heads, guards, and bodies. Parsing is layered: a generic, operator-table-driven Prolog term parser (`YCHR.Internal.PExpr`) reads source text into flat, dot-terminated, source-annotated p-expr terms, and the CHR parser (`YCHR.Internal.Parser`) then converts each term into the surface AST. After parsing, the Collect phase (`YCHR.Internal.Collect`) resolves the transitive library-import closure and rewrites every import into a uniform `CollectedModule`, so everything downstream sees a single kind of import. The frontend pipeline then runs Rename → Resolve (module flattening + declaration-kind validation) → Desugar, with an optional static type-check stage on the desugared AST.

The Resolve phase, in addition to flattening modules, also commits to a structurally typed expression representation. The surface AST uses a uniform `Term` for everything a compound can be — a data constructor application, a user function call, a dynamic dispatch (`'$call'`), a function reference (`fun foo/2`), a lambda, or a host call. `Resolve.termToExpr` translates each `Term` in expression position into a typed `YCHR.Internal.Resolved.Expr` (`VarExpr`, `IntExpr`, `CtorExpr`, `CallExpr`, `ApplyExpr`, `FunRefExpr`, `LambdaExpr`, `HostExpr`, …). The translator consults the program's function-name set exactly once, at this boundary; the call-vs-constructor decision is then a structural property of the AST. Desugar, Compile, and TypeCheck all dispatch on `Expr` constructors without re-checking any function-name set. `Term` itself stays as the value type for the surface, the DSL, pretty-printing, the runtime/value bridge, and head/equation patterns (which match on data shapes, not values).

Tell-side constraint arguments — in rule bodies (`D.BodyTell`) and top-level goals — are *evaluated* expressions, like other expression positions in the language (function args, constructor args, `is` RHS). A compound argument whose head names a declared function becomes a `CallExpr` and runs at tell time; an unqualified bare expression like `1 + 1` evaluates via the prelude's `+` function. Users who want to pass a symbolic compound term opt out via the existing `quote(...)` quoting form (`quote(plus(2, 3))` keeps the inner tree opaque). An argument expression that mentions a logical variable that is still unbound at tell time runtime-errors — there is no auto-suspension or symbolic fallback.

Goal arguments are also *renamed* before they are evaluated, whether the goal came from surface text or was built by the host (`YCHR.Convert`, `YCHR.DSL`). `Run.prepareGoalTerm` runs `Rename.renameQueryArgsWith` over them in `NoResolve` mode — the same mode head-pattern arguments get — so a bare reference to a declared, exported data constructor is canonicalized to `Mod:name` and matches the compiled head patterns. `runProgramWithGoalDSL` is the choke point for the host-built path; `runGoalConstraint` is the variant for goals that have already been prepared. The renaming environment is built once per program and carried on `CompiledProgram.queryRenameEnv`.

`=` is the exception: it is *pure structural unification*, with neither operand evaluated. `X = 1 + 1` binds `X` to the symbolic compound `prelude:+(1, 1)`, not to `2`. Use `is` when you want arithmetic evaluation. The same policy applies in both rule bodies and queries (the compile path lowers `=`'s operands through `compileTerm . exprToTerm`, mirroring the query-side `exprToValue`).

### CHR-to-VM Compiler

Implemented in Haskell. Transforms CHR handlers into VM programs following the compilation scheme from the paper. This includes:

- Head Normal Form (HNF) transformation: all head arguments become distinct variables, implicit equalities become explicit guard conditions.
- Occurrence numbering: occurrences are numbered top-to-bottom, right-to-left as specified by ωr.
- Generation of procedures: `tell_c`, `activate_c`, `occurrence_c_j`, `reactivate_dispatch`.

Some optimizations are applied at this stage (see the Optimizations section).

### Backends

Each backend translates the abstract VM program to target language code. The generated code depends on a target-specific runtime library.

### Runtime Libraries

Each backend (JavaScript, Scheme, Haskell) ships a runtime that provides logical variables, compound terms, the constraint store, the propagation history, the reactivation queue, and recursion management (trampolining or explicit stacks where the host lacks TCO). Logical variables and compound terms are opaque to the VM: dedicated instructions (`NewVar`, `Unify`, `Equal`, `MakeTerm`, `MatchTerm`, `GetArg`) are implemented by the runtime using whatever representation is natural for the target language.


## Abstract VM Design

The VM is a small imperative language represented as a Haskell AST. It is the complete interface between the compiler and the runtime: the compiler never emits calls to runtime functions by name. The VM has three kinds of callable entities:

1. **VM instructions**: dedicated instructions for everything the runtime provides (constraint store operations, unification, term manipulation, etc.). Backends translate these to appropriate runtime calls.
2. **`CallExpr`**: calls to compiler-generated procedures (occurrence procedures, activate, tell, etc.).
3. **`HostCall`**: calls to host language functions (arithmetic, comparisons, user-written guard and body expressions).

### Program Structure

A VM program is a record bundling the list of named procedures with a little metadata: the number and source names of constraint types and rules (for store pre-allocation and runtime introspection), an *evaluables dispatch table* mapping a `(functor, arity)` key to the procedure name of the corresponding user-defined function (consulted by `EvalIs` when `is` walks a dereferenced compound term), a *callables dispatch table* mapping a closure's `(functor, identity field, declared arity)` key to the procedure name of the function or lifted lambda it designates (consulted by `ApplyClosure` at every dynamic call), and the list of *inert* constraint types — those whose `activate_c` runs no occurrence procedure, because the type has no occurrences at all or only passive ones. A runtime may skip registering an inert constraint as an observer of the variables in its arguments, since reactivating it could do nothing; honoring the list changes no result, so a backend may ignore it, and the Scheme backend does. Each procedure has a name, a parameter list, and a body consisting of a sequence of statements. The compiler generates the following kinds of procedures for each CHR handler:

- **`tell_c`**: Entry point for adding a constraint. Creates a suspension and calls `activate_c`. The suspension is *not* stored here: storage is postponed to the latest point that could observe the constraint (Late Storage, paper §5.3) — before a non-empty rule body that keeps the active constraint, or at the end of `activate_c` if it survives every occurrence. A constraint removed during its own activation is never stored at all.
- **`activate_c`**: Tries all occurrence procedures in order for a given constraint. Implements early drop (returns as soon as an occurrence signals the constraint was killed).
- **`occurrence_c_j`**: Handles the j-th occurrence of constraint c. Contains nested iterations over candidate partner constraints, guard checking, history checking, and rule firing (kill + body execution). Returns a boolean: `true` if the active constraint was dropped (early drop), `false` to continue with further occurrences.
- **`reactivate_dispatch`**: Dispatches reactivation by examining the constraint type of a suspension and calling the appropriate `activate_c`.

### Statements

| Statement | Description |
|-----------|-------------|
| `LetVal name valExpr` / `LetId name idExpr` | Bind a local variable to the result of a value or id expression. |
| `AssignVal name valExpr` / `AssignId name idExpr` | Mutate an existing value- or id-bound variable. |
| `If boolExpr thenStmts elseStmts` | Conditional execution. The condition is statically a `BoolExpr`. |
| `Foreach label cType suspVar conditions body` | Labeled loop over the constraint store. Iterates over all stored constraints of type `cType` satisfying the index conditions. Each condition `(argIndex, valExpr)` requires that the argument at `argIndex` is `BEqual` to `valExpr`. Binds the current suspension to `suspVar`. Index conditions use `BEqual` (ask) semantics. |
| `Continue label` / `Break label` | Resume the next iteration of, or exit, the named `Foreach`. Enables backjumping when a partner dies and early drop when the active constraint is killed. |
| `Return valExpr` | Return a value from the current procedure. |
| `ExprStmt valExpr` / `BoolExprStmt boolExpr` | Evaluate a value or boolean expression for its side effects, discarding the result. Used for procedure calls, host calls, and tell-side `BUnify` in statement position. |
| `Store idExpr` | Add a constraint suspension to the constraint store. Unless the constraint's type is inert (see Program Structure), this also registers the constraint as an observer of every unbound variable reachable from its arguments (recursing into compound terms) for reactivation. |
| `Kill idExpr` | Remove a constraint from the store, mark as not alive. |
| `AddHistory ruleName historyIds` | Record a rule firing in the propagation history. The operand is a `HistoryIds`: the matched constraint identifiers as a head-position-indexed tuple. Its constructor is private; `mkHistoryIds` takes position-tagged ids and establishes the order, so the same match keys to the same entry whichever occurrence is active. It is a tuple and not a set on purpose — for `leq(X,Y), leq(Y,Z) ==> leq(X,Z)` the matches `(c1,c2)` and `(c2,c1)` are distinct firings and both must happen. |
| `DrainReactivationQueue suspVar body` | Iterate over all constraints pending reactivation (populated by `BUnify`), binding each to `suspVar` and executing `body`. The body dispatches to the appropriate activate procedure. |
| `PushFrame frame` | Push a runtime call-stack frame (source location + pretty-printed source). Emitted at rule fires and function entries; used for stack traces. |

### Expressions

VM expressions are split by the kind of value they produce: `ValExpr`
produces an ordinary `Value`, `IdExpr` produces a constraint
identifier, and `BoolExpr` produces a boolean. The split is enforced
by the type system; `BFromVal` is the explicit bridge from `ValExpr`
to `BoolExpr` for user-written value expressions used in boolean
position.

#### Value expressions (`ValExpr`)

| Expression | Description |
|------------|-------------|
| `Var name` | Reference to a value-bound variable. |
| `Lit literal` | Literal value (see Literals below). |
| `CallExpr name [callArg]` | Call a compiler-generated procedure, return result. |
| `HostCall name [valExpr]` | Call a host language function. |
| `EvalDeep valExpr` | Evaluate in deep-deref mode (variable references are dereferenced and the mode propagates). |
| `EvalIs valExpr` | The `is`-with-variable-RHS marker: evaluate in deep-deref mode, then walk the resulting value and evaluate any compound subterm whose `(functor, arity)` names a declared evaluable. Emitted only for `R is X` where the RHS is syntactically a variable. |
| `ApplyClosure valExpr [valExpr]` | Apply a first-class callable — the whole of `'$call'(F, A1, …)`. The closure is dereferenced, turned into a `CallableKey`, and resolved through the program's *callables* table; the procedure it maps to is called with the closure's captures followed by the arguments. An unbound closure is an instantiation error; anything else, including a closure applied at an arity it was not declared at, is a general "no matching closure" error. |
| `NewVar` | Create a fresh unbound logical variable. |
| `MakeTerm functor [valExpr]` | Construct a compound term. |
| `GetArg valExpr index` | Extract an argument from a compound term by 0-based index. |
| `FieldArg idExpr argIndex` | Extract a constraint argument from a suspension by index. |
| `FieldType idExpr` | Extract the constraint type tag from a suspension. |

#### Constraint-id expressions (`IdExpr`)

| Expression | Description |
|------------|-------------|
| `IdVar name` | Reference to an id-bound variable. |
| `CreateConstraint cType [valExpr]` | Create a constraint suspension (not yet stored). Returns a constraint identifier. |

#### Boolean expressions (`BoolExpr`)

| Expression | Description |
|------------|-------------|
| `BLit Bool` | Boolean literal. |
| `BNot boolExpr` | Logical negation. |
| `BAnd boolExpr boolExpr` / `BOr boolExpr boolExpr` | Logical conjunction / disjunction (short-circuiting). |
| `BMatchTerm valExpr functor arity` | Check if a value is a compound term with the given functor and arity. |
| `BEqual valExpr valExpr` | Check structural equality (ask semantics). No mutation. Uses Prolog `==`: two distinct unbound variables are not equal. |
| `BIdEqual idExpr idExpr` | Compare two constraint identifiers for equality. |
| `BAlive idExpr` | Check if a constraint is still alive. |
| `BIsConstraintType idExpr cType` | Check if a suspension has the given constraint type. Used for dispatch in reactivation. |
| `BNotInHistory ruleName historyIds` | Check that a rule has not fired with this combination of constraint identifiers. Same `HistoryIds` operand as `AddHistory`. |
| `BUnify valExpr valExpr` | Unify two terms (tell semantics). Returns success. May mutate variables. Pushes affected constraints onto the reactivation queue. |
| `BFromVal valExpr` | Bridge a value-producing expression into boolean position; runtime-checks that the wrapped `ValExpr` evaluates to `VBool`. Used at the early-drop check and for user expressions in guards. |
| `BEvalDeep boolExpr` | Evaluate in deep-deref mode (mirrors `EvalDeep` for booleans). |
| `BSoftGuard boolExpr` | Evaluate with *instantiation* errors caught: an unbound variable reaching a demand point yields `false` instead of aborting. Emitted around rule-occurrence guard residuals only. |

#### Call arguments (`CallArg`)

| Expression | Description |
|------------|-------------|
| `AVal valExpr` / `AId idExpr` | Procedure-call argument tagged by kind. |

### Fields

A constraint suspension is referred to by its constraint identifier (an `IdExpr`, typically an `IdVar`). Its fields are read with the value expressions `FieldArg` and `FieldType`, both of which take the suspension's `IdExpr`:

| Expression | Description |
|------------|-------------|
| `FieldArg idExpr argIndex` | A constraint argument by 0-based index. |
| `FieldType idExpr` | The constraint type (for reactivation dispatch). |

The constraint identifier itself is not a field — it is the `IdExpr` value already in hand. Internal fields such as `alive`, `stored`, and `activated` are managed by the runtime and accessed only through dedicated VM constructs (`BAlive`, `Store`, etc.).

### Literals

- `IntLit Integer` — integer literal (arbitrary precision; carried as `Integer` end to end so programs cannot silently overflow)
- `FloatLit Double` — floating-point literal
- `AtomLit Text` — atom (symbolic constant)
- `TextLit Text` — string literal
- `BoolLit Bool` — boolean literal

There is no wildcard literal. Source `_` is an anonymous logical
variable outside a rule head or equation pattern, so it lowers to
`NewVar`; in a head or equation pattern HNF consumes it before
compilation and no VM operand is emitted at all.


## Key Design Decisions

### Unification Semantics

Two operations are provided:

- **`Unify` (tell)**: Prolog `=` semantics. Binds variables, returns success/failure as a boolean. As a side effect, pushes affected constraints onto the reactivation queue.
- **`Equal` (ask)**: Prolog `==` semantics. Identity/structural equality with no mutation. Two distinct unbound variables return `false`. Used in guards.

The distinction matters because guards must not leave half-done bindings if they fail. Guards use `Equal`, bodies use `Unify`.

### Reactivation Model

Reactivation follows this flow:

1. When a constraint of a non-inert type is stored (`Store`), the runtime registers it as an observer of every unbound variable reachable from its arguments. This recurses into compound terms, so a variable nested inside an argument (e.g. the `X` in `pair(X, 1)` or `[X, X]`) is observed too — otherwise binding it later would silently fail to reactivate the constraint. An *inert* type is one whose `activate_c` runs no occurrence procedure, so its reactivation could do nothing; the program header lists them (see Program Structure).
2. When `Unify` binds a variable, the runtime pushes the constraints observing that variable onto a reactivation queue, skipping any that are already dead. Nothing removes an id from an observer list, so without that filter a variable would keep enqueueing every constraint that ever observed it. The drain checks liveness again, since a constraint can die between being enqueued and being reached.
3. The compiler generates code using `DrainReactivationQueue` to iterate over the queue and dispatch each constraint to its `activate_c` procedure via `reactivate_dispatch`.

This is the *Selective Constraint Reactivation* optimization (paper §5.3). The blanket `reactivate_all` procedure used for the modification problem (paper §5.1–5.2) is intentionally not generated.

### Recursion Optimizations Belong to Backends

The VM uses plain procedure calls (`CallExpr`) and does not include trampoline or explicit stack instructions. Each backend is responsible for preventing call stack overflow using the technique most appropriate for its target:

- JavaScript: trampolining
- Scheme: tail call optimization (in compliant implementations) or trampolining
- Haskell interpreter: native support for deep recursion, or explicit strategy

### Constraint Store Implementation

Indexing is delegated entirely to the runtime. The VM's `Foreach` specifies a constraint type and a set of argument conditions, and the runtime is responsible for finding matching constraints. This keeps the compiler simple and avoids baking indexing strategies into the VM.

The initial implementation uses a simple data structure:

```
HashMap<ConstraintType, Array<Suspension>>
```

The complete constraint store is a hash map whose keys are constraint type names and whose values are arrays of suspensions. Each suspension contains:

- `type`: the constraint type name
- `id`: a unique constraint identifier
- `args`: an array of argument values
- `alive`: a boolean flag

`Foreach` linearly scans the array for the given type, skipping dead entries and checking the index conditions with `Equal` semantics. This is O(n) per lookup; smarter indexing (hash- or tree-based) can be added later as a runtime change without affecting the VM or compiler. See `src/YCHR/Internal/Runtime/Store.hs` for the exact layout and iterator semantics.


## Compilation Scheme

The compiler follows the scheme from the paper, generating VM code as follows.

### Head Normal Form

Each rule is first normalized. All head arguments become distinct variables, and implicit equalities are made explicit guards. For example:

```
leq(X, X) <=> true.
```

becomes:

```
leq(X, X1) <=> equal(X, X1) | true.
```

### Occurrence Numbering

Occurrences are numbered top-to-bottom, right-to-left as specified by ωr. Removed occurrences are tried before kept occurrences in the same rule.

### Generated Procedures

For each constraint, the compiler emits one `tell_c`, one `activate_c`, and one `occurrence_c_j` per occurrence. A single `reactivate_dispatch` is shared across the program.

### Occurrence Procedure Structure

Each occurrence procedure follows this pattern:

1. Iterate over candidate partner constraints using `Foreach` with index conditions.
2. Extract partner fields using `FieldArg` / `FieldType`.
3. Check constraint ID distinctness using `BNot (BIdEqual ...)`. A test is emitted only when the two operands' constraint types can coincide: a suspension identifier is never reused — the allocator's counter is monotone, backtracking does not rewind it, and search forks share it — so a test comparing constraints of different types is statically true and is elided by the compiler (see `wrapInPartnerLoops` in `YCHR.Internal.Compile`).
4. Check guards using `BEqual` (for implicit equality guards) and `HostCall` (for user-written guards).
5. Check propagation history using `BNotInHistory` (for propagation rules only).
6. Fire the rule: `AddHistory` (propagation rules), `Kill` removed constraints, execute body.
7. After body: check `BAlive` for active constraint (early drop) and partner constraints (backjumping).
8. Return `true` for early drop, `false` to continue to next occurrence.

### Body Execution

Rule bodies are compiled as sequences of statements:

- CHR constraint additions become `CallExpr "tell_c" [args]`.
- Built-in constraint tells (like `Unify`) become the corresponding VM instruction, followed by `DrainReactivationQueue` to process reactivations.
- Host language statements become `HostCall`.


## Optimizations

The paper describes numerous optimizations. Each should be considered individually for whether it belongs in the CHR-to-VM compiler or in the VM/backend. Here is a summary with notes on placement:

| Optimization | Description | Stage |
|-------------|-------------|-------|
| Loop-Invariant Code Motion | Schedule guard tests as early as possible to avoid trashing. | CHR-to-VM compiler |
| Indexing | Use hash/tree indexes for efficient partner lookup. | Runtime (via Foreach index conditions) |
| Join Ordering | Reorder partner lookups to maximize index usage. | CHR-to-VM compiler |
| Set Semantics | Replace iteration with single lookup when at most one match exists. | CHR-to-VM compiler (may need VM support) |
| Early Drop | Stop handling active constraint once killed. | CHR-to-VM compiler |
| Backjumping | Resume outer loop when partner dies. | CHR-to-VM compiler (via Continue) |
| Non-Robust Iterators | Use cheaper iterators when robustness not needed. | Runtime |
| Late Storage | Postpone storing until necessary. **Implemented**: `Store` is emitted before a non-empty kept-active rule body and at the end of `activate_c`; `Store` is idempotent in both runtimes. | CHR-to-VM compiler |
| Late Allocation | Postpone suspension creation until necessary. | CHR-to-VM compiler |
| Propagation History Maintenance | Garbage collect stale history entries. | Runtime |
| Propagation History Elimination | Remove history when not needed. | CHR-to-VM compiler |
| Guard Simplification | Remove redundant guard conjuncts. | CHR-to-VM compiler |
| Passive Occurrences | Skip occurrences that can never fire. | CHR-to-VM compiler |
| Selective Constraint Reactivation | Reactivate only affected constraints. | Runtime (observer pattern) |
| Delay Avoidance | Skip reactivation when modifications cannot affect guards. **Partly implemented**: the trivial instance, an *inert* constraint type (no occurrence procedure to run), is computed by the compiler and listed in the program header; the Haskell runtime registers no observers for one. | CHR-to-VM compiler |
| Memory Reuse | Reuse suspension memory for replaced constraints. | Runtime / Backend |
| Recursion Optimizations | Trampoline, explicit stack. | Backend |


### Haskell Interpreter Performance

The optimizations in the table above come from the paper and live at the
algorithmic level. The four items below come from profiling the Haskell
interpreter itself and are implementation-level. The first was
implemented, measured and discarded: what it removes does not show up in
the benchmarks, and it costs a second AST for the interpreter to
maintain. The other three are unimplemented. All four are recorded here,
with the evidence that motivates them and the measurements that settled
the first, so that whoever picks them up does not have to re-derive it.

The measurements are from the workload used to profile the interpreter
here — the CHR type checker running over its own sources:

```
ychr check typechecker/*.chr +RTS -p
```

On 2026-09-23 that run took 7.1 s and allocated 18.0 GB (profiler
figures). Parsing and CHR-to-VM compilation account for 4.3% of the
time and 4.5% of the allocation; 91.8% of the time and 89.8% of the
allocation are the interpreter running the compiled program. Under the
finer instrumentation described below, the same workload makes 2.74 M
procedure calls, 29.8 M value expression evaluations and 22.4 M
statement executions.

Two cautions about reading a profile of this build:

- The `ychr` package is instrumented with cost centres on exported
  bindings only, so the report charges the rest of the interpreter loop
  to `callProc` (73.0% individual time, 66.0% allocation) and never
  mentions `execStmts`, `evalValExpr` or `lookupProc` at all. (Exported
  hot-path helpers — `bindParams`, `matchTerm`, `getArg`, `deref`,
  `equal` — do keep their own cost centres, and the dependencies carry
  theirs.) Rebuilding the local package with
  `cabal build exe:ychr --ghc-options=-fprof-auto` (this rebuilds no
  dependencies) splits it up, and the per-function figures quoted below
  are from that run. The extra cost centres are not free — that run
  reports 11.3 s and 22.1 GB, because they also inhibit inlining — so
  use it for shares, not for absolute costs.
- A profiled build is not the shipping build. `+RTS -s` on the same
  binary reports 30.0 GB allocated where the profiler reports 18.0 GB,
  because the profiler excludes its own overhead. GC is 0.46 s of
  8.35 s (5.5%), with 679 MB copied, so this workload is
  allocation-bound in the mutator rather than GC-bound.

**1. Intern names, and key the hot maps by the interned id. — tried and discarded.**

`Name` is `newtype Name = Name {unName :: Text}`
(`src/YCHR/Internal/VM/Types.hs`) with a derived `Ord`, so every step of
a `Data.Map` lookup or insertion on a `Name`-keyed map is a `Text`
comparison. The fine profile puts 9.4% of individual time in
`$fOrdText_$ccompare` and 3.4% in `Ord Name`'s `compare` — 12.8% of the
run, from 92.9 M entries of the former — and attributes essentially all
of it to four callers: the `Var` case of `evalValExpr`, `lookupProc`,
`insertVal`, and `lookupHostCall`.

The obvious change — give `Name`, or a runtime-only key type, a compact
integer id assigned at compile time, and key every map by it — was
implemented and measured. It was built as its own stage rather than as a
field on `Name`: the compiler's IR keeps text names (that same value is
what the s-expression serializer writes and what the Scheme backend
reads, so the serialized form stays text-only), one total walk assigns
the ids in order of first appearance and interns the names into a program
type the interpreter alone reads, and the session's tables — the
procedure map, a call's local environment — are `IntMap`s over the
resulting ids. The source text rides along on every interned name, so
diagnostics, the call stack and trace events are unchanged. The invariant
is enforced rather than documented: an interned name can only come from
the interner, so a key that names nothing cannot be written down.

It did remove the comparisons. On the fine profile (both trees built with
`cabal build exe:ychr --ghc-options=-fprof-auto`, run over
`typechecker/*.chr`), `$fOrdText_$ccompare` falls from 9.7% of individual
time and `Ord Name`'s `compare` from 3.5% to neither appearing in the
report at all, the `Data.Map` rebalancing those lookups feed (`balanceL`
1.1%, `balanceR` 1.2%) goes with them, `insertVal` halves from 4.1% to
2.1%, and the run goes from 8.75 s to 7.87 s with allocation down from
18.04 GB to 17.30 GB.

It was discarded because that win does not survive to where the project
measures it. On `make bench`, interleaved rounds against a worktree at the
parent commit put every benchmark inside run-to-run noise:
`typecheck/pairs_library`, the benchmark this section names as the proxy,
moved by −0.9%, the micro-benchmarks by a few percent either way, against
a same-tree inter-round spread of 3–10%. So the ~10% the fine profile
shows over the checker's own sources — a workload where the interpreter
loop really is ~92% of the time — is not visible in the benchmark that
stands in for it, and two costs weighed against it:

- **A second AST.** The interpreter's program type mirrors the VM's
  constructors and fields. It fails loudly rather than silently (a new VM
  constructor or field makes the walk non-exhaustive, which is an error
  under `-Wall -Werror`), but it is a second place to edit and review for
  every VM change, and the stage moved `ProcMap`, `SessionInput`,
  `CompiledProgram` and `initSessionEnv` with it.
- **The scope shrank once measured.** Interned host-call dispatch was part
  of the attempt and had to be given back: interning the registry's ~50
  keys at every session init is a search of the whole program table per
  key — a fixed ~9 µs per session, which no long workload notices and
  every short one pays. In the same interleaved setup `guard` went
  12.5 µs → 21.4 µs, `leq` 7.2 µs → 15.3 µs and `sum_list_test`
  43.4 µs → 52.2 µs, while `fib`, `leq_closure` and the search benchmarks
  moved by under 2%. What is left after that is the compiler's own names,
  for the environment and the procedure map.

If it is ever picked up again, the two numbers to beat are the ones above,
and the cheaper shape to try first is a cached comparison key on `Name`
itself — an `Ord` that compares a text-derived integer and falls back to
the text on a tie — which needs no second AST and no API movement, at the
price of a small portable hash and an `Ord Name` whose order is no longer
text order.

**2. Slot-indexed locals instead of the name-keyed `Env`.**

`Env` is a pair of `Map Name _`
(`src/YCHR/Internal/Runtime/Interpreter.hs`), rebuilt on every procedure
call by `bindParams` (an arity check that walks both lists, a `zip`, and
a `foldl'`) and mutated by every `LetVal`/`AssignVal` through
`insertVal`. The fine profile puts `bindParams` at 4.1% time / 4.7%
allocation, `insertVal` at 3.8 / 3.3 over 11.8 M calls — about half of
them one-per-parameter from `bindParams`, the rest from statements —
`balanceL` plus `balanceR` at 1.5 / 4.8, and the `Map.lookup` inside
`evalValExpr`'s `Var` case (`evalValExpr.\`) at 3.5 / 2.6: about 13% of
the time and 15% of the allocation. The discarded item 1 would have taken
the `Text` comparisons out of two of those lookups; the arity check, the
`zip`, the rebalancing and the per-statement insert would all have stayed,
which is this item's point.

The compiler already knows each procedure's parameters and locals, so
it can emit slot indices in their place: `ValExpr`'s `Var`, `IdExpr`'s
`IdVar`, and the `Let*`/`Assign*` statements carry a slot, and a call's
environment becomes a fixed-size array built once per call — an
`IORef (SmallArray Value)` plus a second array, or one array of a tagged
union, for ids — with no search and no rebalancing. A flat array or
vector means adding a dependency (`primitive`, `vector` or `array`);
none of the three is in `build-depends` today. `Env` is already split by
kind and the IR guarantees a name is bound in only one of the two maps,
so slots can be numbered independently per kind.

If the VM shape should stay as it is, there is a cheaper intermediate: a
load-time pass that rewrites `Var`/`IdVar`/`Let*`/`Assign*` to `Int`
slots against a per-procedure `IntMap`-backed environment. Keeping the
names in the IR and consulting a `Name -> Int` table at each access
would not help: that lookup is the `Text` comparison the slot exists to
remove.

The awkward part is mutability. The interpreter threads `Env` through an
`IORef` so that bindings made before a `BSoftGuard` failure survive the
catch (`Note [Soft guard catch safety]`); a fixed-size array keeps that
property by being written in place. Slots must therefore also be
assigned for query-time procedures, which
`src/YCHR/Internal/Runtime/Session.hs` merges into `procMap` after the
program is loaded. Like item 3, the change reaches the IR, its
S-expression form, and the Scheme backend, which reads the same
statements.

**3. Resolve call targets at compile time.**

`CallExpr` and `HostCall` carry a `Name` that the runtime looks up on
every call: `lookupProc` (2.74 M calls per run — an `IORef` read plus a
`Map Name Procedure` search, 1.1% of time, and 0.8 points of `Ord Name`'s
`compare` before its share of the `Text` comparisons underneath) and
`lookupHostCall` (1.83 M calls, 0.4 points of `compare`). A `CallExpr`
target is known to the compiler, so the VM can carry a procedure index
and the runtime index a vector, keeping the name only for diagnostics
and the call stack. A `HostCall` target is not: the registry is a
runtime argument of `interpret` and callers hand in different ones
(`defaultHostCallRegistry`, the search driver's, a host-built
extension), so its index can only be assigned when the session is
initialised, against whatever registry it was given. The `EvaluableKey`
and `CallableKey` lookups behind `is` and `'$call'` are already one map
lookup each — that part is done — but those keys carry a `Name` into a
`Text`-keyed map: they are worth the index treatment this item describes,
and item 1's measurements say they are not worth interning. The
compatibility surface is the serialization format plus the Scheme backend
and driver, which
resolve by name today; and the index space has to stay open, because
query-time lambdas are added to the procedure map at run time.

**4. One traversal, not two, in the argument-access primitives.**

`getArg` (`src/YCHR/Internal/Runtime/Var.hs`), and `getConstraintArg`
and `suspArg` (`src/YCHR/Internal/Runtime/Store.hs`), each check
`idx >= 0 && idx < length args` and then apply `!!`: two traversals of a
list that is usually two or three elements long, for an index the
compiler fixed when it emitted the instruction. `matchTerm` walks the
same list to check `length args == arity`. The fine profile counts 4.7 M `$w!!`
applications, all of them in those three functions (`getArg` 3.29 M
calls, `suspArg` 1.11 M, `getConstraintArg` 335 K), and 40.7 M
`$wlenAcc` steps in total, of which about 23 M come from those three
plus `matchTerm` (3.64 M calls) and the rest from `bindParams`' arity
check (item 2). Together they are about 2.1% of the time, and none of
that work is necessary.

Two independent changes: index in one pass (walk the spine once, or
store a term's and a suspension's arguments in an `Array`/`Vector`,
which turns the arity check into a field read); and fuse `BMatchTerm`
with the `GetArg` that usually follows it in compiled output, so the
value is dereferenced once and the argument list walked once.
`deepEvalValue` and `applyClosure` take `length args` for the same
reason and can share the fix.

The relative sizes say what order to take these in. Item 1 is out — see
its entry above — which leaves item 2 as the way to stop looking local
variables up by text. It is also the better one: it removes the arity
check, the `zip` and the per-statement insert rather than only the
comparisons, so it stands for the whole ~15% spent maintaining the
environment. Item 3 applies the index treatment to the procedure and
host-call tables and to the keys behind `is` and `'$call'`; item 4 is
local and independent of the rest.

The same profile lists three smaller candidates that are not scheduled
here: the `try` wrapped around every host call (`invokeHostCall`,
1.83 M calls), `execForeach`'s `toList` of a store snapshot on every
loop entry, and the per-statement allocation in `execStmts`/`execStmt`
(11.4% and 6.4% of allocation).

Judge any of this with `make bench` and re-profile as described above.
The relevant benchmark is `typecheck/pairs_library`, which drives the
same CHR type checker over a different unit than the profile did, so
use it as a proxy; the numbers in this section come from a profiled
build over the checker's own sources and are indicative, not a
baseline.


## User-Defined Functions

The language supports user-defined functions: pattern-matching, top-to-bottom evaluated equations with optional guard clauses. Functions are declared with `:- function` directives and defined with Erlang-style equations using `->`:

```
:- function factorial/1.
factorial(0) -> 1.
factorial(N) | N > 0 -> N * factorial(N - 1).
```

Functions are callable in guards, `is` RHS expressions, and rule body position (discarding the result). They compile to ordinary VM procedures via `CallExpr` — no new VM instructions are needed.

Equation patterns are normalized using the same Head Normal Form (HNF) machinery as rule heads: non-variable patterns become fresh variables with explicit guard conditions. Equations are tried top-to-bottom; if no equation matches, a runtime error is raised.

Function names are qualified like constraint names and cannot collide with constraint declarations in the same module (rejected as YCHR-16016, `ConstraintFunctionCollision`).

A function name may not pun on a data-constructor name either, because the head of a compound is what decides between a call and a constructor application. Declaring both in one module is YCHR-16020 (`ConstructorFunctionCollision`, in `Resolve`): both spell as `mod:name`, so qualifying could not disambiguate. Across modules the two *are* distinguishable, so the declarations stand and only a bare reference is rejected, per use site, as YCHR-20020 (`ConstructorFunctionAmbiguity`, in `Rename`); `mod:name` keeps working. Arity is not part of either comparison — data constructors are name-only in the type system.

### Closed and Open Functions

Functions come in two flavors. A function declared with `:- function ...`
is *closed*: all of its declarations (typed or untyped) and all of its
equations must live in one module — the declaring module — and the
declarations must form a contiguous block of module items. A function
declared with `:- open_function ...` is *open*: the same constraints
apply to its primary declarations, but other modules may extend it
with equations via `:- extend_function name(P1, ..., Pn) [| Guards] -> Body.`.
`:- function` / `:- open_function` accept only a single signature
(multi-sig groups are rejected as YCHR-16011, `MultiSigOnFunction`),
and may carry a `requiring` clause for bounded polymorphism.

Multi-signature overloading uses the parallel pair `:- class` /
`:- open_class`. `:- open_class` is extended cross-module via
`:- extend_class_type (name(T1, ..., Tn) -> Tret).` (new signature)
and `:- extend_class name(P1, ..., Pn) [| Guards] -> Body.` (new
equation). `:- class` / `:- open_class` cannot carry `requiring`
(rejected as YCHR-15005, `RequiringOnClass`).

Both extension directives resolve their target through the importing
module's imports. Targeting a closed declaration is rejected
(YCHR-16005, `ExtendsClosedFunction`). Targeting the wrong kind is
also rejected: `:- extend_class_type` on `:- open_function`
(YCHR-16013), `:- extend_class` on `:- open_function`
(YCHR-16014), and `:- extend_function` on `:- open_class`
(YCHR-16015). Writing a free-floating equation
`name(args) -> body.` outside the declaring module is also rejected
(YCHR-16006); the importer must use `:- extend_function` /
`:- extend_class` instead.

### Lambdas and Function References

Anonymous functions use Erlang-style syntax: `fun(X, Y) -> Expr end`. The `end` keyword delimits the lambda body, allowing lambdas to appear inside compound-term arguments without parentheses. Lambdas are first-class values that can be passed as arguments, returned from functions, and called with `'$call'`:

```
:- function apply/2.
apply(F, X) -> '$call'(F, X).

result(R) <=> R is apply(fun(X) -> X + 1 end, 5).
```

Lambdas capture free variables from their enclosing scope (closures). A function returning a lambda retains the captured values:

```
:- function make_adder/1.
make_adder(N) -> fun(X) -> X + N end.
```

Named functions can be referenced by name and arity using `fun name/arity` syntax (e.g., `fun double/1`) and called with `'$call'`.

Internally, `fun(X, Y) -> Expr end` is syntactic sugar for the ordinary compound term `'->'(fun(X, Y), Expr)`. The `end` keyword is purely a parsing convenience and does not appear in the AST. During desugaring, lambdas are lifted to top-level functions named `__lambda_N`, with free variables passed as additional parameters. The lambda value becomes a closure: a compound term carrying the captured variable values, which `'$call'` unpacks at the call site.


## Already implemented

- Generic Prolog term ("p-expr") parser in `src/YCHR/Internal/PExpr.hs`.
- Frontend parser in `src/YCHR/Internal/Parser.hs` (converts p-expr terms to the surface AST).
- Surface AST types in `src/YCHR/Internal/Parsed.hs`.
- Library-import collector in `src/YCHR/Internal/Collect.hs` and `src/YCHR/Internal/Collected.hs`.
- Desugared AST types in `src/YCHR/Internal/Desugared.hs`.
- Renaming (qualifying constraint names) in `src/YCHR/Internal/Rename.hs`.
- Resolution (flattens modules into a single program, validates declaration kinds) in `src/YCHR/Internal/Resolve.hs` and `src/YCHR/Internal/Resolved.hs`.
- Desugaring in `src/YCHR/Internal/Desugar.hs`.
- A user-friendly DSL to construct a CHR program in Haskell in `src/YCHR/DSL.hs`. See [`docs/reference/dsl.md`](../docs/reference/dsl.md) for the user-facing reference.
- An ergonomic value-conversion interface in `src/YCHR/Convert.hs`: `ToTerm`/`FromTerm` classes bridging Haskell values and CHR `Term`s, result-decoding helpers, and a typed query wrapper (`runQuery`). Generics-free and portable; GHC-only `Generic` derivation lives in `src/ghc/YCHR/Convert/Generic.hs`. See [`docs/reference/convert.md`](../docs/reference/convert.md).
- An umbrella entry point in `src/YCHR.hs` (module `YCHR`) that re-exports the common compile-and-query surface (compilation, typed queries, and the `ToTerm`/`FromTerm` value bridge) as a single `import YCHR`. `YCHR.DSL` (program construction) and `YCHR.Convert.Generic` (GHC-only generic derivation) stay opt-in companion imports. The library's `exposed-modules` are grouped into a supported public API (`YCHR`, `YCHR.DSL`, `YCHR.Convert`, `YCHR.Run`, `YCHR.Types`, plus GHC-only `YCHR.Convert.Generic`) and internal modules exposed only for the in-package CLI, tests, and benchmarks.
- VM types in `src/YCHR/Internal/VM/Types.hs` (re-exported from `src/YCHR/Internal/VM.hs`).
- CHR-to-VM compiler in `src/YCHR/Internal/Compile.hs`.
- Compile-time embedding of `libraries/*.chr` and `typechecker/*.chr`, which lives *outside* the library in the shared `embed/` source directory (`YCHR.Embedded`, `YCHR.Embedded.StdLib`, `YCHR.Embedded.TypeCheck`). It is compiled into the components that want a self-contained binary — the `ychr` executable, the test suite, the benchmark and the `stlc` example — all of which therefore depend on `template-haskell`. The library instead takes the parsed standard library (`YCHR.Internal.StdLib.StdLib`, built by `parseStdLib`) and the compiled type-checker (`SessionInput`, built by `YCHR.Internal.TypeCheck.Compiled.compileTypeCheckerModules`) as explicit inputs, so it carries no Template Haskell dependency. The MicroHs build has no Template Haskell, so its `ychr` executable compiles `src/mhs/YCHR/Embedded.hs` instead: the same `loadResources` entry point, backed by the library's `YCHR.Internal.Resources`, which reads both directories from `$YCHR_LIB_DIR` (or the current directory) at run time. See [`docs/how-to/embed-a-chr-module.md`](../docs/how-to/embed-a-chr-module.md#5-supplying-the-resources) and `MICROHS_GAPS.md`, gap 5.
- Optional static type checker. The checker *is* a CHR program, under `typechecker/`. Its whole Haskell side is `src/YCHR/Internal/TypeCheck.hs` — the entry points `typeCheckProgram` / `typeCheckGoals` and the diagnostic decoder — plus `src/YCHR/Internal/TypeCheck/{Encode,Render,Error,Compiled}.hs`: `Encode` turns a desugared program into one ground term, `Render` formats solved types back into source syntax, and `Compiled` compiles the checker's sources once on first demand. Declaration collection, slot skeletons, the walkers, overload resolution and warning suppression all happen in CHR. Programs without type annotations are accepted unchanged. It reports errors and warnings; `--Werror` promotes the latter, and the CLI's `--no-check` skips the checker outright (whole-program and per-goal). See [`docs/reference/type-system.md`](../docs/reference/type-system.md).
- The CHR side is: `ast.chr` (the encoded AST's declarations — a matched pair with `Encode.hs`, and its header records how a mismatch between the two is caught), `diag.chr` (the diagnostic vocabulary — `error/3` and `warning/3` are declared over `error_code`/`warning_code` and `error_detail` rather than `any`, so `ychr check --Werror` on the checker's own source rejects a report site that invents a code; the code↔detail pairing is not statically checked and is enforced instead by `decodeError` — plus the accumulators and per-unit warning suppression, keyed on a `unit_id` that spells "outside any checking unit" as `no_unit` instead of a sentinel integer), `env.chr` (the declaration environment), `pure.chr` (the checks that need no solver — duplicate constructors, type-definition validation, constructor arity), `solver.chr` (the solver core: the type representation, the meet table, overload resolution, bound discharge and the guard-derived-evidence rules, every diagnostic carrying a structured `ctx`), `skel.chr` (slot skeletons and variable collection), `walk.chr` (the declaration facts, the rule walk, the function-equation walk, the class-function overload search — one `solve/1` per equation over a `;` chain of attempts, where an attempt that does not fit its candidate signature ends in `fail/0` and the search driver undoes everything it did — and the goal walk), and `main.chr` (the two entry points). Every module — `env.chr`, `pure.chr`, `skel.chr`, `walk.chr` and `solver.chr` — expresses its list traversals with `library(lists)` / `library(pairs)` higher-order functions (`maplist`, `concat_map`, `foldl`, `filter`, `all`, `any`, `all2`, `same_length`, `assoc_get`, `assoc_put_with`, …) instead of hand-rolled recursion, and the solver's trial substitution and per-bound candidate sets are plain association lists rather than bespoke pair types. That is a deliberate readability-over-speed choice, taken with the cost measured, in two steps. The first four modules were worth about +80% of the checker's runtime over the golden corpus (13.4 s → 24.4 s for the corpus's programs plus their rule bodies as goal lists), spread over about 55 call sites at roughly 2–3x per list element. `solver.chr` came last — it had been left as a rule-for-rule mirror of the Haskell solver it replaced so the two could be read side by side while that port was in progress, and was converted once that reason lapsed — for +8% of `cabal bench`'s `typecheck/pairs_library` (180.6 ms → 195.3 ms, measured 2026-09-03). The two figures are over different workloads and do not sum. Neither step has a hot spot to reclaim: the cost is closure dispatch through `'$call'`, not wrapper overhead. That diagnosis held up — keyed `'$call'` dispatch (see "Already implemented") has since removed the per-call dispatch chain and taken a further 13% off this benchmark. The declaration facts a session needs are built as data before being told, so the overload search can hand a whole declaration environment to each attempt (`retell_decls`, which `copy_term`s it first so no variable is shared across the boundary — the attempt that fits is committed, so the trail does not undo its bindings) instead of re-deriving it from the AST on every attempt. Checking one golden program cost ~47 ms on average and checking a query's goals ~13 ms when last measured over the whole corpus (2026-09-02, before the conformance walk was removed); nearly all of the goal figure is per-program work the query repeats (encode, `build_tc_env`, `tell_decls`), and caching that across queries is left to a general mechanism rather than a per-caller one. `cabal bench`'s `typecheck/pairs_library` is the standing single-program measurement.
- Pattern-match exhaustiveness checking for functions over algebraic types in `src/YCHR/Internal/Exhaustiveness.hs` (Maranget's usefulness algorithm), reported as a warning with a concrete unmatched example.
- Opt-in search for the Haskell runtime: `libraries/search.chr` plus
  `src/YCHR/Internal/Runtime/{Search,Trail}.hs`. `alt/1` is an ordinary
  CHR constraint with no rules, so it sits inert in the store; the
  driver forks a session, runs the goal to quiescence, takes the oldest
  live `search:alt` suspension, and tells each of its alternative goals
  in turn. The continuation after a choice is always "tell this goal
  and propagate to quiescence", which the driver invokes itself, so
  nothing has to be captured and neither the VM nor the `Chr` monad
  changes.
  Because an alternative is a *goal*, `choose/2` is not primitive: it
  is one library rule, `choose(X, Alts) <=> alt(maplist(fun(A) ->
  quote(try_unify(X, A)) end, Alts))`. The surface disjunction operator
  `;` is the other way in, lowered by
  `src/YCHR/Internal/Desugar/Disjunction.hs` — a pass shaped like
  lambda lifting, run after it and after the type checker has seen each
  branch in the rule it was written in, which lifts every disjunct into
  its own arity-only constraint and rewrites the node into an `alt`
  tell.
  What deriving `choose` costs is measured by the standing A/B pair
  `test/golden/search_label` (216 labeling branches through `choose`)
  and `test/golden/search_label_alt` (the same search with the `alt`
  written out): 2.13 ms against 2.00 ms, and 2.12 ms against 1.97 ms,
  in two `cabal bench` rounds on 2026-09-05 — about 7–8%, or ~0.65 µs
  per choice point for the rule firing, the `maplist` with a closure
  call per value, and the extra tell. `test/golden/search_generate`
  (36.0 ms then, 32.8 ms since the search-driver fix below) is the `;`
  path on its own, a recursive generator walked to depth 150. Recognizing `choose` in the driver as a fast path is the
  optimization those numbers exist to judge; it is not done.
  Solutions are fetched by three host calls over one driver. The
  driver's per-solution callback answers `continue` / `stop` /
  `commit`, and only `commit` skips the unwind to the base mark taken
  when the search was entered; `solve/1` and `find_all/2` are the
  constant functions `commit` and `continue`, and `fold_solutions/4`
  runs the user's step function to decide. `forall/3` and `find_n/3`
  are derived over `fold_solutions` in CHR rather than added to the
  driver, which used to cost one `call_2` dispatch branch each for every
  program that imports the library (keyed `'$call'` dispatch, see
  "Already implemented", has since removed the per-arity chain) and
  still costs one `length/1` per solution in `find_n`, over a list
  bounded by the N the caller asked for. Both costs are paid only by a
  program that imports the library. Measured 2026-09-07 by interleaving
  three `cabal bench` rounds against a clean worktree at the parent
  commit: the three search benchmarks (`search_label`,
  `search_label_alt`, `search_generate`) do not move outside their
  run-to-run spread, and `typecheck/pairs_library` is 227.3 ms against
  223.3 ms, +1.8%, slower in 3 of 3 rounds with each side's own spread
  under 0.4%. That last one is *unexplained* and was not the dispatch
  branches: at the time of that measurement the type checker did not
  import `library(search)`, and a compiled `typechecker/*.chr`
  contained no reference to it. (It does import it now — the overload
  search is written over `solve/1` — so the reading is pinned to the
  tree as it stood then.) It is
  within this benchmark's documented run-to-run range, and smaller than
  the 3.4% of drift between the 230.8 ms recorded for it on 2026-09-04
  and the 223.3 ms recorded for the same code here.
  The accumulator lives in an `IORef` the driver owns, so backtracking
  does not roll it back — and, deliberately, does not copy it either.
  A step function can return a value *pointing at* a variable the
  branch bound, which reverts when the branch is undone; copying would
  cost `O(|acc|)` per solution, quadratic for a
  list-building fold, and leave `fold_solutions` slower than
  `find_all/2` at `find_all`'s own job. So the witness is copied, the
  accumulator is not, and the contract is documented and pinned by the
  golden pair `test/golden/search_fold/{copied,aliased}`.
  Undo is a
  snapshot of the four store references (persistent structures behind
  one `IORef` each, so undo is a pointer write) plus a trail for the
  cells a snapshot cannot reach — variable cells and the
  `alive` / `stored` suspension flags, hooked at `writeVarState` and
  the `Store` flag writes. One trail is shared down through nested
  forks with a mark per choice point, so a nested search that commits
  still leaves its writes undoable by the enclosing one; the counters
  stay monotonic across backtracking. `SessionEnv.trail` is `Nothing`
  outside a search, so an ordinary program pays a field read and a
  branch per variable and flag write, and records nothing.
  That is not free. Measured 2026-09-04 by interleaving `cabal bench`
  rounds against a clean worktree at the parent commit: the
  micro-benchmarks (`leq`, `fib`, `sum_list_test`, `graph_test`,
  `lambda_test`, `guard`) move by 0–3%, at or below this machine's
  run-to-run noise, while `typecheck/pairs_library` is consistently
  slower — 6 of 6 interleaved pairs, median 245.6 ms against 230.8 ms,
  about +6%. Two things were ruled out: removing `search.chr` from the
  embedded stdlib does not recover it (so it is not the extra
  declarations or the longer `call_N` dispatch chains), and an
  in-branch A/B that deletes only the two hook calls accounts for most
  of it (+3.5% on the same benchmark). The type checker is a
  unification solver, so it reaches `writeVarState` far more often per
  unit of work than the CHR micro-benchmarks do; that is where the cost
  lands. The hook cannot simply skip `deref`'s path-compression writes,
  which are the bulk of them: a cell compressed to point past a
  variable the branch bound has to be restored alongside it.
  That figure is the cost of the hook to a program with no search
  *active*. The checker now runs one, so its overload attempts record
  on the trail for real. What that costs has not been isolated. The
  A/B available is the whole migration against the mechanism it
  replaced: measured 2026-09-08 the same way, over three interleaved
  rounds, `typecheck/pairs_library` is 202.5 ms against a 201.9 ms
  baseline, +0.3% at the median and slower in 1 of 3 rounds, with each
  side's own spread over its three rounds at 5–6%. That delta bundles
  at least three effects with different signs — trail recording during
  attempts, the longer `call_N` dispatch chain from `walk.chr` now
  importing `library(search)`, and one fork per equation in place of
  one per attempt — so it says the migration is free at this
  benchmark's resolution, and says nothing about any of the three on
  its own. Isolating the trail needs a third arm that adds only the
  `use_module`. The three search benchmarks, which do not run the
  checker, do not move outside the same spread. Do not read the
  201.9 ms baseline against the 223.3 ms recorded the day before: it
  is the same benchmark on the same machine and the gap is drift.
  The driver used to be quadratic in the depth of a search path, for
  two reasons that were both runtime representation costs rather than
  anything in the spec. A killed constraint stays on the observer
  lists of every variable its arguments reach, so a path of depth `k`
  left `k` dead choice points observing the search variable and
  binding it enqueued all of them; and dead choice points stay in the
  store sequence, so `findChoice` rescanned the whole consumed prefix
  at every quiescence. Three changes fix it: `enqueueObservers` drops
  ids whose suspension is dead, `search:alt` is an *inert* constraint
  type and so registers no observers at all (see the Delay Avoidance
  row and Program Structure), and `findChoice` scans from a per-branch
  cursor — the index of the choice the branch was entered on, plus
  one, which is sound because a flag only goes back to alive by trail
  undo and an undo restores a state whose cursor was already at most
  that index. Measured on `test/golden/search_deep` (an
  O(1)-per-solution generator under `forall` to a bound, so every
  solution adds one choice point to the path), wall clock less the
  ~0.5 s of compilation, on 2026-09-07: at a bound of 10000, 15.0 s
  before, 0.83 s with the two observer changes, 0.19 s with the cursor
  as well. A bound of 100000 was over 300 s before and takes 2.1 s
  now. The two observer changes leave the shape quadratic — at bounds
  of 10000, 20000 and 40000 they cost 0.83 s, 3.4 s and 13.6 s — and
  it is the cursor that makes it linear.
  What this costs a program that never searches is at or below this
  machine's run-to-run spread. Over three `cabal bench` rounds
  interleaved against the parent commit, every micro-benchmark moves
  by under 4%; `sum_list_test` and `lambda_test` are slower in 3 of 3
  rounds by about 2% and 3%, which is where the per-store set
  membership test and the per-observer flag read land, and
  `typecheck/pairs_library` stays inside its documented ±10–15%. The
  three existing search benchmarks are all faster in 3 of 3 rounds:
  `search_generate` by 10% (36.5 ms → 32.8 ms), `search_label_alt` by
  3.5% and `search_label` by 2.5%.
  The remaining known O(depth) case is a constraint *with* rules that
  is created and killed once per level: it still leaves one dead
  observer per level, now costing a map lookup and a flag read rather
  than queue traffic. The asymptotic answer there is amortized
  compaction of a variable's observer list, which needs `Var.hs` to
  reach an alive flag through a `SuspensionId`; no measured program
  shows the pattern, so it is not built.
  `run_chr_session/1` (`library(meta)`) is the same driver: it
  predated the search and had become a near-duplicate of `solve/1`, so
  it is now `hostRunChrSession` in `Search.hs` — same fork, same base
  mark, same commit on the first solution, with one runtime-error
  catch around it. That is its one distinct job, and the reason it
  cannot be written as `run_chr_session(G) -> solve(G)` in CHR: the
  language has no catch form. The merge also gives it two behaviours
  it did not have. A `false` is now rolled back to the base mark
  rather than leaving the sub-session's bindings in place, and a
  choice point the goal tells is explored rather than sitting inert —
  a goal that tells `alt` is a search whichever entry point runs it.
  Goal resolution stays outside the catch, so a misspelled or
  unexported goal constraint is still a loud caller error and not a
  `false`. `forkSessionEnv` and `forkSearchSessionEnv` collapsed into
  the latter, since every fork now belongs to a search.
  The cost is that a sub-session's writes are trailed even when no
  enclosing search is running. That is not measured: no benchmark
  calls `run_chr_session/1`, and the one hot caller that used to — the
  type checker's overload resolution — migrated to `solve/1` in
  8082a26. The per-write cost itself is the one recorded above for the
  trail hook.
  Haskell runtime only. See
  [`docs/reference/search.md`](../docs/reference/search.md).
- Unification variables for the Haskell runtime in `src/YCHR/Internal/Runtime/Var.hs`.
- Constraint store for the Haskell runtime in `src/YCHR/Internal/Runtime/Store.hs`.
- Propagation history for the Haskell runtime in `src/YCHR/Internal/Runtime/History.hs`.
- Reactivation queue in `src/YCHR/Internal/Runtime/Reactivation.hs`.
- Haskell interpreter in `src/YCHR/Internal/Runtime/Interpreter.hs`.
- User-defined functions: parsing, renaming, desugaring, compilation, and interpretation.
- Scheme backend (`src/YCHR/Internal/Backend/Scheme.hs`) and runtime (`scheme/ychr/`).
  Each generated library exports a session thunk (named after the library's
  final segment) plus two identifier aliases per exported constraint:
  qualified (`module:name/arity`, always) and short (`name/arity`, when
  unique within the library). The aliases are bound to the underlying
  mangled `tell_*` procedures, so callers reach them by direct identifier
  reference with no runtime lookup. The `(ychr)` umbrella library
  re-exports the runtime, pretty-printer, and `(ychr repl)` helpers
  (`open-session`, `tell`) so end-users can drive a compiled program
  interactively without writing a driver script — see
  [`docs/how-to/scheme-repl.md`](../docs/how-to/scheme-repl.md).

- **Keyed `'$call'` dispatch**: `'$call'` no longer compiles to a dispatcher procedure. A dynamic call compiles to the `ApplyClosure` VM construct, and the program carries a *callables* dispatch table mapping the shape of a closure value to the procedure that implements it — one map lookup where the old code scanned a chain of `If` branches whose length grew with the number of same-arity functions and lifted lambdas the program (including every imported library) defined.
  The table is keyed by `CallableKey {functor, identity, arity}` and mirrors the *evaluables* table that `EvalIs` consults. The functor is the closure term's own functor: `"/"` for a function reference `fun name/arity`, whose identity is the flattened source name (`module:name`) and whose declared arity is the second field; `__closure` for a lifted lambda, whose identity is the lifted function's VM name and which records no arity, so the arity it is *applied* at is used. The functor being part of the key is what stops an ordinary data term whose first argument happens to be a function name from dispatching. The declared-arity half is equally load-bearing: one identity can name several functions (`call/2` and `call/3`), so a key of functor and identity alone would redirect an application of `fun call/2` to `call/3`. The runtime reads the closure's two header fields through their bindings, the way the dispatchers' `BEqual` comparisons dereferenced their operands; captures are passed to the callee as `GetArg` handed them, un-dereferenced. Failures keep the dispatchers' kinds and messages: an unbound closure is an instantiation error, so a rule guard soft-fails and retries after reactivation; a non-callable, or a callable applied at an arity it was not declared at, is a general `call: no matching closure`.
  Nothing is generated per call arity any more, so `genCallFunDispatches`, `callFunProcName`, `PKCallDispatch` and the `(call-dispatch …)` serialization tag are gone, and `Compile.buildCallables` replaced them. `maxCallArity = 10` stays, but only as the surface-language limit `Resolve.termToExpr` enforces (YCHR-16022): it was previously forced by the one-dispatcher-per-arity code generator, and the limit is now aligned with the prelude's `call/N` family rather than with any implementation shape. The Scheme backend registers the table with `register-callable!` and applies closures with `%apply-closure`; the driver emits the same `%apply-closure` for a `'$call'` in a goal. `SchemeDriver`'s function-reference encoding was also brought in line with `Compile.compileExpr`: it minted `module__name` with `vmName` where the table is keyed on the flattened `module:name`, so a function reference reaching a driver could never have matched. That arm is reachable — a function reference passed to a declared function inside a goal resolves and is exercised by the `closure_dispatch_errors` golden case `driver_funref` — though two query-side gaps in the same area remain pre-existing and separate: a `fun` reference used as the direct callee of `'$call'` in a goal does not resolve (`Unknown name 'double/1'`), and a *qualified* one (`fun prelude:max/2`) is mis-read as arity zero (`Module 'prelude' does not export 'max/0'`).
  Measured 2026-09-22 by interleaving rounds of the new benchmark binary with a baseline binary captured from the parent commit, both reading the same fixtures. Two independent five-round comparisons give `typecheck/pairs_library` a 178.4 ms median (176.6–182.0 ms) against 155.0 ms (153.4–156.7 ms), −13.1%, and then 183.2 ms (179.5–202.9 ms) against 157.1 ms (152.5–162.1 ms), −14.2%: faster in 10 of 10 interleaved pairs, each side's own spread a few percent. A single full-suite round gives 188.4 ms → 157.0 ms (−16.7%), and moves the two most `'$call'`-heavy micro-benchmarks, `sum_list_test` (−48%) and `lambda_test` (−33%); `fib` (+5.5%) and `guard` (+1.1%) are inside this benchmark's documented ±10–15% run-to-run spread, as are the search benchmarks. The scaling claim is the durable one: per-`'$call'` cost no longer grows with the number of callables the program defines.

## Work Remaining

The following components have not yet been implemented:

- **Optimizations**: Implement the optimizations listed above, at the appropriate stage. The profiling-driven interpreter items under "Haskell Interpreter Performance" are separate from the paper's catalogue and are also still open.
- **JavaScript backend**: Translate VM programs to JavaScript code.
- **JavaScript runtime**: Implement logical variables, compound terms, constraint store, propagation history, reactivation queue, and iterators in JavaScript.
- **Testing**: Test suite covering individual components and end-to-end execution of standard CHR programs (leq, Fibonacci, Dijkstra, RAM simulator, etc.).


## Golden Tests

Golden tests verify end-to-end correctness by compiling a CHR program, running one or more goals, and comparing the results against expected output files. Each test lives in its own directory under `test/golden/<name>/`.

A test directory contains:

- One or more `.chr` files. All `.chr` files in the directory are compiled together via `compileFiles`, so a test can exercise multi-file programs (imports, exports, cross-module visibility). Goals are module-qualified, so the harness does not need to designate a "main" file.
- Any number of cases, of the three kinds below.

**Positive cases** are pairs of `<case>.goal` and `<case>.expected` files. For each pair, the harness runs the goal via `runProgramWithGoal`, formats the resulting bindings with `prettyBindings`, and asserts equality with the `.expected` file (which uses `K = V` format, one binding per line, sorted alphabetically). A directory may contain any number of pairs.

**Compilation-negative cases** are bare `<case>.error` files (no matching `.goal`) containing a YCHR error code (e.g., `YCHR-20002`). For each one, the harness asserts that compilation (or type-checking) fails with a message containing that code. A directory of compilation-negative cases has no `.goal` files.

**Goal-negative cases** are pairs of `<case>.goal` and `<case>.error` files: compilation and program-level type-checking must succeed, and *running the goal* must throw an error whose message contains every non-empty line of the `.error` file. The first line is conventionally the `YCHR-NNNNN` code; later lines pin a phrase from the actual error text, since a code like `YCHR-60001` covers every runtime error. This is how one directory mixes passing and failing goals over the same program — see `test/golden/mode_boundness_guard/`.

Files with extensions outside `{.chr, .goal, .expected, .error}` are ignored, so per-test READMEs are fine. Subdirectories inside a test directory are ignored.

Discovery rules (enforced by `test/YCHR/GoldenTest.hs`):

- A directory must contain at least one `.chr` file, and at least one `.goal` or `.error` file.
- Every `.goal` must be paired with exactly one of `.expected` (positive) or `.error` (goal-negative); an unpaired `.goal` or `.expected` is an error.
- A directory containing any `.goal` file may not also contain a bare `.error`: it could not be told apart from a compilation-negative case.

Test IDs are nested: a test directory `strings/` with cases `concat_basic.goal` and `len_basic.goal` produces `Golden.strings.concat_basic` and `Golden.strings.len_basic` in tasty (and `test_scheme_golden[strings-concat_basic]`, `test_scheme_golden[strings-len_basic]` in pytest).

Golden tests run on both the Haskell interpreter (`cabal test`) and the Scheme backend (`python3 -m pytest test/scheme/`). The Scheme harness only runs positive cases. Run both with `make test`.

To add a new golden test, create a directory under `test/golden/`, drop the `.chr`, `.goal`, and `.expected` files into it, and the test is picked up automatically.

### Scheme backend skip lists

Some tests pin Haskell-runtime behavior that the Scheme runtime does not (yet) match — typically because the Scheme runtime lacks a primitive (e.g. Guile's r6rs subset has no `quotient`, so integer `div`/`mod` is unimplemented), pretty-prints values differently (e.g. negative numbers as `-2` vs Haskell's `(-2)`, unicode-quoted atoms), or doesn't implement a meta primitive (e.g. `copy_term`). The Scheme harness in `test/scheme/test_golden.py` provides two skip mechanisms so a divergent case does not block `make test`:

- `HASKELL_ONLY` — a set of test-directory names. Every case in those directories is skipped on the Scheme backend.
- `HASKELL_ONLY_CASES` — a set of `(test_dir, case_name)` pairs for finer control when only some cases in a directory diverge.

Both sets are intended as a compatibility bridge, not a permanent exclusion: an entry should be removed once the Scheme runtime is updated to match. Adding to either set requires a comment explaining why the case diverges.


## References

- Van Weert, P., Wuille, P., Schrijvers, T., & Demoen, B. "CHR for Imperative Host Languages." K.U.Leuven. (The primary reference for the compilation scheme and optimizations.)
- Duck, G.J., Stuckey, P.J., García de la Banda, M., & Holzbaur, C. "The refined operational semantics of Constraint Handling Rules." ICLP '04. (Defines ωr.)
- Schrijvers, T. "Analyses, optimizations and extensions of Constraint Handling Rules." PhD thesis, K.U.Leuven, 2005. (Comprehensive treatment of CHR compilation.)
- Frühwirth, T. "Constraint Handling Rules." Cambridge University Press, 2009. (Definitive CHR reference.)
