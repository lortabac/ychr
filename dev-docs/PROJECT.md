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
Parser ──▶ Rename ──▶ Resolve ──▶ Desugar ──▶ TypeCheck (optional)
                                                  │
                                                  ▼
                                       CHR-to-VM Compiler (Haskell)
                                                  │
                                                  ▼
                                       Abstract VM Program
                                                  │
                                ┌─────────────────┼─────────────────┐
                                ▼                 ▼                 ▼
                          JavaScript          Scheme           Haskell
                          backend             backend          interpreter
```

### Frontend

Parses standard CHR with Prolog-compatible syntax. Produces an internal representation of CHR handlers: constraint declarations, rule definitions (simplification, propagation, simpagation), with heads, guards, and bodies. The frontend pipeline runs Rename → Resolve (module flattening + declaration-kind validation) → Desugar, with an optional static type-check stage on the desugared AST.

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

A VM program is a list of named procedures. Each procedure has a name, a parameter list, and a body consisting of a sequence of statements. The compiler generates the following kinds of procedures for each CHR handler:

- **`tell_c`**: Entry point for adding a constraint. Creates a suspension, stores it, and calls `activate_c`.
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
| `Store idExpr` | Add a constraint suspension to the constraint store. Also registers the constraint as an observer of its arguments for reactivation. |
| `Kill idExpr` | Remove a constraint from the store, mark as not alive. |
| `AddHistory ruleName [idExpr]` | Record a rule firing in the propagation history. |
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
| `BNotInHistory ruleName [idExpr]` | Check that a rule has not fired with this combination of constraint identifiers. |
| `BUnify valExpr valExpr` | Unify two terms (tell semantics). Returns success. May mutate variables. Pushes affected constraints onto the reactivation queue. |
| `BFromVal valExpr` | Bridge a value-producing expression into boolean position; runtime-checks that the wrapped `ValExpr` evaluates to `VBool`. Used at the early-drop check and for user expressions in guards. |
| `BEvalDeep boolExpr` | Evaluate in deep-deref mode (mirrors `EvalDeep` for booleans). |

#### Call arguments (`CallArg`)

| Expression | Description |
|------------|-------------|
| `AVal valExpr` / `AId idExpr` | Procedure-call argument tagged by kind. |

### Fields

Constraint suspensions expose the following fields via `FieldGet`:

| Field | Description |
|-------|-------------|
| `FieldId` | The unique constraint identifier. |
| `FieldArg index` | A constraint argument by 0-based index. |
| `FieldType` | The constraint type (for reactivation dispatch). |

Internal fields such as `alive`, `stored`, and `activated` are managed by the runtime and accessed only through dedicated VM instructions (`Alive`, `Store`, etc.).

### Literals

- `IntLit Int` — integer literal
- `FloatLit Double` — floating-point literal
- `AtomLit Text` — atom (symbolic constant)
- `TextLit Text` — string literal
- `BoolLit Bool` — boolean literal
- `WildcardLit` — anonymous placeholder, matches any value in patterns


## Key Design Decisions

### Unification Semantics

Two operations are provided:

- **`Unify` (tell)**: Prolog `=` semantics. Binds variables, returns success/failure as a boolean. As a side effect, pushes affected constraints onto the reactivation queue.
- **`Equal` (ask)**: Prolog `==` semantics. Identity/structural equality with no mutation. Two distinct unbound variables return `false`. Used in guards.

The distinction matters because guards must not leave half-done bindings if they fail. Guards use `Equal`, bodies use `Unify`.

### Reactivation Model

Reactivation follows this flow:

1. When a constraint is stored (`Store`), the runtime registers it as an observer of its arguments.
2. When `Unify` binds a variable, the runtime pushes all constraints observing that variable onto a reactivation queue.
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

`Foreach` linearly scans the array for the given type, skipping dead entries and checking the index conditions with `Equal` semantics. This is O(n) per lookup; smarter indexing (hash- or tree-based) can be added later as a runtime change without affecting the VM or compiler. See `src/YCHR/Runtime/Store.hs` for the exact layout and iterator semantics.


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
2. Extract partner fields using `FieldGet`.
3. Check constraint ID distinctness using `Not (IdEqual ...)`.
4. Check guards using `Equal` (for implicit equality guards) and `HostCall` (for user-written guards).
5. Check propagation history using `NotInHistory` (for propagation rules only).
6. Fire the rule: `AddHistory` (propagation rules), `Kill` removed constraints, execute body.
7. After body: check `Alive` for active constraint (early drop) and partner constraints (backjumping).
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
| Late Storage | Postpone storing until necessary. | CHR-to-VM compiler |
| Late Allocation | Postpone suspension creation until necessary. | CHR-to-VM compiler |
| Propagation History Maintenance | Garbage collect stale history entries. | Runtime |
| Propagation History Elimination | Remove history when not needed. | CHR-to-VM compiler |
| Guard Simplification | Remove redundant guard conjuncts. | CHR-to-VM compiler |
| Passive Occurrences | Skip occurrences that can never fire. | CHR-to-VM compiler |
| Selective Constraint Reactivation | Reactivate only affected constraints. | Runtime (observer pattern) |
| Delay Avoidance | Skip reactivation when modifications cannot affect guards. | CHR-to-VM compiler |
| Memory Reuse | Reuse suspension memory for replaced constraints. | Runtime / Backend |
| Recursion Optimizations | Trampoline, explicit stack. | Backend |


## User-Defined Functions

The language supports user-defined functions: pattern-matching, top-to-bottom evaluated equations with optional guard clauses. Functions are declared with `:- function` directives and defined with Erlang-style equations using `->`:

```
:- function factorial/1.
factorial(0) -> 1.
factorial(N) | N > 0 -> N * factorial(N - 1).
```

Functions are callable in guards, `is` RHS expressions, and rule body position (discarding the result). They compile to ordinary VM procedures via `CallExpr` — no new VM instructions are needed.

Equation patterns are normalized using the same Head Normal Form (HNF) machinery as rule heads: non-variable patterns become fresh variables with explicit guard conditions. Equations are tried top-to-bottom; if no equation matches, a runtime error is raised.

Function names are qualified like constraint names and cannot collide with constraint declarations in the same module.

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

- Frontend parser in `src/YCHR/Parser.hs`.
- Surface AST types in `src/YCHR/Parsed.hs`.
- Desugared AST types in `src/YCHR/Desugared.hs`.
- Renaming (qualifying constraint names) in `src/YCHR/Rename.hs`.
- Resolution (flattens modules into a single program, validates declaration kinds) in `src/YCHR/Resolve.hs` and `src/YCHR/Resolved.hs`.
- Desugaring in `src/YCHR/Desugar.hs`.
- A user-friendly DSL to construct a CHR program in Haskell in `src/YCHR/DSL.hs`. See [`docs/reference/dsl.md`](../docs/reference/dsl.md) for the user-facing reference.
- VM types in `src/YCHR/VM/Types.hs` (re-exported from `src/YCHR/VM.hs`).
- CHR-to-VM compiler in `src/YCHR/Compile.hs`.
- Optional static type checker in `src/YCHR/TypeCheck.hs` (driver) and `src/YCHR/TypeCheck/{Compiled,TH}.hs`. Implemented as a CHR program; programs without type annotations are accepted unchanged.
- Unification variables for the Haskell runtime in `src/YCHR/Runtime/Var.hs`.
- Constraint store for the Haskell runtime in `src/YCHR/Runtime/Store.hs`.
- Propagation history for the Haskell runtime in `src/YCHR/Runtime/History.hs`.
- Reactivation queue in `src/YCHR/Runtime/Reactivation.hs`.
- Haskell interpreter in `src/YCHR/Runtime/Interpreter.hs`.
- User-defined functions: parsing, renaming, desugaring, compilation, and interpretation.
- Scheme backend (`src/YCHR/Backend/Scheme.hs`) and runtime (`scheme/ychr/`).


## Work Remaining

The following components have not yet been implemented:

- **Optimizations**: Implement the optimizations listed above, at the appropriate stage.
- **JavaScript backend**: Translate VM programs to JavaScript code.
- **JavaScript runtime**: Implement logical variables, compound terms, constraint store, propagation history, reactivation queue, and iterators in JavaScript.
- **Testing**: Test suite covering individual components and end-to-end execution of standard CHR programs (leq, Fibonacci, Dijkstra, RAM simulator, etc.).


## Golden Tests

Golden tests verify end-to-end correctness by compiling a CHR program, running one or more goals, and comparing the results against expected output files. Each test lives in its own directory under `test/golden/<name>/`.

A test directory contains:

- One or more `.chr` files. All `.chr` files in the directory are compiled together via `compileFiles`, so a test can exercise multi-file programs (imports, exports, cross-module visibility). Goals are module-qualified, so the harness does not need to designate a "main" file.
- Either positive cases or negative cases, but not both.

**Positive cases** are pairs of `<case>.goal` and `<case>.expected` files. For each pair, the harness runs the goal via `runProgramWithGoal`, formats the resulting bindings with `prettyBindings`, and asserts equality with the `.expected` file (which uses `K = V` format, one binding per line, sorted alphabetically). A directory may contain any number of pairs.

**Negative cases** are `<case>.error` files containing a YCHR error code (e.g., `YCHR-20002`). For each one, the harness asserts that compilation (or type-checking) fails with a message containing that code. A negative-test directory has no `.goal` files.

Files with extensions outside `{.chr, .goal, .expected, .error}` are ignored, so per-test READMEs are fine. Subdirectories inside a test directory are ignored.

Discovery rules (enforced by `test/YCHR/GoldenTest.hs`):

- A directory must contain at least one `.chr` file.
- Mixing `.goal` and `.error` files in the same directory is an error.
- An orphan `.goal` (no matching `.expected`) or orphan `.expected` (no matching `.goal`) is an error.

Test IDs are nested: a test directory `fib/` with cases `fib.goal` and `fib_small.goal` produces `Golden.fib.fib` and `Golden.fib.fib_small` in tasty (and `test_scheme_golden[fib-fib]`, `test_scheme_golden[fib-fib_small]` in pytest).

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
