# CHR Compiler for Dynamically-Typed Procedural Languages

## Project Overview

This project implements a compiler for Constraint Handling Rules (CHR) that targets dynamically-typed procedural languages. The surface language is standard CHR with Prolog-compatible syntax. The compiler is implemented in Haskell and compiles CHR to an internal abstract VM. The abstract VM representation can then be compiled to JavaScript or Scheme, or interpreted directly in Haskell.

The project is based on the compilation scheme described in:

> Peter Van Weert, Pieter Wuille, Tom Schrijvers, and Bart Demoen.
> "CHR for Imperative Host Languages."
> Department of Computer Science, K.U.Leuven, Belgium.

This paper presents a comprehensive treatment of compiling CHR to imperative host languages, covering language design, a basic compilation scheme following the refined operational semantics (ωr), an extensive catalog of optimizations, and novel recursion optimizations (trampoline and explicit continuation stack) needed because imperative hosts typically lack tail call optimization.


## Architecture

The system has three layers:

```
CHR source (Prolog-compatible syntax)
  │
  ▼
Frontend: Parser
  │
  ▼
CHR-to-VM Compiler (Haskell)
  │
  ▼
Abstract VM Program
  │
  ├──▶ JavaScript backend  ──▶  JS code + JS runtime library
  ├──▶ Scheme backend      ──▶  Scheme code + Scheme runtime library
  └──▶ Haskell interpreter ──▶  Direct execution with Haskell runtime
```

### Frontend

Parses standard CHR with Prolog-compatible syntax. Produces an internal representation of CHR handlers: constraint declarations, rule definitions (simplification, propagation, simpagation), with heads, guards, and bodies.

### CHR-to-VM Compiler

Implemented in Haskell. Transforms CHR handlers into VM programs following the compilation scheme from the paper. This includes:

- Head Normal Form (HNF) transformation: all head arguments become distinct variables, implicit equalities become explicit guard conditions.
- Occurrence numbering: occurrences are numbered top-to-bottom, right-to-left as specified by ωr.
- Generation of procedures: `tell_c`, `activate_c`, `occurrence_c_j`, `reactivate_dispatch`, `reactivate_all`.

Some optimizations are applied at this stage (see the Optimizations section).

### Backends

Each backend translates the abstract VM program to target language code. The generated code depends on a target-specific runtime library.

### Runtime Libraries

Each backend (JavaScript, Scheme, Haskell) requires a runtime library that provides the substrate for CHR execution. The runtime implements:

- **Logical variables**: creation, binding, dereferencing (following binding chains), unification with occurs check (optional), and observer lists for reactivation.
- **Algebraic data types / compound terms**: Prolog-style terms like `f(X, g(Y, 3))`. Construction, structural pattern matching (one-way unification), functor/arity inspection. JavaScript and Scheme need explicit representations (e.g., tagged arrays or objects).
- **Constraint store**: storage, removal, liveness tracking of constraint suspensions. Indexed lookup with iterator support satisfying robustness, correctness, completeness, and weak termination properties.
- **Propagation history**: set of tuples recording which rule fired with which combination of constraint identifiers, to prevent redundant re-firing of propagation rules.
- **Reactivation queue**: populated as a side effect of unification when a variable gets bound, containing all constraints that observe the affected variable and need to be reconsidered.
- **Recursion management**: trampolining, explicit continuation stacks, or other mechanisms to avoid call stack overflow. This is the responsibility of each backend, not the VM.

From the VM's perspective, logical variables and compound terms are opaque values. The VM provides dedicated instructions for operating on them (`NewVar`, `Unify`, `Equal`, `MakeTerm`, `MatchTerm`, `GetArg`), and the runtime implements these instructions using whatever representation is natural for the target language.


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
- **`reactivate_all`**: Iterates over all constraint types, reactivating every stored constraint. Used for the modification problem (when host language code may have changed values).

### Statements

| Statement | Description |
|-----------|-------------|
| `Let name expr` | Bind a local variable to the result of an expression. |
| `Assign name expr` | Mutate an existing variable. |
| `If expr thenStmts elseStmts` | Conditional execution. |
| `Foreach label cType suspVar conditions body` | Labeled loop over the constraint store. Iterates over all stored constraints of type `cType` satisfying the index conditions. Each condition `(argIndex, expr)` requires that the argument at `argIndex` is `Equal` to `expr`. Binds the current suspension to `suspVar`. |
| `Continue label` | Jump to the next iteration of the labeled `Foreach` loop. Used for backjumping when a partner constraint dies. |
| `Break label` | Exit the labeled `Foreach` loop. |
| `Return expr` | Return a value from the current procedure. |
| `ExprStmt expr` | Evaluate an expression for its side effects, discard the result. Used for procedure calls and host language calls in statement position. |
| `Store expr` | Add a constraint suspension to the constraint store. Also registers the constraint as an observer of its arguments for reactivation. |
| `Kill expr` | Remove a constraint from the store, mark as not alive. |
| `AddHistory ruleName [expr]` | Record a rule firing in the propagation history. |
| `DrainReactivationQueue suspVar body` | Iterate over all constraints pending reactivation (populated by `Unify`), binding each to `suspVar` and executing `body`. The body dispatches to the appropriate activate procedure. |

### Expressions

| Expression | Description |
|------------|-------------|
| `Var name` | Variable reference. |
| `Lit literal` | Literal value (integer, atom, boolean). |
| `CallExpr name [expr]` | Call a compiler-generated procedure, return result. |
| `HostCall name [expr]` | Call a host language function. |
| `Not expr` | Logical negation. |
| `And expr expr` | Logical conjunction (short-circuiting). |
| `Or expr expr` | Logical disjunction (short-circuiting). |
| `NewVar` | Create a fresh unbound logical variable. |
| `MakeTerm functor [expr]` | Construct a compound term. |
| `MatchTerm expr functor arity` | Check if a value is a compound term with the given functor and arity. Returns boolean. |
| `GetArg expr index` | Extract an argument from a compound term by 0-based index. |
| `CreateConstraint cType [expr]` | Create a constraint suspension (not yet stored). Returns a constraint identifier. |
| `Alive expr` | Check if a constraint is still alive. |
| `IdEqual expr expr` | Compare two constraint identifiers for equality. |
| `IsConstraintType expr name` | Check if a suspension has the given constraint type. Used for dispatch in reactivation. |
| `NotInHistory ruleName [expr]` | Check that a rule has not fired with this combination of constraint identifiers. |
| `Unify expr expr` | Unify two terms (tell semantics). Returns boolean. May mutate variables. Pushes affected constraints onto the reactivation queue. |
| `Equal expr expr` | Check equality of two terms (ask semantics). No mutation. Uses Prolog `==` semantics: two distinct unbound variables are not equal. |
| `FieldGet expr field` | Access a field of a constraint suspension. |

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
- `AtomLit String` — atom (symbolic constant)
- `BoolLit Bool` — boolean literal


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
4. For the modification problem (arbitrary host language changes), the compiler generates a `reactivate_all` procedure that iterates all constraint types.

### Terms and Variables Are Opaque

The VM treats logical variables and compound terms as opaque values. It provides instructions for creating and operating on them (`NewVar`, `Unify`, `Equal`, `MakeTerm`, `MatchTerm`, `GetArg`), but their internal representation is entirely the runtime's concern. This means:

- Dereferencing (following binding chains) is handled internally by the runtime inside `Unify`, `Equal`, `FieldGet`, and `Foreach` lookups.
- The compiler does not need to emit explicit dereference calls.
- Each backend can choose the most natural representation for its target language.

### Recursion Optimizations Belong to Backends

The VM uses plain procedure calls (`CallExpr`) and does not include trampoline or explicit stack instructions. Each backend is responsible for preventing call stack overflow using the technique most appropriate for its target:

- JavaScript: trampolining
- Scheme: tail call optimization (in compliant implementations) or trampolining
- Haskell interpreter: native support for deep recursion, or explicit strategy

### No Runtime Calls by Name

The compiler never emits calls to runtime functions by name. Every runtime capability is expressed as a dedicated VM instruction. This ensures backends can freely organize their runtime libraries without affecting the compiler. The only named calls the compiler emits are to its own generated procedures (`CallExpr`) and to host language functions (`HostCall`).

### Foreach with Labeled Control Flow

Partner constraint iteration uses `Foreach` loops with labels. `Continue label` and `Break label` target specific outer loops, enabling:

- **Backjumping**: when a partner constraint dies after body execution, `Continue` resumes the appropriate outer loop.
- **Early drop**: when the active constraint is killed, `Break` (or `Return`) exits all loops.

The index conditions in `Foreach` use `Equal` (ask) semantics. The runtime's iterator implementation handles dereferencing and indexing transparently.

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

The operations map to this structure as follows:

- **`CreateConstraint`**: allocates a new suspension with a fresh unique identifier and `alive = true`. Does not add it to the store.
- **`Store`**: looks up (or creates) the array for the constraint's type and appends the suspension. Also registers the suspension as an observer of its arguments (for the reactivation mechanism).
- **`Kill`**: sets `alive = false` on the suspension. The suspension remains in the array but is skipped during iteration.
- **`Alive`**: reads the `alive` flag.
- **`Foreach` with conditions**: iterates the array for the given constraint type, skipping dead entries, and checking each index condition by comparing the suspension's argument at the given position with the provided value using `Equal` semantics. Only suspensions passing all conditions are yielded to the loop body.
- **`Foreach` with no conditions**: iterates the array for the given constraint type, skipping dead entries.

This is O(n) per lookup where n is the number of suspensions (alive or dead) of the given constraint type. For a first implementation this is acceptable. More sophisticated indexing (hash-based or tree-based indexes on specific argument positions) can be added later as a runtime optimization without any changes to the VM or the compiler.

Iterator robustness under modification is straightforward with this structure. Iteration proceeds by integer index over the array. Kills during iteration only set a flag, so the iterator is unaffected. New constraints appended during iteration go to the end of the array. To avoid processing newly added constraints (which have already been activated themselves), the iterator records the array length at creation time and stops there.


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

For a constraint `leq/2` with 7 occurrences, the compiler generates:

- `tell_leq(X, Y)` — creates suspension, stores, activates
- `activate_leq(id, X, Y)` — tries occurrences 1 through 7 with early drop
- `occurrence_leq_1(id, X, Y)` through `occurrence_leq_7(id, X, Y)` — each handles one occurrence
- `reactivate_dispatch(susp)` — type-based dispatch to appropriate activate procedure
- `reactivate_all()` — iterates all constraint types, reactivates each stored constraint

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


## Already implemented

- Surface AST types in `src/YCHR/Parsed.hs`.
- Desugared AST types in `src/YCHR/Desugared.hs`.
- Renaming (qualifying constraint names) in `src/YCHR/Rename.hs`.
- Desugaring in `src/YCHR/Desugar.hs`.
- A user-friendly DSL to construct a CHR program in Haskell in `src/YCHR/DSL.hs`.
- VM types in `src/YCHR/VM.hs`.
- Unification variables for the Haskell runtime in `src/YCHR/Runtime/Var.hs`.
- Constraint store for the Haskell runtime in `src/YCHR/Runtime/Store.hs`.
- Propagation history for the Haskell runtime in `src/YCHR/Runtime/History.hs`.
- Reactivation queue in `src/YCHR/Runtime/Reactivation.hs`.
- Haskell interpreter in `src/YCHR/Runtime/Interpreter.hs`.


## Work Remaining

The following components have not yet been implemented:

- **Frontend parser**: Parse standard CHR with Prolog-compatible syntax into a close-to-surface representation of handlers, constraints, and rules.
- **CHR-to-VM compiler**: Transform parsed CHR handlers into VM programs. Includes HNF transformation, occurrence numbering, and generation of all required procedures.
- **Optimizations**: Implement the optimizations listed above, at the appropriate stage.
- **JavaScript backend**: Translate VM programs to JavaScript code.
- **JavaScript runtime**: Implement logical variables, compound terms, constraint store, propagation history, reactivation queue, and iterators in JavaScript.
- **Scheme backend**: Translate VM programs to Scheme code.
- **Scheme runtime**: Same capabilities as the JavaScript runtime, in Scheme.
- **Testing**: Test suite covering individual components and end-to-end execution of standard CHR programs (leq, Fibonacci, Dijkstra, RAM simulator, etc.).


## References

- Van Weert, P., Wuille, P., Schrijvers, T., & Demoen, B. "CHR for Imperative Host Languages." K.U.Leuven. (The primary reference for the compilation scheme and optimizations.)
- Duck, G.J., Stuckey, P.J., García de la Banda, M., & Holzbaur, C. "The refined operational semantics of Constraint Handling Rules." ICLP '04. (Defines ωr.)
- Schrijvers, T. "Analyses, optimizations and extensions of Constraint Handling Rules." PhD thesis, K.U.Leuven, 2005. (Comprehensive treatment of CHR compilation.)
- Frühwirth, T. "Constraint Handling Rules." Cambridge University Press, 2009. (Definitive CHR reference.)
