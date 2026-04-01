# YCHR Virtual Machine Specification

This document specifies the YCHR abstract VM: its instruction set,
s-expression serialization format, and the runtime contract that
backends must implement. The intended audience is backend implementors
targeting languages such as Erlang, Python, Clojure, JavaScript, or
Scheme.

## Overview

A compiled CHR program is a **VM program**: a list of named procedures.
Each procedure has parameters and a body of imperative statements.
Statements may contain expressions. The VM is the *complete interface*
between the compiler and the runtime -- the compiler never emits calls
to runtime functions by name.

There are three kinds of callable entities:

1. **VM instructions** -- dedicated operations for everything the runtime
   provides (constraint store, unification, term manipulation, etc.).
2. **`call-expr`** -- calls to compiler-generated procedures (tell,
   activate, occurrence procedures, etc.).
3. **`host-call`** -- calls to host language functions (arithmetic,
   comparisons, user-written guards and body expressions).


## S-Expression Format

VM programs are serialized as s-expressions with kebab-case identifiers.
The grammar:

```
sexpr  = atom | int | string | list
atom   = [a-zA-Z_][a-zA-Z0-9_-]*
int    = [-]?[0-9]+
string = '"' (escape | [^"\\])* '"'
list   = '(' sexpr* ')'
```

Line comments start with `;` and extend to end of line.

### Conventions

- **Names** (variable names, procedure names, labels, rule names) are
  always double-quoted strings: `"x"`, `"tell_leq"`, `"L1"`.
- **Constraint types** are bare integers (0-based indices): `0`, `1`.
- **Argument indices** are bare integers (0-based): `0`, `1`.
- **Booleans** are bare atoms: `true`, `false`.
- **Variable-length argument lists** are trailing children within the
  enclosing form -- the closing `)` marks the boundary.
- **Fixed-length sub-lists** (e.g. then/else branches, foreach
  conditions and body) are wrapped in `(...)`.


## Top-Level Structure

A serialized compilation unit is a `vm-program` containing the VM
program, the exported names, and the symbol table:

```scheme
(vm-program
  <program>
  (exports <name> ...)
  (symbol-table (<name> <type-id>) ...))
```

- **`<program>`** -- the VM program (see below).
- **`exports`** -- the set of CHR names (constraints and functions)
  visible to external callers. Backends should generate public entry
  points (e.g. `tell_c` wrappers) for each exported name.
- **`symbol-table`** -- maps each CHR name to its 0-based constraint
  type integer. This is the authoritative mapping between symbolic
  names and the numeric type IDs used throughout the VM program.

### Names

CHR names appear in the exports list and symbol table. They come in
two forms:

- **Unqualified**: a bare string, e.g. `"gcd"`.
- **Qualified**: `(qualified "<module>" "<name>")`, e.g.
  `(qualified "order" "leq")`.


## Program

```scheme
(program <num-types>
  <procedure>
  ...)
```

- `<num-types>` -- integer, number of distinct constraint types.
- Zero or more procedure definitions follow.

### Procedure

```scheme
(procedure "<name>" ("<param>" ...)
  <stmt>
  ...)
```

The compiler generates these procedure kinds:

| Procedure | Purpose |
|-----------|---------|
| `tell_c(X_0, ..., X_n)` | Creates a constraint suspension, stores it, calls `activate_c`. |
| `activate_c(susp)` | Extracts arguments from the suspension, tries each occurrence in order. Returns `false` if the constraint survives all occurrences. |
| `occurrence_c_j(id, X_0, ..., X_n)` | Handles the j-th occurrence of constraint c. Iterates over partner constraints, checks guards, fires rules. Returns `true` (early drop) or `false`. |
| `reactivate_dispatch(susp)` | Checks the suspension's constraint type and calls the appropriate `activate_c`. |


## Statements

### let

```scheme
(let "<name>" <expr>)
```

Bind a local variable to the result of an expression.

### assign

```scheme
(assign "<name>" <expr>)
```

Mutate an existing variable.

### if

```scheme
(if <condition> (<then-stmt> ...) (<else-stmt> ...))
```

Conditional execution. Both branches are always present (the else
branch may be an empty list `()`).

### foreach

```scheme
(foreach "<label>" <constraint-type> "<susp-var>"
  (<condition> ...)
  (<body-stmt> ...))
```

Labeled loop over the constraint store. Iterates over all **alive**
stored constraints of the given type that satisfy the index conditions.

Each condition is `(<arg-index> <expr>)` and requires that the
constraint's argument at the given position is `equal` to the
expression (using ask semantics).

The current constraint suspension is bound to `<susp-var>` on each
iteration.

#### Iterator properties

The runtime's iterator must satisfy:

- **Robustness**: if constraints are added or removed during a
  suspended iteration, iteration can resume from the point where it
  was suspended.
- **Correctness**: only alive constraint suspensions are returned.
- **Completeness**: all constraints that were stored at the moment of
  the iterator's creation are returned at least once.
- **Weak termination**: a contiguous iteration does not contain
  duplicate suspensions.

### continue

```scheme
(continue "<label>")
```

Jump to the next iteration of the named `foreach` loop. Used for
backjumping when a partner constraint dies.

### break

```scheme
(break "<label>")
```

Exit the named `foreach` loop.

### return

```scheme
(return <expr>)
```

Return a value from the current procedure.

### expr-stmt

```scheme
(expr-stmt <expr>)
```

Evaluate an expression for its side effects; discard the result.

### store

```scheme
(store <expr>)
```

Add a constraint suspension to the constraint store. The argument must
be a constraint identifier (as returned by `create-constraint`). This
also **registers the constraint as an observer** of its arguments for
reactivation purposes.

### kill

```scheme
(kill <expr>)
```

Remove a constraint from the store and mark it as no longer alive.

### add-history

```scheme
(add-history "<rule-name>" <id-expr> ...)
```

Record that a rule has fired with the given combination of constraint
identifiers. Used to prevent redundant re-firing of propagation rules.

### drain-reactivation-queue

```scheme
(drain-reactivation-queue "<susp-var>"
  <body-stmt> ...)
```

Iterate over all constraints pending reactivation (populated as a side
effect of `unify`). Each pending suspension is bound to `<susp-var>`
and the body statements are executed. The body typically dispatches to
`reactivate_dispatch`.


## Expressions

### Variables and literals

```scheme
(var "<name>")
(int <value>)
(atom "<value>")
(text "<value>")
true
false
wildcard
```

Literals are serialized directly without a `lit` wrapper.

### Procedure and host calls

```scheme
(call-expr "<proc-name>" <arg> ...)
(host-call "<func-name>" <arg> ...)
(host-eval <expr>)
```

- `call-expr` calls a compiler-generated procedure.
- `host-call` calls a host language function.
- `host-eval` evaluates a nested term as a host arithmetic expression.
  Compound terms inside (e.g. `(make-term "+" a b)`) are interpreted
  as function applications.

### Boolean operations

```scheme
(not <expr>)
(and <expr> <expr>)
(or <expr> <expr>)
```

`and` and `or` are short-circuiting.

### Logical variables

```scheme
new-var
```

Creates a fresh unbound logical variable. Serialized as a bare atom
(no parentheses).

### Term operations

```scheme
(make-term "<functor>" <arg> ...)
(match-term <expr> "<functor>" <arity>)
(get-arg <expr> <index>)
```

- `make-term` constructs a compound term.
- `match-term` checks whether a value is a compound term with the
  given functor and arity. Returns a boolean.
- `get-arg` extracts an argument by 0-based index.

### Constraint operations

```scheme
(create-constraint <type> <arg> ...)
(alive <expr>)
(id-equal <expr> <expr>)
(is-constraint-type <expr> <type>)
```

- `create-constraint` allocates a new suspension with a fresh unique
  identifier and `alive = true`. Does **not** add it to the store.
- `alive` checks the alive flag.
- `id-equal` compares two constraint identifiers for equality.
- `is-constraint-type` checks whether a suspension has the given type.

### Propagation history

```scheme
(not-in-history "<rule-name>" <id-expr> ...)
```

Returns `true` if the rule has not previously fired with the given
combination of constraint identifiers.

### Unification and equality

```scheme
(unify <expr> <expr>)
(equal <expr> <expr>)
```

- **`unify`** (tell semantics, Prolog `=`): binds variables, returns
  boolean. As a side effect, pushes affected constraints onto the
  reactivation queue. Used in rule bodies.
- **`equal`** (ask semantics, Prolog `==`): structural equality with no
  mutation. Two distinct unbound variables return `false`. Used in
  guards (guards must not leave half-done bindings on failure).

### Suspension field access

```scheme
(field-get <expr> <field>)
```

Where `<field>` is one of:

```scheme
field-id          ; the unique constraint identifier
(field-arg <i>)   ; constraint argument at 0-based index i
field-type        ; the constraint type (integer)
```


## Runtime Contract

A backend must implement the following runtime capabilities.

### Logical variables

- Creation of fresh unbound variables (`new-var`).
- Binding via unification (`unify`) with occurs-check optional.
- Dereferencing (following binding chains) -- handled transparently
  inside `unify`, `equal`, `field-get`, and `foreach` lookups.
- Observer lists: when a variable is bound, all constraints observing
  it are pushed onto the reactivation queue.

### Compound terms

- Construction (`make-term`), structural matching (`match-term`),
  argument extraction (`get-arg`).
- Representation is backend-specific (e.g. tagged arrays, objects,
  tuples).

### Constraint store

Each suspension contains:

| Field | Description |
|-------|-------------|
| `type` | Constraint type (integer). |
| `id` | Unique constraint identifier. |
| `args` | Array of argument values. |
| `alive` | Boolean flag. |

A simple implementation is a hash map from constraint type to an array
of suspensions. See the [Iterator properties](#foreach) section for
the requirements on iteration under modification.

### Propagation history

A set of tuples `(rule-name, id_1, ..., id_n)`. Must support:

- `add-history`: insert a tuple.
- `not-in-history`: membership test.

### Reactivation queue

A queue of constraint suspensions populated by `unify` when a variable
is bound. Drained by `drain-reactivation-queue`.

### Recursion management

The VM uses plain procedure calls. Backends targeting languages
without tail-call optimization must implement trampolining or an
explicit continuation stack to prevent call-stack overflow. This is
entirely the backend's responsibility.


## Complete Example

The `leq` (less-than-or-equal) handler with a single `reflexivity`
rule, serialized:

```scheme
(vm-program
  (program 1

    ; tell_leq(X, Y): create, store, activate
    (procedure "tell_leq" ("X" "Y")
      (let "id" (create-constraint 0 (var "X") (var "Y")))
      (store (var "id"))
      (expr-stmt (call-expr "activate_leq" (var "id"))))

    ; activate_leq(susp): extract args, try each occurrence
    (procedure "activate_leq" ("susp")
      (let "id" (var "susp"))
      (let "X_0" (field-get (var "susp") (field-arg 0)))
      (let "X_1" (field-get (var "susp") (field-arg 1)))
      (let "d" (call-expr "occurrence_leq_1" (var "id") (var "X_0") (var "X_1")))
      (if (var "d") ((return true)) ())
      (return false))

    ; occurrence_leq_1: reflexivity @ leq(X, X1) <=> X == X1 | true.
    (procedure "occurrence_leq_1" ("id" "X_0" "X_1")
      (if (equal (var "X_0") (var "X_1"))
        ((kill (var "id"))
         (return true))
        ())
      (return false))

    ; reactivate_dispatch(susp): type-based dispatch
    (procedure "reactivate_dispatch" ("susp")
      (if (is-constraint-type (var "susp") 0)
        ((expr-stmt (call-expr "activate_leq" (var "susp"))))
        ())))

  (exports (qualified "mymodule" "leq"))

  (symbol-table
    ((qualified "mymodule" "leq") 0)))
```
