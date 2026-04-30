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

- **Names** (variable names, procedure names, labels) are always
  double-quoted strings: `"x"`, `"tell_mymodule__leq2"`, `"L1"`.
- **Constraint types** are bare integers (0-based indices): `0`, `1`.
- **Rule identifiers** are bare integers (0-based indices): `0`, `1`.
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
  (exports (<name> <arity>) ...)
  (symbol-table (<name> <arity> <type-id>) ...))
```

- **`<program>`** -- the VM program (see below).
- **`exports`** -- the set of CHR identifiers (name + arity) visible
  to external callers. Backends should generate public entry points
  (e.g. `tell_c` wrappers) for each exported identifier.
- **`symbol-table`** -- maps each CHR identifier (name + arity) to
  its 0-based constraint type integer. This is the authoritative
  mapping between symbolic names and the numeric type IDs used
  throughout the VM program. The same name with different arities
  gets distinct type IDs (e.g. `foo/1` and `foo/2` are separate
  constraint types).

### Names

CHR names appear in the exports list and symbol table. The
serialization format supports two forms:

- **Qualified**: `(qualified "<module>" "<name>")`, e.g.
  `(qualified "order" "leq")`.
- **Unqualified**: a bare string, e.g. `"gcd"`.

In practice, all names in the symbol table and exports are qualified,
since the renaming pass resolves every constraint and function to its
defining module before compilation.


## Program

```scheme
(program <num-types>
  (type-names "<type-name>" ...)
  <num-rules>
  (rule-names "<rule-name>" ...)
  <procedure>
  ...)
```

- `<num-types>` -- integer, number of distinct constraint types.
- `type-names` -- list of strings indexed by constraint type integer.
  `type-names[i]` is the flattened source name (e.g.
  `"mymodule:leq"`) of the constraint type with index `i`. Used by
  runtime introspection.
- `<num-rules>` -- integer, number of rules in the compilation unit.
- `rule-names` -- list of strings indexed by rule identifier integer.
  `rule-names[i]` is the source name of the rule with id `i`, or a
  synthetic `"__rule_N"` fallback for anonymous rules. Used by
  runtime introspection.
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
| `func_f(arg_0, ..., arg_n)` | Evaluates a user-defined function. |


### Procedure Naming

Procedure names are generated deterministically from the constraint or
function name, module qualifier, and arity. The scheme guarantees
injectivity: distinct identifiers always produce distinct procedure
names.

All constraints and functions are fully qualified by the renaming
pass, so procedure names always include a module component.

**Format:**

```
<prefix>_<module>__<name><arity>
```

Where `<prefix>` is one of `tell`, `activate`, `occurrence`, or
`func`. The double underscore (`__`) separates the module from the
name. Arity is appended as a plain decimal integer with no separator.

Occurrence procedures append the 1-based occurrence number after an
additional underscore:

```
occurrence_<module>__<name><arity>_<occ-number>
```

**Examples** for a constraint `order:leq/2`:

| Procedure | Name |
|-----------|------|
| tell | `tell_order__leq2` |
| activate | `activate_order__leq2` |
| occurrence 1 | `occurrence_order__leq2_1` |
| occurrence 3 | `occurrence_order__leq2_3` |

For a function `math:factorial/1`:

| Procedure | Name |
|-----------|------|
| func | `func_math__factorial1` |

The `reactivate_dispatch` procedure is unique and not parameterized by
constraint name.

**Non-ASCII encoding.** Characters outside the ASCII range are encoded
as `__u<hex>__` where `<hex>` is the Unicode code point in
hexadecimal. For example, a constraint named `café` produces the
encoded component `caf__u00e9__`. ASCII characters (including
punctuation and underscores) pass through unchanged.

**Restrictions.** Double underscores (`__`) are forbidden in atom
names (both quoted and unquoted) at the source level. This ensures the
`__` separator is unambiguous.

**Term functor names** (used in `make-term` and `match-term`) follow
the same encoding and module separator rules but do **not** include
arity, since the arity is already explicit in those instructions.


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
(add-history <rule-id> <id-expr> ...)
```

Record that a rule has fired with the given combination of constraint
identifiers. Used to prevent redundant re-firing of propagation rules.
`<rule-id>` is the rule's integer identifier (see the program's
`rule-names` table for the corresponding source name).

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
```

- `call-expr` calls a compiler-generated procedure.
- `host-call` calls a host language function.

### Deep deref-aware evaluation

```scheme
(eval-deep <expr>)
```

- `eval-deep` switches the nested expression into deep deref-aware
  evaluation: variable references are dereferenced (following binding
  chains) before use, and this mode propagates recursively into
  sub-expressions (`call-expr`, `make-term`, etc.). Used for guard
  expressions and the right-hand side of `is`.

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
(not-in-history <rule-id> <id-expr> ...)
```

Returns `true` if the rule has not previously fired with the given
combination of constraint identifiers. `<rule-id>` is the rule's
integer identifier (see the program's `rule-names` table for the
corresponding source name).

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

A set of tuples `(rule-id, id_1, ..., id_n)`, where `rule-id` is the
integer identifier assigned to the rule at compile time. Must
support:

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
rule, serialized. The constraint is `mymodule:leq/2`, so procedure
names use the pattern `<prefix>_mymodule__leq2`:

```scheme
(vm-program
  (program 1
    (type-names "mymodule:leq")
    1
    (rule-names "reflexivity")

    ; tell_mymodule__leq2(X, Y): create, store, activate
    (procedure "tell_mymodule__leq2" ("X_0" "X_1")
      (let "id" (create-constraint 0 (var "X_0") (var "X_1")))
      (store (var "id"))
      (expr-stmt (call-expr "activate_mymodule__leq2" (var "id"))))

    ; activate_mymodule__leq2(susp): extract args, try each occurrence
    (procedure "activate_mymodule__leq2" ("susp")
      (let "id" (var "susp"))
      (let "X_0" (field-get (var "susp") (field-arg 0)))
      (let "X_1" (field-get (var "susp") (field-arg 1)))
      (let "d" (call-expr "occurrence_mymodule__leq2_1"
                  (var "id") (var "X_0") (var "X_1")))
      (if (var "d") ((return true)) ())
      (return false))

    ; occurrence_mymodule__leq2_1:
    ;   reflexivity @ leq(X, X1) <=> X == X1 | true.
    (procedure "occurrence_mymodule__leq2_1" ("id" "X_0" "X_1")
      (if (equal (var "X_0") (var "X_1"))
        ((kill (var "id"))
         (return true))
        ())
      (return false))

    ; reactivate_dispatch(susp): type-based dispatch
    (procedure "reactivate_dispatch" ("susp")
      (if (is-constraint-type (var "susp") 0)
        ((expr-stmt (call-expr "activate_mymodule__leq2" (var "susp"))))
        ())))

  (exports ((qualified "mymodule" "leq") 2))

  (symbol-table
    ((qualified "mymodule" "leq") 2 0)))
```
