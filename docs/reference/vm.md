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

### Expression kinds: values, ids, and bools

The VM has three disjoint kinds of expression:

- **Value expressions** evaluate to ordinary runtime values: integers,
  floats, atoms, strings, booleans, logical variables, compound terms,
  wildcards. They populate every position where a unifiable value is
  expected (procedure arguments, term construction, host call
  arguments, the right-hand side of `is`).
- **Id expressions** evaluate to constraint identifiers (suspension
  references). They populate every position that operates on a stored
  constraint (`store`, `kill`, `add-history`, `balive`, `bid-equal`,
  `bis-constraint-type`, `bnot-in-history`, `field-arg`, `field-type`).
- **Bool expressions** evaluate to booleans. They populate every
  boolean-position operand: the condition of `if`, the body of
  `bool-expr-stmt`, and the operands of `bnot`/`band`/`bor`. The
  syntactically-bool constructors (`bnot`, `band`, `bor`,
  `bmatch-term`, `bequal`, `bid-equal`, `balive`,
  `bis-constraint-type`, `bnot-in-history`, `bunify`) live here, plus
  the explicit bridge `bfrom-val` for value expressions whose
  boolean-ness is only known at runtime (e.g. user-defined function
  calls in guards). The bridge carries a runtime shape check; every
  other bool position is statically a boolean.

Constraint identifiers cannot flow into unification or term
construction, and value expressions cannot directly satisfy a boolean
position — they must be wrapped in `bfrom-val`. The three kinds are
physically distinct in the IR. A backend can keep one runtime
representation for ids and the suspension they refer to (the Haskell
and Scheme runtimes do — a suspension reference *is* its identifier)
but the IR statically distinguishes the positions.

A handful of forms are explicitly heterogeneous: procedures that take
a mix of value and id parameters use the `arg-val` / `arg-id` wrapper
at the call boundary (see `call-expr`). Variable references split into
`var` (value-bound) and `id-var` (id-bound). There is no `bool-var`:
the only place a boolean is bound to a name in compiler-generated code
is the early-drop result, which is bound as a value (`let-val` /
`var`) and bridged at the read site with `bfrom-val`.


## S-Expression Format

VM programs are serialized as s-expressions with kebab-case identifiers.
The grammar:

```
sexpr  = atom | int | float | string | list
atom   = [a-zA-Z_][a-zA-Z0-9_-]*
int    = [-]?[0-9]+
float  = [-]?[0-9]+\.[0-9]+([eE][-+]?[0-9]+)?
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
- **Boolean value literals** are bare atoms: `true`, `false`. Boolean
  expression literals (the bool-position counterpart) are bare atoms
  `btrue` / `bfalse`. The two coexist because `Lit (BoolLit _)` in
  value position and `BLit _` in boolean position are different IR
  constructors at different positional types.
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

Procedure parameters are positional. Each parameter's kind (value or
constraint id) is determined by how the caller's `call-expr` tags the
corresponding argument (`arg-val` or `arg-id`). Within the body,
references use `var` for value-bound parameters and `id-var` for
id-bound parameters.

The compiler generates these procedure kinds:

| Procedure | Purpose | Parameter kinds |
|-----------|---------|-----------------|
| `tell_c(X_0, ..., X_n)` | Creates a constraint suspension, stores it, calls `activate_c`. | all values |
| `activate_c(susp)` | Extracts arguments from the suspension, tries each occurrence in order. Returns `false` if the constraint survives all occurrences. | id |
| `occurrence_c_j(id, X_0, ..., X_n)` | Handles the j-th occurrence of constraint c. Iterates over partner constraints, checks guards, fires rules. Returns `true` (early drop) or `false`. | id, then values |
| `reactivate_dispatch(susp)` | Checks the suspension's constraint type and calls the appropriate `activate_c`. | id |
| `func_f(arg_0, ..., arg_n)` | Evaluates a user-defined function. | all values |
| `call_n(closure, arg_0, ..., arg_{n-1})` | Dispatches a first-class function value to its compiled procedure. | all values |


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
constraint name. The `call_n` dispatchers (`call_1`, `call_2`, ...)
are likewise unique per call arity.

**Non-ASCII encoding.** Characters outside the ASCII range are encoded
as `%%u<hex>` where `<hex>` is the Unicode code point in lowercase
hexadecimal, padded to exactly six digits. There is no closing
delimiter — the escape is always 9 characters long. For example, a
constraint named `café` produces the encoded component
`caf%%u0000e9`. ASCII characters (including punctuation and
underscores) pass through unchanged.

This encoding applies to *term functor* names used by `make-term`,
`bmatch-term`, and runtime values. The separate identifier encoding
used for generated procedure names (`tell_*`, `activate_*`, `func_*`)
keeps the older `__u<hex>__` form because procedure names must be
valid identifiers in every target language (Scheme, JavaScript),
neither of which accept `%`.

**Restrictions.** Two infixes are forbidden in source atom names
(both quoted and unquoted) at the source level:

- `__` — reserved as the module/base separator in mangled symbols.
- `%%u` — reserved as the unicode-escape marker in mangled symbols.

Together with the fixed-width escape (no `__` in encoded text), these
restrictions make the mangling injective: the only `__` in a mangled
symbol is the module separator, and the only `%%u` is the start of a
unicode escape.

**Term functor names** (used in `make-term` and `bmatch-term`) follow
the same encoding and module separator rules but do **not** include
arity, since the arity is already explicit in those instructions.


## Statements

Each `let`/`assign` form comes in two variants: one for binding values,
one for binding constraint identifiers. Statements that operate on
stored constraints (`store`, `kill`, `add-history`) take an
*id-expression*. The condition of `if` and the operand of
`bool-expr-stmt` take a *bool-expression*. Other statements
(`return`, `expr-stmt`, `foreach` index conditions) take a
*value-expression*.

### let-val / let-id

```scheme
(let-val "<name>" <val-expr>)
(let-id  "<name>" <id-expr>)
```

Bind a local variable to the result of an expression. The two variants
differ only by the kind they bind. References to the bound name use
`var` (after `let-val`) or `id-var` (after `let-id`).

### assign-val / assign-id

```scheme
(assign-val "<name>" <val-expr>)
(assign-id  "<name>" <id-expr>)
```

Mutate an existing variable. Same kind discipline as `let-val` /
`let-id`.

### if

```scheme
(if <bool-expr> (<then-stmt> ...) (<else-stmt> ...))
```

Conditional execution. The condition is a boolean expression. To
condition on a value expression whose boolean-ness is only known at
runtime, wrap it with `bfrom-val`. Both branches are always present
(the else branch may be an empty list `()`).

### foreach

```scheme
(foreach "<label>" <constraint-type> "<susp-var>"
  (<condition> ...)
  (<body-stmt> ...))
```

Labeled loop over the constraint store. Iterates over all **alive**
stored constraints of the given type that satisfy the index conditions.

Each condition is `(<arg-index> <val-expr>)` and requires that the
constraint's argument at the given position is structurally equal to
the value expression (Prolog `==` ask semantics, identical to
`bequal`).

The current constraint suspension is bound to `<susp-var>` on each
iteration. Inside the body, reference it as `(id-var "<susp-var>")` —
the suspension is an id-bound name.

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
(return <val-expr>)
```

Return a value from the current procedure. Procedures always return a
value (never a constraint identifier).

### expr-stmt / bool-expr-stmt

```scheme
(expr-stmt      <val-expr>)
(bool-expr-stmt <bool-expr>)
```

Evaluate an expression for its side effects; discard the result. The
two variants differ only by the kind of expression they wrap. Tell-side
unification (`bunify`) in body position uses `bool-expr-stmt`; ordinary
discarded procedure or host calls use `expr-stmt`.

### store

```scheme
(store <id-expr>)
```

Add a constraint suspension to the constraint store. The argument is a
constraint identifier (typically `(id-var "id")` after a `let-id` from
`create-constraint`). This also **registers the constraint as an
observer** of its arguments for reactivation purposes.

### kill

```scheme
(kill <id-expr>)
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
effect of `bunify`). Each pending suspension is bound to `<susp-var>`
as an id-bound name; the body statements are executed and reference it
via `(id-var "<susp-var>")`. The body typically dispatches to
`reactivate_dispatch`.


## Value Expressions

Expressions in this section evaluate to ordinary values.

### Variable reference

```scheme
(var "<name>")
```

Look up a value-bound variable (parameter or `let-val` / `assign-val`
binding).

### Literals

```scheme
(int <value>)
(float <value>)
(atom "<value>")
(text "<value>")
true
false
wildcard
```

Literals are serialized directly without a `lit` wrapper. `true`,
`false`, and `wildcard` are bare atoms.

### Procedure and host calls

```scheme
(call-expr "<proc-name>" <call-arg> ...)
(host-call "<func-name>" <val-expr> ...)
```

- `call-expr` calls a compiler-generated procedure. Each argument is a
  `<call-arg>` that explicitly tags the kind of value being passed
  (see below).
- `host-call` calls a host language function. Host functions take and
  return values only — arguments are plain value expressions, with no
  wrapper.

### Call arguments

```scheme
(arg-val <val-expr>)
(arg-id  <id-expr>)
```

A `<call-arg>` is one of these two forms. The wrapper is required at
every `call-expr` argument position so the procedure boundary stays
explicit about which arguments are values and which are constraint
identifiers.

### Deep deref-aware evaluation

```scheme
(eval-deep <val-expr>)
```

Switches the nested value expression into deep deref-aware evaluation:
variable references are dereferenced (following binding chains) before
use, and this mode propagates recursively into sub-expressions
(`call-expr` arguments wrapped in `arg-val`, `make-term`, etc.). Used
for the right-hand side of `is`. Constraint identifiers do not deref;
the mode is a no-op for `arg-id` arguments. The bool-position
counterpart is `beval-deep` (see Bool Expressions).

### Logical variables

```scheme
new-var
```

Creates a fresh unbound logical variable. Serialized as a bare atom
(no parentheses).

### Term operations

```scheme
(make-term "<functor>" <val-expr> ...)
(get-arg <val-expr> <index>)
```

- `make-term` constructs a compound term.
- `get-arg` extracts an argument by 0-based index.

The structural-match predicate `bmatch-term` is a bool expression; see
Bool Expressions.

### Suspension field access

```scheme
(field-arg  <id-expr> <i>)
(field-type <id-expr>)
```

- `field-arg` extracts the constraint argument at 0-based index `<i>`.
  Returns a value (the suspension's stored argument).
- `field-type` extracts the constraint type tag. Returns an integer.

There is no separate `field-id` form: a suspension *is* its constraint
identifier in the runtime, so the corresponding extraction is just a
reference to the id-bound name itself (`(id-var "<susp>")`).


## Id Expressions

Expressions in this section evaluate to constraint identifiers.

### Variable reference

```scheme
(id-var "<name>")
```

Look up an id-bound variable (parameter, `let-id` / `assign-id`
binding, or the suspension binder of a `foreach` /
`drain-reactivation-queue`).

### Constraint creation

```scheme
(create-constraint <type> <val-expr> ...)
```

Allocates a new suspension with a fresh unique identifier and
`alive = true`. Does **not** add it to the store; use `store` for
that. The arguments are values that become the constraint's stored
arguments.


## Bool Expressions

Expressions in this section evaluate to booleans. They populate the
condition of `if`, the operand of `bool-expr-stmt`, and the operands
of `bnot` / `band` / `bor`. The serialization uses a `b` prefix on
each constructor to distinguish it from any value-side counterpart.

### Literals

```scheme
btrue
bfalse
```

Boolean literals in bool position. Bare atoms, no parentheses.
Distinct from the value-side `true` / `false` literals.

### Logical operations

```scheme
(bnot <bool-expr>)
(band <bool-expr> <bool-expr>)
(bor  <bool-expr> <bool-expr>)
```

`band` and `bor` are short-circuiting.

### Term match

```scheme
(bmatch-term <val-expr> "<functor>" <arity>)
```

Checks whether the value evaluates to a compound term with the given
functor and arity.

### Equality

```scheme
(bequal    <val-expr> <val-expr>)
(bid-equal <id-expr>  <id-expr>)
```

- **`bequal`** (ask semantics, Prolog `==`): structural equality with
  no mutation. Two distinct unbound variables return `false`. Used in
  guards (guards must not leave half-done bindings on failure).
- **`bid-equal`** compares two constraint identifiers for equality.

### Constraint observation

```scheme
(balive              <id-expr>)
(bis-constraint-type <id-expr> <type>)
```

- `balive` checks the alive flag of a suspension.
- `bis-constraint-type` checks whether a suspension has the given type.

### Propagation history

```scheme
(bnot-in-history <rule-id> <id-expr> ...)
```

Returns `true` if the rule has not previously fired with the given
combination of constraint identifiers. `<rule-id>` is the rule's
integer identifier (see the program's `rule-names` table for the
corresponding source name).

### Unification

```scheme
(bunify <val-expr> <val-expr>)
```

Tell-side unification (Prolog `=`): binds variables, returns boolean.
As a side effect, pushes affected constraints onto the reactivation
queue. Used in rule bodies, typically wrapped in `bool-expr-stmt`
because the result is discarded.

### Value-to-bool bridge

```scheme
(bfrom-val <val-expr>)
```

Promotes a value expression into bool position. The wrapped expression
must evaluate to a boolean value (`VBool`); the runtime checks this and
errors otherwise. Used wherever the compiler cannot statically prove
the operand is a boolean — typically user-defined function calls in
guards, and the early-drop result variable read at the boundary.

### Deep deref-aware evaluation

```scheme
(beval-deep <bool-expr>)
```

Switches the nested boolean expression into deep deref-aware
evaluation. Mirrors `eval-deep` for booleans: any `<val-expr>` and
`<id-expr>` payloads inside the nested expression are evaluated in
deep-deref mode. Used for guard expressions wrapped via `bfrom-val .
eval-deep`.


## Runtime Contract

A backend must implement the following runtime capabilities.

### Logical variables

- Creation of fresh unbound variables (`new-var`).
- Binding via unification (`bunify`) with occurs-check optional.
- Dereferencing (following binding chains) -- handled transparently
  inside `bunify`, `bequal`, and `foreach` lookups.
- Observer lists: when a variable is bound, all constraints observing
  it are pushed onto the reactivation queue.

### Compound terms

- Construction (`make-term`), structural matching (`bmatch-term`),
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
- `bnot-in-history`: membership test.

### Reactivation queue

A queue of constraint suspensions populated by `bunify` when a
variable is bound. Drained by `drain-reactivation-queue`.

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

    ; tell_mymodule__leq2(X_0, X_1): create, store, activate
    (procedure "tell_mymodule__leq2" ("X_0" "X_1")
      (let-id "id" (create-constraint 0 (var "X_0") (var "X_1")))
      (store (id-var "id"))
      (expr-stmt (call-expr "activate_mymodule__leq2"
                   (arg-id (id-var "id")))))

    ; activate_mymodule__leq2(susp): extract args, try each occurrence
    (procedure "activate_mymodule__leq2" ("susp")
      (let-id "id" (id-var "susp"))
      (let-val "X_0" (field-arg (id-var "susp") 0))
      (let-val "X_1" (field-arg (id-var "susp") 1))
      (let-val "d" (call-expr "occurrence_mymodule__leq2_1"
                     (arg-id (id-var "id"))
                     (arg-val (var "X_0"))
                     (arg-val (var "X_1"))))
      (if (bfrom-val (var "d")) ((return true)) ())
      (return false))

    ; occurrence_mymodule__leq2_1:
    ;   reflexivity @ leq(X, X1) <=> X == X1 | true.
    (procedure "occurrence_mymodule__leq2_1" ("id" "X_0" "X_1")
      (if (bequal (var "X_0") (var "X_1"))
        ((kill (id-var "id"))
         (return true))
        ())
      (return false))

    ; reactivate_dispatch(susp): type-based dispatch
    (procedure "reactivate_dispatch" ("susp")
      (if (bis-constraint-type (id-var "susp") 0)
        ((expr-stmt (call-expr "activate_mymodule__leq2"
                      (arg-id (id-var "susp")))))
        ())))

  (exports ((qualified "mymodule" "leq") 2))

  (symbol-table
    ((qualified "mymodule" "leq") 2 0)))
```
