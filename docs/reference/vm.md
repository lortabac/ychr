# YCHR Virtual Machine Specification

For backend implementors (Erlang, Python, Clojure, JavaScript,
Scheme, …): the VM's instruction set, its s-expression serialization,
and the runtime contract a backend must implement.

## Overview

A compiled CHR program is a **VM program**: a list of named procedures,
each with parameters and a body of imperative statements containing
expressions. The VM is the *complete interface* between the compiler
and the runtime — the compiler never emits calls to runtime functions
by name.

Everything the runtime provides (constraint store, unification, term
manipulation) is a dedicated VM instruction; `call-expr` calls a
compiler-generated procedure, `host-call` a host language function
([Procedure and host calls](#procedure-and-host-calls)) and
`apply-closure` a first-class callable the program's callables table
resolves ([Closure application](#closure-application)). Every
expression has one of the three kinds below.

### Expression kinds: values, ids, and bools

The VM has three disjoint kinds of expression:

- **Value expressions** evaluate to ordinary runtime values —
  integers, floats, atoms, strings, booleans, logical variables,
  compound terms — and fill every position that expects a
  unifiable value.
- **Id expressions** evaluate to constraint identifiers (suspension
  references) and fill every position that operates on a stored
  constraint.
- **Bool expressions** evaluate to booleans and fill every boolean
  position: the condition of `if`, the body of `bool-expr-stmt`, the
  operands of `bnot`/`band`/`bor`. The bridge `bfrom-val` promotes a
  value expression whose boolean-ness is only known at runtime (e.g. a
  user-defined function call in a guard), with a runtime shape check;
  every other bool position is statically a boolean.

Constraint identifiers cannot flow into unification or term
construction, and a value expression satisfies a boolean position only
wrapped in `bfrom-val`. The three kinds are physically distinct in the
IR; a backend may still use one runtime representation for an id and
the suspension it refers to (the Haskell and Scheme runtimes do — a
suspension reference *is* its identifier).

Procedures taking a mix of value and id parameters tag each argument
with `arg-val` / `arg-id` at the call boundary (see `call-expr`);
variable references split into `var` (value-bound) and `id-var`
(id-bound). There is no `bool-var`: the only boolean that
compiler-generated code binds to a name is the early-drop result,
bound as a value (`let-val` / `var`) and bridged at the read site with
`bfrom-val`.


## S-Expression Format

VM programs are serialized as s-expressions with kebab-case identifiers.
Every serialized unit opens with a format-version header; see
[Top-Level Structure](#top-level-structure).
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
- **Boolean literals** are bare atoms: `true` / `false` in value
  position, `btrue` / `bfalse` in bool position — two spellings
  because the two positions are distinct expression kinds.
- **Variable-length argument lists** are trailing children of the
  enclosing form, ended by its closing `)`.
- **Fixed-length sub-lists** (then/else branches, foreach conditions
  and body) are wrapped in `(...)`.


## Top-Level Structure

A serialized compilation unit is a `vm-program` containing the VM
format version, the VM program, the exported names, and the symbol
table:

```scheme
(vm-program
  (version <n>)
  <program>
  (exports (<name> <arity>) ...)
  (symbol-table (<name> <arity> <type-id>) ...))
```

- **`<version>`** — the VM format version, a non-negative integer, and
  the first child of `vm-program`; a `version` anywhere else is a
  malformed header. Each YCHR release supports exactly one VM version;
  the compiler always writes it and a reader accepts only it. Version 0
  is reserved for the pre-versioning format — a unit with no `version`
  header at all, anything written before VM version numbers existed;
  an explicit `(version 0)` is rejected as well. Such a unit is
  rejected by any version-aware binary, because only a binary predating
  VM version numbers knows that format. The current version is 1.
- **`<program>`** — the VM program (see below).
- **`exports`** — the CHR identifiers (name + arity) visible to
  external callers; backends should generate a public entry point
  (e.g. a `tell_c` wrapper) for each.
- **`symbol-table`** — the authoritative map from each CHR identifier
  (name + arity) to the 0-based constraint type integer used
  throughout the VM program. Different arities of one name are
  distinct types (`foo/1` and `foo/2`).

### Names

CHR names (in `exports` and `symbol-table`) take two forms:

- **Qualified**: `(qualified "<module>" "<name>")`, e.g.
  `(qualified "order" "leq")`.
- **Unqualified**: a bare string, e.g. `"gcd"`.

In practice every name there is qualified: the renaming pass resolves
every constraint and function to its defining module before
compilation.


## Program

```scheme
(program <num-types>
  (type-names <name> ...)
  <num-rules>
  (rule-names "<rule-name>" ...)
  (evaluables ("<functor>" <arity> "<proc-name>") ...)
  (callables ("<functor>" "<identity>" <arity> "<proc-name>") ...)
  (inert-types <constraint-type> ...)
  <procedure>
  ...)
```

- `<num-types>` — integer, number of distinct constraint types.
- `type-names` — CHR names (see [Names](#names)) indexed by
  constraint type: `type-names[i]` is the source name of type `i`, in
  practice always qualified, e.g. `(qualified "mymodule" "leq")`.
  Used by runtime introspection.
- `<num-rules>` — integer, number of rules in the compilation unit.
- `rule-names` — strings indexed by rule id: `rule-names[i]` is the
  source name of rule `i`, or a synthetic `"__rule_N"` for an
  anonymous rule. Used by runtime introspection.
- `evaluables` — the dispatch table `eval-is` consults (see
  [is evaluation](#is-evaluation)), one entry per user-defined
  function: `<functor>` is the term functor in its runtime encoding
  (module and base name joined by `__`, e.g. `"prelude__+"`),
  `<arity>` the argument count, `<proc-name>` the mangled name of the
  `func_*` procedure. Present even when empty.
- `callables` — the dispatch table `apply-closure` consults (see
  [closure application](#closure-application)), one entry per
  user-defined function and per lifted lambda. `<functor>` is the
  closure term's functor (`"/"` for a function reference, `__closure`
  for a lifted lambda), `<identity>` its first field (a flattened
  function name like `"prelude:double"`, or a lambda identifier),
  `<arity>` the arity the callable was declared at, and `<proc-name>`
  the mangled name of the `func_*` procedure. Present, possibly empty,
  in everything the compiler emits; optional on read (an absent table
  is an empty one), like `inert-types`.
- `inert-types` — constraint types whose activation runs no
  occurrence procedure (no occurrences, or only passive ones).
  Reactivating one can only re-store it, and `store` is idempotent,
  so a runtime may skip registering such suspensions as observers of
  their argument variables (see [Store](#store)) — the trivial
  instance of *Delay Avoidance*. Honoring the entry changes only
  reactivation traffic, never a result, so a backend may ignore it;
  the Scheme backend does. Optional on read within a supported
  version: an absent entry declares no inert type, which changes no
  result. Present, possibly empty, in everything the compiler emits.
  (A dump that predates the entry is version 0 and is rejected by the
  version header before the shape matters.)
- Zero or more procedure definitions follow.

### Procedure

```scheme
(procedure "<name>" ("<param>" ...) <proc-kind>
  <stmt>
  ...)
```

Parameters are positional. Each one's kind (value or constraint id)
is whatever the caller's `call-expr` tags the argument (`arg-val` /
`arg-id`); the body references it with `var` or `id-var` accordingly.

`<proc-kind>` says what the procedure is, so a backend or tool can
classify it without parsing its mangled name:

| Proc-kind | Meaning |
|-----------|---------|
| `(tell <type>)` | Tell procedure for constraint type `<type>`. |
| `(activate <type>)` | Activate procedure for constraint type `<type>`. |
| `(occurrence <type> <occ> <rule-id> "<rule-name>")` | Occurrence procedure: 1-based occurrence number `<occ>` of constraint type `<type>`, belonging to rule `<rule-id>` (the string is the rule's display name). |
| `(reactivate-dispatch)` | The reactivation dispatcher. |
| `(function "<module>" "<name>" <arity>)` | A user-defined function, identified by its unmangled module, base name, and arity. |

The roles of the generated procedures:

| Procedure | Purpose | Parameter kinds |
|-----------|---------|-----------------|
| `tell_c(X_0, ..., X_n)` | Creates a constraint suspension and calls `activate_c`. Storage happens later (Late Storage): inside a fired occurrence that keeps the constraint, or at the end of `activate_c`. | all values |
| `activate_c(susp)` | Extracts arguments from the suspension, tries each occurrence in order. If the constraint survives all occurrences, stores it and returns `false`. | id |
| `occurrence_c_j(id, X_0, ..., X_n)` | Handles the j-th occurrence of constraint c. Iterates over partner constraints, checks guards, fires rules. Returns `true` (early drop) or `false`. | id, then values |
| `reactivate_dispatch(susp)` | Checks the suspension's constraint type and calls the appropriate `activate_c`. | id |
| `func_f(arg_0, ..., arg_n)` | Evaluates a user-defined function. | all values |

There is no dispatcher procedure for a dynamic call: `'$call'` lowers to
`apply-closure`, which resolves the callee through the `callables` table
(see [closure application](#closure-application)).


### Procedure Naming

Procedure names are generated deterministically from the constraint
or function name, module qualifier, and arity, and injectively:
distinct identifiers always produce distinct procedure names. The
renaming pass fully qualifies every constraint and function, so a
procedure name always includes a module component.

**Format:**

```
<prefix>_<module>__<name><arity>
```

`<prefix>` is `tell`, `activate`, `occurrence`, or `func`; `__`
separates module from name; arity is a plain decimal integer with no
separator.

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

`reactivate_dispatch` is unique and not parameterized by constraint
name. Dynamic calls add no procedure name of their own: a `'$call'` is
an `apply-closure`, resolved through the `callables` table.

**Non-ASCII encoding.** A character outside ASCII is encoded as
`%%u<hex>`, `<hex>` being the Unicode code point in lowercase
hexadecimal padded to exactly six digits; there is no closing
delimiter, so the escape is always 9 characters long. A constraint
named `café` gives the component `caf%%u0000e9`. ASCII characters,
punctuation and underscores included, pass through unchanged.

This applies to *term functor* names (`make-term`, `bmatch-term`,
runtime values). Generated procedure names (`tell_*`, `activate_*`,
`func_*`) use `__u<hex>__` instead, because they must be valid
identifiers in the target language and `%` usually is not.

**Restrictions.** Source atom names may not contain the infixes `__`
or `%%u` ([language.md §Lexical syntax](language.md#lexical-syntax));
both are reserved for the mangling above. That reservation, with the
fixed-width escape, is what makes the mangling injective: the only
`__` in a mangled symbol is the module separator, and the only `%%u`
starts a unicode escape.

**Term functor names** (`make-term`, `bmatch-term`) follow the same
encoding and separator rules but carry **no** arity, which those
instructions state explicitly.


## Statements

`let` and `assign` each come in a value variant and a constraint-id
variant. `store`, `kill` and `add-history` take an *id-expression*;
the condition of `if` and the operand of `bool-expr-stmt` take a
*bool-expression*; `return`, `expr-stmt` and `foreach` index
conditions take a *value-expression*.

### let-val / let-id

```scheme
(let-val "<name>" <val-expr>)
(let-id  "<name>" <id-expr>)
```

Bind a local variable; the variants differ only by the kind bound.
Reference the name with `var` after `let-val`, `id-var` after
`let-id`.

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

The condition is a boolean expression; wrap a value expression whose
boolean-ness is only known at runtime in `bfrom-val`. Both branches
are always present (the else branch may be the empty list `()`).

### foreach

```scheme
(foreach "<label>" <constraint-type> "<susp-var>"
  (<condition> ...)
  (<body-stmt> ...))
```

Labeled loop over all **alive** stored constraints of the given type
that satisfy the index conditions.

Each condition `(<arg-index> <val-expr>)` requires the argument at
that position to be structurally equal to the value (Prolog `==` ask
semantics, identical to `bequal`).

Each iteration binds the current suspension to `<susp-var>`, an
id-bound name referenced in the body as `(id-var "<susp-var>")`.

#### Iterator properties

The runtime's iterator must satisfy:

- **Robustness**: iteration resumes where it was suspended even if
  constraints were added or removed meanwhile.
- **Correctness**: only alive constraint suspensions are returned.
- **Completeness**: all constraints that were stored at the moment of
  the iterator's creation are returned at least once.
- **Weak termination**: a contiguous iteration does not contain
  duplicate suspensions.

### continue

```scheme
(continue "<label>")
```

Next iteration of the named `foreach`; used for backjumping when a
partner constraint dies.

### break

```scheme
(break "<label>")
```

Exit the named `foreach` loop.

### return

```scheme
(return <val-expr>)
```

Return from the current procedure. Procedures always return a value,
never a constraint identifier.

### expr-stmt / bool-expr-stmt

```scheme
(expr-stmt      <val-expr>)
(bool-expr-stmt <bool-expr>)
```

Evaluate for side effects and discard the result; the variants differ
only by kind. Tell-side `bunify` in body position uses
`bool-expr-stmt`; discarded procedure or host calls use `expr-stmt`.

### store

```scheme
(store <id-expr>)
```

Add a suspension (typically `(id-var "id")` after a `let-id` from
`create-constraint`) to the constraint store, and **register it as an
observer** of every unbound variable reachable from its arguments,
recursing into compound terms: the `X` in `pair(X, 1)` must be
observed too, or binding it later would silently fail to reactivate
the constraint.

A type listed in the program's `inert-types` is exempt from the
registration: its activation runs no occurrence procedure, so a
reactivation could do nothing.

`store` is **idempotent**: an already-stored suspension is left
untouched. The compiler relies on this — under Late Storage it emits a
reachable `store` for the same suspension both inside fired kept
occurrences and at the end of every activation (re-activations via
`reactivate_dispatch` included), and only the first may append and
register observers. `store` need not follow `create-constraint` at
all: a constraint removed during its own activation is never stored.

### kill

```scheme
(kill <id-expr>)
```

Remove a constraint from the store and mark it not alive.

### add-history

```scheme
(add-history <rule-id> <id-expr> ...)
```

Record that rule `<rule-id>` (its integer identifier; `rule-names`
gives the source name) has fired with this combination of constraint
identifiers, so a propagation rule does not re-fire on it.

### drain-reactivation-queue

```scheme
(drain-reactivation-queue "<susp-var>"
  <body-stmt> ...)
```

Iterate over the constraints pending reactivation (enqueued by
`bunify`), binding each to the id-bound name `<susp-var>` —
`(id-var "<susp-var>")` in the body, which typically dispatches to
`reactivate_dispatch`.

`return`, `break` and `continue` are not permitted in the body: the
drain is neither a labelled loop nor a value-producing position. The
compiler emits only a single dispatch call here, so the restriction is
never felt; a runtime may diagnose a violation as a runtime error.

### push-frame

```scheme
(push-frame <label> <line> <col> <file> <source>)
```

Push a frame onto the call stack used for error stack traces. The
compiler emits one at each occurrence-procedure entry (`rule <name>`,
before the guard) and each function entry
(`function <module:name/arity>`), with the source location and the
pretty-printed source of the fired rule head or matched equation.
There is no pop: the runtime saves the stack at every procedure call
and restores it on return, so frames pushed inside a body are visible
until the enclosing procedure exits. Only the innermost frames are
reported, so a runtime that truncates does so where the stack is
read, not where it is pushed. A backend that ignores `push-frame`
loses stack traces in runtime errors and nothing else.

The five fields are emitted as raw unquoted text — a label or source
fragment containing spaces or parentheses (the common case) does not
survive re-parsing as a single atom. Treat `push-frame` fields as
display-only.


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
```

No `lit` wrapper; `true` and `false` are bare atoms. There is no
wildcard literal: source `_` compiles to `new-var` (one fresh logical
variable per occurrence), because in every position the compiler sees it
in — term and evaluating positions alike — it is an ordinary anonymous
variable. In a rule head, an equation pattern, or a lambda parameter —
all HNF'd pattern positions — `_` never reaches the VM at all; HNF
consumes it.

### Procedure and host calls

```scheme
(call-expr "<proc-name>" <call-arg> ...)
(host-call "<func-name>" <val-expr> ...)
```

- `call-expr` calls a compiler-generated procedure; each argument is
  a kind-tagged `<call-arg>` (below).
- `host-call` calls a host language function, which takes and returns
  values only; arguments are plain value expressions, unwrapped.

### Call arguments

```scheme
(arg-val <val-expr>)
(arg-id  <id-expr>)
```

A `<call-arg>` is one of these two forms. The wrapper is required at
every `call-expr` argument, so the procedure boundary states which
arguments are values and which are constraint identifiers.

### Deep deref-aware evaluation

```scheme
(eval-deep <val-expr>)
```

Evaluates the nested value expression in deep deref-aware mode:
variable references are dereferenced (following binding chains)
before use, recursively through sub-expressions (`arg-val` arguments
of `call-expr`, `make-term`, etc.). Used for the right-hand side of
`is`. Constraint identifiers do not deref, so the mode is a no-op for
`arg-id`. The bool-position counterpart is `beval-deep`.

### is evaluation

```scheme
(eval-is <val-expr>)
```

Evaluate as `eval-deep`, then walk the result and evaluate every
compound subterm whose functor and arity appear in the program's
`evaluables` table (see [Program](#program)), calling the procedure
it maps to. Emitted only for `R is X` with a syntactically variable
right-hand side: the compound is not known until run time, so
dispatch goes through the table instead of a direct `call-expr`.

### Closure application

```scheme
(apply-closure <val-expr> <val-expr> ...)
```

Apply a first-class callable to the arguments that follow it: the
whole of `'$call'(F, A1, …, An)`, and the only form a dynamic call
takes. Evaluate the closure operand, dereference it, and read a key off
its shape:

| Closure | Key `<functor>` `<identity>` `<arity>` |
|---------|----------------------------------------|
| `/(Identity, Arity)` — a function reference `fun name/arity` | `"/"`, the closure's first field (a flattened source name, `module:name`), the arity in its second field |
| `__closure(Identity, SourceForm, Capture …)` — a lifted lambda | `"__closure"`, the closure's first field, the arity it is *applied* at |

The key is looked up in the program's `callables` table (see
[Program](#program)) and the procedure it maps to is called with the
closure's captured values — the fields after `SourceForm` for a lambda,
none for a function reference — followed by the arguments. The functor
is part of the key so an ordinary data term whose first argument
happens to be a function name is not mistaken for a callable.

Two failures, with distinct kinds:

- an *unbound* closure is an insufficient-instantiation error, so a
  rule guard soft-fails and retries the occurrence after reactivation;
- anything else — a non-callable, a function reference applied at an
  arity other than the one it records, or a lambda applied at an arity
  other than the one its source lambda declared — is a general
  `call: no matching closure` error.

The declared-arity check is load-bearing: one identity can name several
functions (`call/2` and `call/3`), so a key of functor and identity
alone would redirect an application of `fun call/2` to `call/3`.

A lambda closure's field count is not itself validated: the captures
are simply the fields after the header, so a malformed `__closure`
term — something no compiler emits — surfaces as an argument-count
mismatch inside the callee rather than as `call: no matching closure`.

### Logical variables

```scheme
new-var
```

A fresh unbound logical variable. A bare atom, no parentheses.

### Term operations

```scheme
(make-term "<functor>" <val-expr> ...)
(get-arg <val-expr> <index>)
```

- `make-term` constructs a compound term.
- `get-arg` extracts an argument by 0-based index.

The structural-match predicate `bmatch-term` is a bool expression.

### Suspension field access

```scheme
(field-arg  <id-expr> <i>)
(field-type <id-expr>)
```

- `field-arg` returns the stored argument at 0-based index `<i>`.
- `field-type` returns the constraint type tag, an integer.

There is no `field-id`: a suspension *is* its constraint identifier in
the runtime, so that extraction is a reference to the id-bound name
itself, `(id-var "<susp>")`.


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

Allocates a suspension with a fresh unique identifier, `alive = true`,
and the given values as its stored arguments. Does **not** add it to
the store; `store` does.


## Bool Expressions

Expressions in this section evaluate to booleans; each constructor
carries a `b` prefix to distinguish it from a value-side counterpart.

### Literals

```scheme
btrue
bfalse
```

Bare atoms, no parentheses; distinct from the value-side `true` /
`false`.

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

Whether the value is a compound term with the given functor and arity.

### Equality

```scheme
(bequal    <val-expr> <val-expr>)
(bid-equal <id-expr>  <id-expr>)
```

- **`bequal`** (ask semantics, Prolog `==`): structural equality, no
  mutation; two distinct unbound variables give `false`. Used in
  guards, which must not leave half-done bindings on failure. Guard
  residuals are mutation-free as a whole — no `bunify`, `store`,
  `kill` or `add-history` is reachable from one — which is also what
  makes `bsoft-guard` sound: a guard abandoned part-way leaves
  nothing to undo.
- **`bid-equal`** compares two constraint identifiers for equality.

### Constraint observation

```scheme
(balive              <id-expr>)
(bis-constraint-type <id-expr> <type>)
```

- `balive`: the suspension's alive flag.
- `bis-constraint-type`: whether the suspension has the given type.

### Propagation history

```scheme
(bnot-in-history <rule-id> <id-expr> ...)
```

`true` if rule `<rule-id>` (its integer identifier; `rule-names` gives
the source name) has not previously fired with this combination of
constraint identifiers.

### Unification

```scheme
(bunify <val-expr> <val-expr>)
```

Tell-side unification (Prolog `=`): binds variables, returns success,
and pushes the affected constraints onto the reactivation queue. Used
in rule bodies, typically under `bool-expr-stmt` since the result is
discarded.

### Value-to-bool bridge

```scheme
(bfrom-val <val-expr>)
```

Promotes a value expression into bool position. It must evaluate to a
boolean value (`VBool`); the runtime checks and errors otherwise. Used
wherever the compiler cannot statically prove the operand boolean —
user-defined function calls in guards, and the early-drop result
variable read at the boundary.

The check must distinguish its two failures, because an enclosing
`bsoft-guard` treats them differently: an operand dereferencing to an
*unbound* variable is an instantiation failure (the guard cannot be
decided yet); a bound non-boolean is a general one. A backend must not
let host truthiness stand in for the check: where an unbound variable
is truthy, that reads an undecidable guard as `true`.

### Deep deref-aware evaluation

```scheme
(beval-deep <bool-expr>)
```

`eval-deep` for booleans: every `<val-expr>` and `<id-expr>` payload
inside the nested expression is evaluated in deep-deref mode. Used for
guard expressions wrapped via `bfrom-val . eval-deep`.

### Soft guard evaluation

```scheme
(bsoft-guard <bool-expr>)
```

Evaluates the nested boolean expression with *instantiation* errors
caught: if an unbound logical variable reaches a point that demands
its value, `bsoft-guard` yields `false` instead of propagating the
error. Runtime errors of any other kind propagate unchanged, as do the
non-local jumps (`break`, `continue`, `return`).

Emitted around the guard residual of a rule occurrence, and only
there. It is the VM-level form of
[soft guard failure](language.md#soft-guard-failure): the rule does
not fire, no diagnostic is produced, and reactivation retries the
occurrence once the missing variable is bound.

Catching is sound under two conditions, both maintained by the
compiler rather than checked by the instruction:

- guard residuals do not tell (see `bequal`): no `bunify`, `store`,
  `kill` or `add-history` is reachable from one, so there is no
  partial store, history or reactivation-queue state to roll back. A
  `host-call` in the guard is outside this guarantee, but its effects
  survive a guard that evaluates to `false` just as they survive an
  abandoned one, so the catch changes nothing there;
- the runtime call stack is restored at the `bsoft-guard` boundary, so
  frames a caught guard pushed do not leak into subsequent execution.
  (A backend that ignores `push-frame` has nothing to do here.)

A residual is wrapped only when it can actually raise — in practice,
when it contains a `bfrom-val`; a pure `bequal` conjunction is emitted
unwrapped.


## Runtime Contract

A backend must implement the following runtime capabilities.

### Logical variables

- Creation (`new-var`); binding by unification (`bunify`), occurs
  check optional.
- Dereferencing (following binding chains), transparently inside
  `bunify`, `bequal`, and `foreach` lookups.
- Observer lists: binding a variable pushes every constraint observing
  it onto the reactivation queue. A runtime may drop dead observers
  there; the drain checks liveness regardless, since a constraint can
  die between being enqueued and being reached.

### Compound terms

- Construction (`make-term`), structural matching (`bmatch-term`),
  argument extraction (`get-arg`); representation is backend-specific
  (tagged arrays, objects, tuples).

### Constraint store

Each suspension contains:

| Field | Description |
|-------|-------------|
| `type` | Constraint type (integer). |
| `id` | Unique constraint identifier. |
| `args` | Array of argument values. |
| `alive` | Boolean flag. |

A simple implementation is a hash map from constraint type to an array
of suspensions; [Iterator properties](#iterator-properties) gives the
requirements on iteration under modification.

### Propagation history

A set of tuples `(rule-id, id_1, ..., id_n)`, `rule-id` being the
integer assigned to the rule at compile time. Must support:

- `add-history`: insert a tuple.
- `bnot-in-history`: membership test.

### Reactivation queue

A queue of suspensions, filled by `bunify` when a variable is bound
and drained by `drain-reactivation-queue`.

### Recursion management

The VM uses plain procedure calls. A backend targeting a language
without tail-call optimization must prevent call-stack overflow
itself, by trampolining or an explicit continuation stack.


## Complete Example

The `leq` (less-than-or-equal) handler with a single `reflexivity`
rule:

```prolog
:- module(mymodule, [leq/2]).
:- chr_constraint leq/2.

reflexivity @ leq(X, X) <=> true.
```

The output of `ychr compile -t vm mymodule.chr`, reindented. The
prelude is always compiled in, so the real dump also has one
`evaluables` entry, one `callables` entry, one `func_*` procedure and
one export per prelude function — elided here (`; ...`). The constraint
is `mymodule:leq/2`, so procedure names follow
`<prefix>_mymodule__leq2`:

```scheme
(vm-program
  (version 1)
  (program 1
    (type-names (qualified "mymodule" "leq"))
    1
    (rule-names "reflexivity")
    (evaluables
      ("prelude__+" 2 "func_prelude____u2b__2")
      ; ... one entry per prelude function elided
      )
    (callables
      ("/" "prelude:+" 2 "func_prelude____u2b__2")
      ; ... one entry per prelude function and lifted lambda elided
      )
    (inert-types)

    ; tell_mymodule__leq2(X_0, X_1): create, store, activate
    (procedure "tell_mymodule__leq2" ("X_0" "X_1") (tell 0)
      (let-id "active" (create-constraint 0 (var "X_0") (var "X_1")))
      (store (id-var "active"))
      (expr-stmt (call-expr "activate_mymodule__leq2"
                   (arg-id (id-var "active")))))

    ; activate_mymodule__leq2(active): extract args, try each occurrence
    (procedure "activate_mymodule__leq2" ("active") (activate 0)
      (let-val "X_0" (field-arg (id-var "active") 0))
      (let-val "X_1" (field-arg (id-var "active") 1))
      (let-val "dropped" (call-expr "occurrence_mymodule__leq2_1"
                           (arg-id (id-var "active"))
                           (arg-val (var "X_0"))
                           (arg-val (var "X_1"))))
      (if (bfrom-val (var "dropped")) ((return true)) ())
      (return false))

    ; occurrence_mymodule__leq2_1: after HNF,
    ;   reflexivity @ leq(X, X1) <=> X == X1 | true.
    (procedure "occurrence_mymodule__leq2_1" ("active" "X_0" "X_1")
               (occurrence 0 1 0 "reflexivity")
      (push-frame rule reflexivity 4 15 mymodule.chr leq(X, X))
      (if (bequal (var "X_0") (var "X_1"))
        ((kill (id-var "active"))
         (return true))
        ())
      (return false))

    ; ... prelude func_* procedures elided

    ; reactivate_dispatch(susp): type-based dispatch
    (procedure "reactivate_dispatch" ("susp") (reactivate-dispatch)
      (if (bis-constraint-type (id-var "susp") 0)
        ((expr-stmt (call-expr "activate_mymodule__leq2"
                      (arg-id (id-var "susp")))))
        ()))
    )

  (exports
    ((qualified "mymodule" "leq") 2)
    ; ... prelude exports elided
    )

  (symbol-table
    ((qualified "mymodule" "leq") 2 0)))
```
