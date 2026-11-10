# Scheme libraries for `chr_type`s

`ychr scheme-types` reads one module and writes an R6RS library with a
constructor, a predicate and accessors for each of its `:- chr_type`s.
Scheme code uses it to build and read CHR values without knowing how
the runtime stores them. It can also write a schema: one s-expression
that describes the same types, for tools outside YCHR.

The library imports only `(rnrs)` and `(ychr var)`, so it loads without
the compiled program.

## Usage

```
ychr scheme-types FILES... [-m MODULE] [-d DIR] [--library "(NAME ...)"]
                  [--schema] [--all] [--checked]
                  [--no-check] [--Werror] [--dump-splices]
```

| Flag | Meaning |
|---|---|
| `-m`, `--module` | The module to generate for. Not needed when `FILES` declare one module. |
| `-d`, `--output-dir` | Output directory (default `.`). |
| `--library` | The library name. Default `(ychr types MODULE)`. The file goes to `DIR/` plus the name's parts, so `(ychr types points)` is `DIR/ychr/types/points.sls`. |
| `--schema` | Also write the schema, next to the library, as `….schema.scm`. |
| `--all` | Every type the module declares, with every constructor. By default only exported types are included, with the constructors the export list shows (`type(T/N)` or `type(T/N, [C, …])`). |
| `--checked` | Accessors check the constructor (see [Accessors](#accessors)). |

`--no-check`, `--Werror` and `--dump-splices` work as for `ychr
compile`. The prelude is refused: its `bool` and `list` are native
Scheme values (`#t`, pairs, `'()`), not records.

## Example

`points.chr`:

```prolog
:- module(points, [type(point/2), type(shape/0), area/2]).

:- chr_type point(X, Y) ---> point(x :: X, y :: Y).
:- chr_type shape ---> circle(r :: float) ; rect(float, float) ; empty.

:- chr_constraint area/2.

area(circle(R), A) <=> A is 3.0 * R * R.
area(rect(W, H), A) <=> A is W * H.
area(empty, A) <=> A = 0.0.
```

```
$ ychr scheme-types --schema -d out points.chr
out/ychr/types/points.sls
out/ychr/types/points.schema.scm
```

(The note about the runtime that follows on stderr is left out.)

With the program compiled by `ychr compile -t scheme -n points -d out
points.chr`, this script

```scheme
(import (rnrs) (ychr) (ychr generated points) (ychr types points))
(define s (open-session points))
(define p (point-with-x (make-point 1 2) 10))
(display (list (point? p) (point-x p) (point-y p))) (newline)
(define a (make-var s))
(points:area/2 s (make-rect 2.0 3.0) a)
(display (deref a)) (newline)
(display (shape? empty)) (newline)
```

prints, under Chez Scheme (`scheme --libdirs scheme:out --libexts .sls
--program use.sps`):

```
(#t 10 2)
6.0
#t
```

## Generated definitions

For a constructor `C` of type `T`:

| Definition | Meaning |
|---|---|
| `(make-C a …)` | Builds the term. |
| `(C? v)` | `v` dereferences to a `C` term. |
| `(C-L t)` | The argument labelled `L`. |
| `(C-i t)` | Argument `i` (from 1) of a constructor without labels. |
| `(C-with-L t v)` | A copy of `t` with label `L` set to `v`, like `set_field`. Labelled arguments only. |
| `C` | A nullary constructor: the atom itself. With `C?`, no other definitions. |
| `(T? v)` | `v` is a term of any constructor of `T`, exported or not. |

When a type has one constructor with the type's own name, `T?` and
`C?` are one procedure, defined once. An opaque type and a built-in type
get no definitions.

Names come from the source names, never from the runtime's mangled
functors. A character that is not allowed in an identifier is escaped
the same way the backend escapes constraint aliases.

**Collisions are errors** (YCHR-50006): two definitions with one name,
for example the same constructor name in two types, or a type `t` with a
constructor `t` and another constructor (both want `t?`). The generator
never renames.

The library itself imports `(rnrs)` and `(ychr var)` with a prefix, so
any name is fine inside it. Your code may not be: common constructors
give names that `(rnrs)` or `(ychr)` also export, such as `error?` and
`make-error` for `error(E)`, `null?`, `pair?`, `var?` or `term?`. Chez
refuses such an import. Import the generated library with `(prefix …)`,
or leave the clashing names out with `(except …)`. The same goes for
several generated libraries used together.

YCHR-50007 means `-m` names no loaded module or the prelude, or no
`-m` was given and `FILES` declare no module or several.

## Accessors

- **Dereferenced.** An accessor dereferences the term and the
  argument, so it never returns a bound variable. An unbound one is
  returned as is.
- **Shallow.** An argument that is a list or a compound may still hold
  variables deeper down. Call the runtime's `deep-deref` once on
  structures that come from CHR.
- **Fast.** Each accessor reads its field directly; there is no
  dispatch on the arity.
- **Unchecked by default.** An accessor applied to another constructor
  is an error from the record system when the arity differs, and a wrong
  field otherwise. With `--checked`, every accessor tests `C?` first and
  raises an `assertion-violation` naming the accessor and the value.
- Constructors do not check argument types, and type parameters change
  nothing in the code. Lists are native Scheme lists.

## Schema

```scheme
(ychr-schema 1
  (module points)
  (library (ychr types points))
  (type point (X Y)
    (constructor point points__point (field x X) (field y Y)))
  (type shape ()
    (constructor circle points__circle (field r float))
    (constructor rect points__rect (field #f float) (field #f float))
    (constructor empty points__empty)))
```

- `1` is the format version.
- `(type NAME (PARAMS …) CONSTRUCTOR …)`, or `(type NAME (PARAMS …)
  opaque)`. Only the generated constructors are listed.
- `(constructor NAME FUNCTOR FIELD …)`: the source name, then the symbol
  the runtime uses as the term's functor.
- `(field LABEL TYPE)`: the label is `#f` for an unlabelled argument.
- Types use YCHR's syntax as s-expressions: a type variable is its
  name, an application is a list (`(list A)`). Built-in and prelude
  types are bare; other types are qualified (`pairs:pair`).
- A name that is not a valid identifier is written as a string.

## Serialization

The runtime's term records are nongenerative, so on Chez a ground term
written with `fasl-write` reads back in another process, and the
generated predicates and accessors accept it. Serialize ground terms
only (call `deep-deref` first): a variable has no meaning outside its
session.
