# Scheme libraries for `chr_type`s

`ychr scheme-types` reads one module and writes an R6RS library with a
constructor, a predicate and accessors for each of its `:- chr_type`s.
Scheme code uses it to build and read CHR values without knowing how
the runtime stores them. It can also write a schema: one s-expression
that describes the same types, for tools outside YCHR.

The library imports only `(rnrs)` and `(ychr var)`, so it loads without
the compiled program.

There are two variants. The default one dereferences, so it works on
terms straight from a CHR session. The ground one (`--ground`) does not,
so it is faster but only takes ground terms. See [Ground
libraries](#ground-libraries).

## Usage

```
ychr scheme-types FILES... [-m MODULE] [-d DIR] [--library "(NAME ...)"]
                  [--schema] [--all] [--checked] [--ground]
                  [--no-check] [--Werror] [--dump-splices]
```

| Flag | Meaning |
|---|---|
| `-m`, `--module` | The module to generate for. Not needed when `FILES` declare one module. |
| `-d`, `--output-dir` | Output directory (default `.`). |
| `--library` | The library name. Default `(ychr types MODULE)`, or `(ychr ground-types MODULE)` with `--ground`. The file goes to `DIR/` plus the name's parts, so `(ychr types points)` is `DIR/ychr/types/points.sls`. |
| `--schema` | Also write the schema, next to the library, as `….schema.scm`. |
| `--all` | Every type the module declares, with every constructor. By default only exported types are included, with the constructors the export list shows (`type(T/N)` or `type(T/N, [C, …])`). |
| `--checked` | Accessors check the constructor (see [Accessors](#accessors)). With `--ground`, everything also checks for variables. |
| `--ground` | The ground variant: no dereferencing (see [Ground libraries](#ground-libraries)). |

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
(display (shape-type? empty)) (newline)
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
| `(C? v)` | `v` dereferences to a `C` term (ground variant: `v` is a `C` term). |
| `(C-L t)` | The argument labelled `L`. |
| `(C-i t)` | Argument `i` (from 1) of a constructor without labels. |
| `(C-with-L t v)` | A copy of `t` with label `L` set to `v`, like `set_field`. Labelled arguments only. |
| `C` | A nullary constructor: the atom itself. With `C?`, no other definitions. |
| `(T-type? v)` | `v` is a term of any constructor of `T`, exported or not. |

The type predicate has its own suffix so it never clashes with a
constructor predicate: in `:- chr_type t ---> t(int) ; u.`, `t?` tests
for the constructor `t` and `t-type?` for the type. An opaque type and a
built-in type get no definitions.

Names come from the source names, never from the runtime's mangled
functors. A character that is not allowed in an identifier is escaped
the same way the backend escapes constraint aliases.

**Collisions are errors** (YCHR-50006): two definitions with one name,
for example the same constructor name in two types. The generator never
renames.

The library itself imports `(rnrs)` and `(ychr var)` with a prefix, so
any name is fine inside it. Your code may not be: common constructors
give names that `(rnrs)` or `(ychr)` also export, such as `error?` and
`make-error` for `error(E)`, `null?`, `pair?`, `var?`, `term?` or
`ground?`. Chez
refuses such an import. Import the generated library with `(prefix …)`,
or leave the clashing names out with `(except …)`. The same goes for
several generated libraries used together.

YCHR-50007 means `-m` names no loaded module or the prelude, or no
`-m` was given and `FILES` declare no module or several.

## Accessors

- **Dereferenced** (default variant only). An accessor dereferences the
  term and the argument, so it never returns a bound variable. An
  unbound one is returned as is. The ground variant dereferences
  nothing.
- **Shallow** (both). An argument that is a list or a compound may
  still hold variables deeper down. Call the runtime's `deep-deref` once
  on structures that come from CHR.
- **Fast** (both). Each accessor reads its field directly; there is no
  dispatch on the arity. The ground variant reads one field and nothing
  else.
- **Unchecked by default** (both). An accessor applied to another
  constructor is an error from the record system when the arity
  differs, and a wrong field otherwise. With `--checked`, every accessor
  tests `C?` first and raises an `assertion-violation` naming the
  accessor and the value. The ground variant with `--checked` also
  checks for variables (see below).
- Constructors do not check argument types, and type parameters change
  nothing in the code. Lists are native Scheme lists.

## Ground libraries

`--ground` writes a library with the same exported names and the same
meaning, minus the `deref`s: a predicate tests `v` itself, an accessor
reads the field and returns it, an update copies `t` itself. Terms are
the same flat compounds, so a term built with one variant is fine for
the other, for CHR and for `fasl-write`. To switch, change the import.

Use it when your Scheme code only sees ground terms: terms it built
itself, terms read with `fasl-read`, or terms from CHR after
`deep-deref`. Reading a tree is then several times faster (the `size/*`
and `rewrite/*` cases of `make bench-scheme-chez` compare it with the
default variant and with native records).

**Contract.** Every term you pass is ground where the procedure reads
it: the term is not a variable, and neither is the field an accessor
returns. A *bound* variable counts as a variable here, since nothing
dereferences it. If you break the contract, you get what any wrong
argument to an unchecked accessor gives: a predicate answers `#f` for a
variable, and an accessor fails in the record system or returns the
variable.

**Checked.** With `--ground --checked`, on top of the `C?` test of
`--checked`:

- a predicate, an accessor or an update given a variable raises an
  `assertion-violation` naming the procedure and the value;
- an accessor whose field is a variable raises the same, naming the
  accessor and the term.

The checks are shallow, like the accessors. To check a whole term, use
`ground?`.

**`(ground? t)`**, from `(ychr var)` (also exported by `(ychr runtime)`
and `(ychr)`): `#t` if no variable occurs in `t`, bound or unbound.
Pairs and compounds are walked; any other value is ground. It does not
dereference, so a term fresh from CHR is usually not ground until you
call `deep-deref`. Call it in debug builds on terms that cross from CHR
into code that uses a ground library.

With the program of the example above:

```scheme
(import (rnrs) (ychr) (ychr generated points) (ychr ground-types points))
(define s (open-session points))
(define a (make-var s))
(points:area/2 s (make-rect 2.0 3.0) a)
(display (list (ground? a) (ground? (deep-deref a)) (deep-deref a))) (newline)
(define p (make-point 1 (make-circle 2.0)))
(display (list (ground? p) (point-x p) (circle-r (point-y p)))) (newline)
```

prints, under Chez Scheme:

```
(#f #t 6.0)
(#t 1 2.0)
```

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
generated predicates and accessors of both variants accept it. Serialize ground terms
only (call `deep-deref` first): a variable has no meaning outside its
session.
