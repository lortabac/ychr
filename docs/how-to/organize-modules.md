# How to organize a program into modules

> **Goal:** split a YCHR program across multiple files and control what
> each module exports.

This page is a stub.

## Declare a module

```prolog
:- module(order, [leq/2]).
:- chr_constraint leq/2.
```

## Import another module

```prolog
:- use_module(library(lists)).
```

## Export forms

Each entry in the export list is one of:

| Form | Meaning |
|------|---------|
| `name/arity` | Export the constraint `name/arity`. |
| `fun(name/arity)` | Export the function `name/arity`. |
| `op(Pri, Type, Name)` | Export the operator declaration. |
| `type(name/arity)` | Export the type and all of its data constructors. |
| `type(name/arity, [c1, ...])` | Export the type and only the listed constructors. Pass `[]` to expose the type without any constructors. |

The constructor allowlist is also accepted on the import side, where it
intersects with the exporter's allowlist:

```prolog
:- use_module(palette, [type(col/0, [red])]).
```

If a constructor named in either list is not actually a constructor of
the type (or, on the import side, is not in the source module's
allowlist), the renamer rejects the program with `YCHR-20008`.

## Restricted imports

> **TODO:** `use_module(M, [name/arity, ...])` to import only specific
> identifiers. Cross-link to relevant golden tests if useful.

## Qualified vs unqualified references

> **TODO:** when names need to be qualified (`module:name`) and when the
> renamer resolves them automatically.

## Library search path

> **TODO:** what `library(lists)` resolves to and how to extend the
> search path.

## See also

- [Language reference: modules](../reference/language.md#modules).
