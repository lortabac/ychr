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

> **TODO:** document the supported export forms — `name/arity`,
> `fun name/arity`, `op(/3)`, `type(name/arity)` — and what each makes
> visible to importers.

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
