# Error Code Reference

> **Audience:** users hitting a `YCHR-NNNNN` diagnostic and looking up
> what it means.

This page is a stub.

YCHR diagnostics carry a numeric code of the form `YCHR-NNNNN`. The codes
are stable across releases; user-facing messages may evolve.

## Code ranges (planned layout)

> **TODO:** confirm and document the actual numbering scheme used in the
> source. As a starting point:
>
> - `10000–19999` — parser
> - `20000–29999` — name resolution / module system
> - `30000–39999` — desugaring
> - `40000–49999` — type checker
> - `50000–59999` — runtime

## Catalog

> **TODO:** list each code, its category, the user-facing message, and a
> short note on how to fix the underlying issue.
>
> The source of truth lives in the modules that emit them; until this
> page is filled in, search the source for `YCHR-` to find the
> definitions.

| Code | Phase | Meaning |
|------|-------|---------|
| `YCHR-20008` | Rename | A `type(t/n, [c, ...])` export or import entry names a constructor that the type does not declare. Fix the typo, add the constructor to the type, or remove it from the list. |
| `YCHR-20010` | Rename | A qualified reference like `palette:green` names a data constructor that is declared on the type but excluded by the exporting module's allowlist. Add the constructor to the exporter's `type(t/n, [...])` list, or use a different one. |
| `YCHR-20011` | Rename | A `use_module(palette, [type(col/0, [green])])` import lists a constructor that is declared on the type but excluded by the exporting module's allowlist. Same underlying condition as `YCHR-20010` but observed at the import site rather than at a use site. |
| `YCHR-20012` | Rename | An unqualified data-constructor reference is exported by more than one imported module. Qualify the constructor (`mod:ctor`) to disambiguate, or narrow the import list. Parallel to `YCHR-20001` for functions/constraints; data constructors are not arity-overloadable, so the error names only the constructor and the modules that export it. |

## See also

- [Language reference](language.md).
- [Type-system reference](type-system.md).
