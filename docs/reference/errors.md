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

## See also

- [Language reference](language.md).
- [Type-system reference](type-system.md).
