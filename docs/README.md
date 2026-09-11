# YCHR Documentation

Runnable programs the docs refer to live in [`examples/`](../examples/).
Conventions for these pages: [`dev-docs/DOC_CONVENTIONS.md`](../dev-docs/DOC_CONVENTIONS.md).

## Tutorials

- [Getting started](tutorials/01-getting-started.md) — install, run a program.
- [CHR primer](tutorials/02-chr-primer.md) — what a rule is and when it fires.
- [Your first program](tutorials/03-your-first-program.md)
- [Functions, types, and lambdas](tutorials/04-functions-and-types.md)

## How-to

- [Call host-language functions](how-to/call-host-functions.md)
- [Embed a CHR module in Haskell](how-to/embed-a-chr-module.md)
- [Drive a compiled program from the Scheme REPL](how-to/scheme-repl.md)

## Reference

- [Language](reference/language.md) — syntax, modules, functions, evaluation, host calls.
- [Type system](reference/type-system.md)
- [Search](reference/search.md) — `library(search)`
- [REPL](reference/repl.md)
- [Haskell DSL](reference/dsl.md)
- [Haskell conversion](reference/convert.md) — `ToTerm`/`FromTerm`, typed queries, host functions.
- [Abstract VM](reference/vm.md) — for backend implementors.
- Standard library: [`libraries/`](../libraries/). The prelude is always
  imported; the others need `:- use_module(library(name))`.
- CLI: `ychr --help`.
- Error codes: `src/YCHR/Internal/Display.hs` maps every `YCHR-NNNNN` to
  its message. Warnings carry `2x1xx` codes; `--Werror` promotes them.

## Explanation

- [What is CHR?](explanation/what-is-chr.md)

## Status

- [Roadmap](roadmap.md)
