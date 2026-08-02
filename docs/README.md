# YCHR Documentation

The documentation is organized into four categories, following the
[Diátaxis](https://diataxis.fr/) framework:

- **Tutorials** — learning-oriented, step-by-step.
- **How-to guides** — task-oriented, "how do I X?"
- **Reference** — information-oriented, dry facts.
- **Explanation** — understanding-oriented, conceptual.

The tutorials and the reference section are complete. A few how-to guides
(the REPL, adding types, organizing modules) and two explanation pages
(design rationale, operational semantics) are still outlines; they lay out
the structure and are being filled in incrementally.

Runnable, self-contained programs that the docs reference live under
[`../examples/`](../examples/) at the repo root. Every REPL transcript
is copied verbatim from a real run; the authoring conventions are in
[`dev-docs/DOC_CONVENTIONS.md`](../dev-docs/DOC_CONVENTIONS.md).

## Reading paths

**New to constraint programming?**

1. [Getting started](tutorials/01-getting-started.md) — install and run.
2. [CHR primer](tutorials/02-chr-primer.md) — what CHR is and how a rule fires.
3. [Your first program](tutorials/03-your-first-program.md) — guided walkthrough.
4. [Functions, types, and lambdas](tutorials/04-functions-and-types.md).

**Already know CHR or Prolog?**

1. [Getting started](tutorials/01-getting-started.md) — quick install check.
2. [Your first program](tutorials/03-your-first-program.md) — skim for the YCHR specifics.
3. [Language reference](reference/language.md) — the ways YCHR diverges from
   K.U.Leuven CHR-in-Prolog.
4. [Prelude reference](reference/prelude.md) and [CLI](reference/cli.md) for daily use.

**Embedding YCHR in a Haskell program?**

1. [Embed a CHR module](how-to/embed-a-chr-module.md) — the worked
   end-to-end example.
2. [Value conversion](reference/convert.md) — `ToTerm` / `FromTerm` and
   the typed query wrappers.
3. [Host functions](reference/host-functions.md) — calling your Haskell
   code from CHR.
4. [Haskell DSL](reference/dsl.md) — building programs as Haskell values
   instead of parsing `.chr` source.

**Implementing a backend?**

1. [VM specification](reference/vm.md) — instruction set, s-expression
   format, runtime contract.
2. [Operational semantics](explanation/operational-semantics.md) — the
   firing order the runtime must respect.
3. Contributor docs: [`dev-docs/PROJECT.md`](../dev-docs/PROJECT.md).

## Tutorials

- [01 — Getting started](tutorials/01-getting-started.md)
- [02 — A CHR primer](tutorials/02-chr-primer.md)
- [03 — Your first YCHR program](tutorials/03-your-first-program.md)
- [04 — Functions, types, and lambdas](tutorials/04-functions-and-types.md)

## How-to guides

- [Use the REPL](how-to/use-the-repl.md)
- [Add types to a program](how-to/add-types.md)
- [Call host-language functions](how-to/call-host-functions.md)
- [Organize a program into modules](how-to/organize-modules.md)
- [Embed a CHR module in Haskell](how-to/embed-a-chr-module.md)
- [Drive a compiled program from the Scheme REPL](how-to/scheme-repl.md)

## Reference

- [Language](reference/language.md) — feature-level reference
- [Syntax](reference/syntax.md) — lexical and grammatical rules
- [Haskell DSL](reference/dsl.md) — embedded `YCHR.DSL` for library use
- [Haskell conversion](reference/convert.md) — `ToTerm` / `FromTerm` and
  the typed query wrappers for embedding
- [Host functions](reference/host-functions.md) — registering custom
  `host:_` functions from Haskell
- [Type system](reference/type-system.md) — gradual type-system spec
- [Prelude / standard library](reference/prelude.md)
- [CLI](reference/cli.md) — `ychr` command
- [REPL](reference/repl.md) — meta-commands and live sessions
- [Errors](reference/errors.md) — `YCHR-NNNNN` code catalogue
- [Abstract VM](reference/vm.md) — instruction set and runtime contract

## Explanation

- [What is CHR?](explanation/what-is-chr.md)
- [The refined operational semantics](explanation/operational-semantics.md)
- [Design rationale](explanation/design-rationale.md)

## Project status

- [Roadmap](roadmap.md)
