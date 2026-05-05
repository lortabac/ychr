# YCHR Documentation

The documentation is organized into four categories, following the
[Diátaxis](https://diataxis.fr/) framework:

- **Tutorials** — learning-oriented, step-by-step.
- **How-to guides** — task-oriented, "how do I X?"
- **Reference** — information-oriented, dry facts.
- **Explanation** — understanding-oriented, conceptual.

Many pages are currently stubs. They lay out the structure; content will
be filled in incrementally.

## Conventions

### Audience banner
Each page opens with an **Audience** / **You will** callout so readers
can self-route. Pages may add a **Skip if** line for readers who can
move on to a more advanced page.

### REPL transcripts
Interactive sessions are shown in code fences with the info-string
`ychr-repl`. The REPL uses two prompts:

- `ychr> ` — normal mode.
- `ychr live> ` — inside a `:begin … :end` live session, where the
  constraint store persists between inputs.

Both prompts appear in transcripts. Every output line is copied
verbatim from a real REPL run; nothing is paraphrased or guessed.

```
ychr> :begin
ychr live> egg.
ychr live> egg.
ychr live> print_store.
'bakery:egg'()
'bakery:egg'()
ychr live> :end
ychr>
```

A test harness that executes these fences will land later. Until then,
the convention is the contract.

### Examples
Runnable, self-contained programs that the docs reference live under
[`../examples/`](../examples/) at the repo root. They are pedagogical,
not regression tests — for edge cases see `test/golden/`.

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

## Reference

- [Language](reference/language.md) — feature-level reference
- [Syntax](reference/syntax.md) — lexical and grammatical rules
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
