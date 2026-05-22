# `ychr` Command-Line Reference

> **Audience:** anyone running YCHR from the shell.
> **You will:** find the exact form, options, and examples for every
> `ychr` subcommand.

For a guided walk-through, see
[tutorials/01-getting-started.md](../tutorials/01-getting-started.md).

## Synopsis

```
ychr [SUBCOMMAND] [OPTIONS] [FILES...]
```

If no subcommand is given, `ychr` starts the REPL — equivalent to
`ychr repl`. The top-level `--help` lists the available subcommands:

```sh
ychr --help
```

## Subcommands

### `ychr repl [--quiet] [--Werror] [FILES...]`

Start the interactive REPL on the given files.

| Option | Description |
|--------|-------------|
| `--quiet` | Suppress the prompt and warnings. Useful for scripted input. |
| `--Werror` | Treat warnings as errors. Warnings during the initial load abort startup; warnings during `:recompile` keep the previously loaded program; query-rename warnings (one-shot or live-session queries) abort the query without disturbing the constraint store. Warnings are still printed to stderr under `--Werror` even when `--quiet` is set, so the failure is never silent. |

Example:

```sh
ychr repl examples/bakery.chr
```

See [REPL reference](repl.md) for meta-commands and live sessions.

### `ychr run -g GOAL [--show-bindings] [--Werror] [FILES...]`

Compile the given files and execute a single goal non-interactively.

| Option | Description |
|--------|-------------|
| `-g GOAL` | The goal to execute. **Must be a single declared constraint** — an atom or compound whose name and arity match a `:- chr_constraint` declaration in scope (e.g. `cake`, `compute(5, R)`, `bakery:egg`). Bare expressions (`true`, `1 + 1`), evaluation forms (`X is E`, `X = E`), conjunctions (`a, b`), and function calls (`factorial(5)`) are rejected with `YCHR-20013`. The REPL is broader on purpose; use it (or wrap them in a helper constraint) for those forms. |
| `--show-bindings` | Print the resulting variable bindings (one binding per line, sorted alphabetically). |
| `--Werror` | Treat warnings as errors. Exits non-zero before the goal runs if any warnings were produced. |

Example:

```sh
ychr run -g 'cake' examples/bakery.chr
```

`run` exits silently on success. To execute expression goals,
conjunctions, or function calls non-interactively, wrap them in a
single helper constraint whose body posts them; otherwise use the
REPL (one-shot or `:begin ... :end` live session).

### `ychr check [--Werror] [FILES...]`

Type-check the program. Exits non-zero on type errors. No output on
success.

| Option | Description |
|--------|-------------|
| `--Werror` | Treat warnings as errors. Exits non-zero before type-checking if any warnings were produced. |

```sh
ychr check examples/bakery.chr
```

### `ychr compile [-d DIR] [-n NAME] [-t TARGET] [--Werror] [FILES...]`

Compile the program to a target representation.

| Option | Description |
|--------|-------------|
| `-d`, `--output-dir DIR` | Output directory (default: current directory). |
| `-n`, `--base-name NAME` | Base name for the generated files (default: `program`). |
| `-t TARGET` | `vm` (s-expression VM dump, default) or `scheme`. |
| `--Werror` | Treat warnings as errors. Exits non-zero without writing the output file if any warnings were produced. |

Examples:

```sh
ychr compile -t vm examples/bakery.chr           # → ./program.vm
ychr compile -t scheme -d build/ examples/bakery.chr
```

The Scheme target writes a Scheme library file under
`<output-dir>/ychr/generated/<name>.sls`.

### `ychr gen-driver -g GOAL [--Werror] [FILES...]`

Generate a Scheme driver script that runs the given goal against a
program already compiled with `ychr compile -t scheme`. Output is
written to standard output. Pair it with `ychr compile -t scheme` and
run the driver under Guile.

| Option | Description |
|--------|-------------|
| `-g GOAL` | The goal to bake into the driver. |
| `--Werror` | Treat warnings as errors. Applies to both file-level warnings (during compilation) and warnings produced while renaming the goal's arguments. Exits non-zero without writing the driver if any warnings were produced. |

```sh
ychr compile -t scheme -d build/ examples/bakery.chr
ychr gen-driver -g 'cake' examples/bakery.chr > build/run.scm
```

For interactive use against a compiled program, see
[`docs/how-to/scheme-repl.md`](../how-to/scheme-repl.md).

## Files

- REPL line history: `$XDG_DATA_HOME/ychr/history` (typically
  `~/.local/share/ychr/history`).

## See also

- [REPL reference](repl.md).
- [How-to: use the REPL](../how-to/use-the-repl.md).
