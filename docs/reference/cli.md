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

### `ychr repl [--quiet] [FILES...]`

Start the interactive REPL on the given files.

| Option | Description |
|--------|-------------|
| `--quiet` | Suppress the prompt and warnings. Useful for scripted input. |

Example:

```sh
ychr repl examples/bakery.chr
```

See [REPL reference](repl.md) for meta-commands and live sessions.

### `ychr run -g GOAL [--show-bindings] [FILES...]`

Compile the given files and execute a single goal non-interactively.

| Option | Description |
|--------|-------------|
| `-g GOAL` | The goal to execute. **Only one goal** per invocation — conjunctions like `a, b` are not accepted at this level. |
| `--show-bindings` | Print the resulting variable bindings (one binding per line, sorted alphabetically). |

Example:

```sh
ychr run -g 'cake' examples/bakery.chr
```

`run` exits silently on success. To compose multiple goals, use the
REPL with a live session, or wrap them in a single helper constraint
that posts the others as its body.

### `ychr check [FILES...]`

Type-check the program. Exits non-zero on type errors. No output on
success.

```sh
ychr check examples/bakery.chr
```

### `ychr compile [-d DIR] [-n NAME] [-t TARGET] [FILES...]`

Compile the program to a target representation.

| Option | Description |
|--------|-------------|
| `-d`, `--output-dir DIR` | Output directory (default: current directory). |
| `-n`, `--base-name NAME` | Base name for the generated files (default: `program`). |
| `-t TARGET` | `vm` (s-expression VM dump, default) or `scheme`. |

Examples:

```sh
ychr compile -t vm examples/bakery.chr           # → ./program.vm
ychr compile -t scheme -d build/ examples/bakery.chr
```

The Scheme target writes a Scheme library file under
`<output-dir>/ychr/generated/<name>.sls`.

### `ychr gen-driver -g GOAL [FILES...]`

Generate a Scheme driver script that runs the given goal against a
program already compiled with `ychr compile -t scheme`. Output is
written to standard output. Pair it with `ychr compile -t scheme` and
run the driver under Guile.

```sh
ychr compile -t scheme -d build/ examples/bakery.chr
ychr gen-driver -g 'cake' examples/bakery.chr > build/run.scm
```

## Files

- REPL line history: `$XDG_DATA_HOME/ychr/history` (typically
  `~/.local/share/ychr/history`).

## See also

- [REPL reference](repl.md).
- [How-to: use the REPL](../how-to/use-the-repl.md).
