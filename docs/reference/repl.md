# REPL Reference

> **Audience:** anyone using `ychr repl`.
> **You will:** find the REPL prompts, meta-commands, and the
> difference between one-shot queries and live sessions.

For a guided walk-through, see
[how-to/use-the-repl.md](../how-to/use-the-repl.md).

## Starting the REPL

```sh
ychr repl [--quiet] [FILES...]
```

The REPL loads the given files (or none, falling back to the bundled
prelude alone), prints any warnings and type-check messages, and
presents the `ychr> ` prompt. The full standard library is auto-loaded;
no `:- use_module(library(...))` is needed for prelude or meta
identifiers.

The `--quiet` flag suppresses the prompt and warnings — useful when
piping input from a script or test harness.

## Prompts

| Prompt | Mode |
|--------|------|
| `ychr> ` | Normal mode. Each query runs against a fresh, empty store. |
| `ychr live> ` | Live session (between `:begin` and `:end`). Queries share a persistent store. |

## Tab completion

Tab completion offers the meta-commands plus the names of constraints
and functions exported from the loaded modules.

## Meta-commands

| Command | Alias | Description |
|---------|-------|-------------|
| `:help` | `:h` | Show meta-command help. |
| `:recompile` | `:r` | Reload the source files from disk. |
| `:list_files` | | List the loaded files. |
| `:list_modules` | | List the loaded modules. |
| `:list_declarations` | | List visible constraint and function declarations. |
| `:list_operators` | | List defined operators (in `op(/3)` form). |
| `:begin` | | Enter a live CHR session. End with `:end`. |
| `:end` | | Leave the current live session. The session's store is discarded. |
| `:quit` | `:q` | Exit the REPL. |

## One-shot queries

Outside a live session, anything typed at the prompt is parsed as a
goal and executed against a **fresh** constraint store. The store is
discarded when the query returns. Resulting bindings (if any) are
printed.

```ychr-repl
ychr> :quit
ychr>
```

(Empty output: the only "query" was `:quit`.)

A query that adds a constraint without firing any rules will silently
succeed; the new constraint is then thrown away with the rest of the
store:

```ychr-repl
ychr> egg.
ychr>
```

## Live sessions

Inside `:begin … :end`, the store **persists** between inputs. Each
line is a goal that adds to (or fires rules against) the running
store. `:end` discards the session's store and returns to normal mode.

The `print_store/0` constraint from the meta library prints every
alive constraint in the store, qualified by module:

```ychr-repl
ychr> :begin
ychr live> egg.
ychr live> egg.
ychr live> print_store.
bakery:egg()
bakery:egg()
ychr live> :end
ychr>
```

(Captured against [`examples/bakery.chr`](../../examples/bakery.chr).)

## History

The REPL stores a persistent line-history file at
`$XDG_DATA_HOME/ychr/history` (typically
`~/.local/share/ychr/history`). It survives across invocations.

## See also

- [How-to: use the REPL](../how-to/use-the-repl.md).
- [CLI reference](cli.md).
