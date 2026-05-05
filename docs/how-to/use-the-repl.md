# How to use the REPL

> **Goal:** load a program, run queries, and use a live session.

This page is a stub.

## Starting the REPL

```sh
ychr repl file.chr
ychr repl --quiet file.chr   # no banner, no prompt
```

## Meta-commands

| Command | Purpose |
|---------|---------|
| `:help`, `:h` | Show meta-command help. |
| `:recompile`, `:r` | Reload the source files. |
| `:list_files` | List the loaded files. |
| `:list_modules` | List the loaded modules. |
| `:list_declarations` | List visible constraint and function declarations. |
| `:list_operators` | List defined operators. |
| `:begin` | Start a live CHR session (interactive store; end with `:end`). |
| `:quit`, `:q` | Exit the REPL. |

> **TODO:** examples of each, what the output looks like, and the
> difference between a one-shot query and a live session.

## Queries

> **TODO:** show how to type a query, how bindings are printed, how
> `Ctrl-D` and `:quit` behave.

## Live sessions

> **TODO:** describe the `:begin … :end` workflow — how the constraint
> store persists between inputs, when to use it instead of one-shot
> queries.

## See also

- [CLI reference](../reference/cli.md).
- [REPL reference](../reference/repl.md).
