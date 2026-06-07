# REPL Reference

> **Audience:** anyone using `ychr repl`.
> **You will:** find the REPL prompts, meta-commands, and the
> difference between one-shot queries and live sessions.

For a guided walk-through, see
[how-to/use-the-repl.md](../how-to/use-the-repl.md).

## Starting the REPL

```sh
ychr repl [--quiet] [--Werror] [FILES...]
```

The REPL loads the given files (or none, falling back to the bundled
prelude alone), prints any warnings and type-check messages, and
presents the `ychr> ` prompt. The full standard library is auto-loaded;
no `:- use_module(library(...))` is needed for prelude or meta
identifiers.

The `--quiet` flag suppresses the prompt and warnings — useful when
piping input from a script or test harness.

The `--Werror` flag treats warnings as errors. Warnings during the
initial load abort startup with a non-zero exit; warnings encountered
during `:recompile` keep the previously loaded program in place
(matching the behavior on a compile error). Warnings are still printed
to stderr under `--Werror` even if `--quiet` is also set, so the
failure is never silent.

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
| `:info NAME` | `:i NAME` | Show information about an identifier (see below). |
| `:trace GOAL` | | Run `GOAL` with refined-operational-semantics tracing (see below). |
| `:begin` | | Enter a live CHR session. End with `:end`. |
| `:end` | | Leave the current live session. The session's store is discarded. |
| `:quit` | `:q` | Exit the REPL. |

### `:info`

`:info NAME` (alias `:i NAME`) prints information about an identifier:
the fully qualified name on the first line, then a semantically
equivalent declaration on the next. Built-in types (`int`, `float`,
`string`, `any`) print `built-in type`. The argument can be a bare
name (`foo`), an operator atom (`'+'`), a `name/arity` form
(`call/2`), a qualified name (`prelude:max`), or any combination.
When a bare name matches multiple arities, every match is printed.
When a bare `name/arity` is exported by more than one module the
command refuses to guess: it reports the ambiguity and asks for a
qualified form.

```ychr-repl
ychr> :info int
'$typechecker':int
built-in type
ychr> :info '+'
prelude:'+'
:- class
    ('+'(float, float) -> float),
    ('+'(int, int) -> int).
ychr> :info max
prelude:max
:- function max(T, T) -> T requiring '>='(T, T) -> bool.
ychr> :info true
prelude:true
:- chr_type bool ---> true ; false.
ychr> :info foo
unknown identifier: foo
```

### `:trace`

`:trace GOAL` runs `GOAL` with the interpreter's tracer enabled,
printing one event per step of the refined operational semantics (ωr)
plus entries for user-function calls, lambda calls, and host calls.
Indentation reflects nesting. The output is the trace only — final
bindings are not printed; re-run the goal without `:trace` to see them.

`:trace` works at the outer prompt (against a fresh store) and inside
a live session (the trace handler is installed for the duration of
one query, leaving subsequent untraced queries unaffected).

```ychr-repl
ychr> :trace R is 1 + 2.
call prelude:+(1, 2)
  host call +(1, 2) = 3
return 3
```

A small CHR example showing tell, store, activate, try-occurrence,
partner pick, fire, and recursive activation. The first `leq(1, 2)`
finds no partners (the store is empty when it activates); the second
`leq(2, 3)` finds `c#0` as a transitivity partner and the rule fires:

```ychr-repl
ychr> :trace order:leq(1, 2), order:leq(2, 3).
tell order:leq(1, 2)
  store c#0: order:leq(1, 2)
  activate c#0: order:leq(1, 2)
    try occurrence order:leq #1 (rule reflexivity)
    try occurrence order:leq #2 (rule antisymmetry)
    try occurrence order:leq #3 (rule antisymmetry)
    try occurrence order:leq #4 (rule idempotence)
      partner c#0: order:leq(1, 2)
    try occurrence order:leq #5 (rule idempotence)
      partner c#0: order:leq(1, 2)
    try occurrence order:leq #6 (rule transitivity)
    try occurrence order:leq #7 (rule transitivity)
tell order:leq(2, 3)
  store c#1: order:leq(2, 3)
  activate c#1: order:leq(2, 3)
    try occurrence order:leq #1 (rule reflexivity)
    try occurrence order:leq #2 (rule antisymmetry)
    try occurrence order:leq #3 (rule antisymmetry)
    try occurrence order:leq #4 (rule idempotence)
      partner c#1: order:leq(2, 3)
    try occurrence order:leq #5 (rule idempotence)
      partner c#1: order:leq(2, 3)
    try occurrence order:leq #6 (rule transitivity)
      partner c#0: order:leq(1, 2)
        fire transitivity [c#1, c#0]
        tell order:leq(1, 3)
          store c#2: order:leq(1, 3)
          activate c#2: order:leq(1, 3)
            try occurrence order:leq #1 (rule reflexivity)
            try occurrence order:leq #2 (rule antisymmetry)
            try occurrence order:leq #3 (rule antisymmetry)
            try occurrence order:leq #4 (rule idempotence)
              partner c#2: order:leq(1, 3)
            try occurrence order:leq #5 (rule idempotence)
              partner c#2: order:leq(1, 3)
            try occurrence order:leq #6 (rule transitivity)
            try occurrence order:leq #7 (rule transitivity)
    try occurrence order:leq #7 (rule transitivity)
```

Note: the `partner c#N` lines that appear in the idempotence
occurrences match the active constraint against itself; the compiled
guard then rejects the self-match (events for those guard rejections
are not currently traced).

The events are:

| Event | Meaning |
|-------|---------|
| `tell C(...)` | A constraint is being added. |
| `store c#N: C(...)` | The constraint has been added to the store with id `c#N`. |
| `activate c#N: C(...)` | The constraint becomes the active constraint. |
| `try occurrence T #J (rule R)` | Entering the `J`-th occurrence of constraint `T` (in rule `R`). |
| `partner c#N: C(...)` | A partner constraint matched in a head loop. |
| `history hit R [c#…]` | Propagation history blocked the rule firing again. |
| `fire R [c#…]` | The rule `R` is firing with the listed constraints. |
| `kill c#N` | The constraint has been removed from the store. |
| `reactivate c#N: C(...)` | A stored constraint is being re-activated because a variable it observes was bound. |
| `unify L = R (K constraints reactivated)` | An ask-side unification succeeded, enqueueing `K` constraints for reactivation. |
| `call F(...)` / `return V` | A user-defined function or lambda was called and returned. |
| `host call F(...) = V` | A host primitive was called. |

## One-shot queries

Outside a live session, anything typed at the prompt is parsed as a
goal and executed against a **fresh** constraint store. The store is
discarded when the query returns. Resulting bindings (if any) are
printed. Following Prolog convention, bindings for variables whose
name begins with `_` (e.g. `_X`, `_Y`) are omitted from the printed
result — the leading underscore marks them as intentionally
uninteresting. They are still bound; only the output is filtered.

Unlike `ychr run -g` (which accepts only a single declared constraint
— see [`cli.md`](cli.md)), the REPL accepts any goal: bare expressions
(`1 + 1.`), equality and `is` (`X = 2.`, `X is 1 + 1.`), comma-separated
conjunctions, and constraint calls all work.

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

The `print_store/0` function from the meta library prints every
alive constraint in the store, qualified by module:

```ychr-repl
ychr> :begin
ychr live> egg.
ychr live> egg.
ychr live> print_store.
bakery:egg
bakery:egg
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
