# REPL Reference

## Starting the REPL

```sh
ychr repl [--quiet] [--Werror] [FILES...]
```

Loads the files (or none), prints warnings and type-check messages,
shows the `ychr> ` prompt. The full standard library is auto-loaded;
no `:- use_module(library(...))` is needed for prelude, meta or search
names.

A query resolves against every auto-loaded library, so a bare name a
loaded file also exports is ambiguous at the prompt (inside a module
body it would resolve locally). With a file exporting its own `fail/0`:

```ychr-repl
ychr> fail.
=== error ===
<generated>:1:1: YCHR-20001
Ambiguous name 'fail/0'
  Hint: could be: lib_a, search; qualify the name explicitly to disambiguate
```

Qualify it: `lib_a:fail`. `library(search)` puts in query scope the
constraints `alt/1`, `choose/2`, `try_unify/2`; the functions
`fail/0`, `solve/1`, `find_all/2`, `fold_solutions/4`, `forall/3`,
`find_n/3`; and the type `step/1` with constructors `continue/1`,
`stop/1`, `commit/1` — so a bare `continue(1)` is
`search:continue(1)`.

`--quiet` drops the prompt, the warnings and the type-check report,
except under `--Werror`,
where warnings are still printed. Under `--Werror` a warning on the
initial load aborts startup; on `:recompile` it keeps the previous
program; while renaming a query's arguments it aborts that query and
leaves the store alone.

## Prompts

| Prompt | Mode |
|--------|------|
| `ychr> ` | Normal mode. Each query runs against a fresh, empty store. |
| `ychr live> ` | Live session (between `:begin` and `:end`). Queries share a persistent store. |

Tab completion offers the constraint and function names exported from
the loaded modules, plus the meta-commands at the outer prompt (only
`:end` inside a live session).

## Meta-commands

| Command | Alias | Description |
|---------|-------|-------------|
| `:help` | `:h` | Show meta-command help. |
| `:recompile` | `:r` | Reload the source files from disk. |
| `:list_files` | | List the loaded files. |
| `:list_modules` | | List the loaded modules. |
| `:list_declarations` | | List visible constraint and function declarations. |
| `:list_operators` | | List defined operators, one `op/3` term per line. |
| `:info NAME` | `:i NAME` | Show information about an identifier (see below). |
| `:trace GOAL` | | Run `GOAL` with refined-operational-semantics tracing (see below). |
| `:begin` | | Enter a live CHR session. End with `:end`. |
| `:end` | | Leave the current live session. The session's store is discarded. |
| `:quit` | `:q` | Exit the REPL. |

### `:info`

`:info NAME` prints the fully qualified name, then an equivalent
declaration. Built-in types (`int`, `float`, `string`, `any`) print
`built-in type`, qualified by the type checker's internal module.
`NAME` may be bare (`foo`), an operator atom (`'+'`), `name/arity`
(`call/2`), qualified (`prelude:max`), or any combination. A bare name
matching several arities prints all of them; a bare `name/arity`
exported by more than one module is reported as ambiguous — qualify it.

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

`:trace GOAL` runs `GOAL` printing one event per step of the refined
operational semantics (ωr) plus user-function, lambda and host calls,
indented by nesting. Only the trace is printed; re-run without
`:trace` for the bindings. Works at the outer prompt and inside a live
session (the handler lasts one query).

```ychr-repl
ychr> :trace R is 1 + 2.
call prelude:+(1, 2)
  host call +(1, 2) = 3
return 3
```

The next transcript shows tell, activate, try-occurrence, partner,
fire, store and recursive activation. The first `leq(1, 2)` finds no
partner (the store is empty); the second finds `c#0` and transitivity
fires:

```ychr-repl
ychr> :trace order:leq(1, 2), order:leq(2, 3).
tell order:leq(1, 2)
  activate c#0: order:leq(1, 2)
    try occurrence order:leq #1 (rule reflexivity)
    try occurrence order:leq #2 (rule antisymmetry)
    try occurrence order:leq #4 (rule idempotence)
    try occurrence order:leq #6 (rule transitivity)
    try occurrence order:leq #7 (rule transitivity)
    store c#0: order:leq(1, 2)
tell order:leq(2, 3)
  activate c#1: order:leq(2, 3)
    try occurrence order:leq #1 (rule reflexivity)
    try occurrence order:leq #2 (rule antisymmetry)
    try occurrence order:leq #4 (rule idempotence)
    try occurrence order:leq #6 (rule transitivity)
      partner c#0: order:leq(1, 2)
        fire transitivity [c#1, c#0]
        store c#1: order:leq(2, 3)
        tell order:leq(1, 3)
          activate c#2: order:leq(1, 3)
            try occurrence order:leq #1 (rule reflexivity)
            try occurrence order:leq #2 (rule antisymmetry)
            try occurrence order:leq #4 (rule idempotence)
            try occurrence order:leq #6 (rule transitivity)
            try occurrence order:leq #7 (rule transitivity)
            store c#2: order:leq(1, 3)
    try occurrence order:leq #7 (rule transitivity)
```

Occurrences 3 and 5 are passive: the compiler emits no procedure for
them ([passive occurrences](../../dev-docs/passive-occurrences.md#worked-example-leq)).

Storage is late: a constraint enters the store on the first fire that
keeps it (`store c#1` before transitivity's body) or when its
activation ends without dropping it (`store c#0`); one removed during
its own activation is never stored. So during its initial activation a
constraint never appears as its own partner — it is not in the store
yet. A reactivated one is already stored and can, until the guard
rejects the self-match.

Events:

| Event | Meaning |
|-------|---------|
| `tell C(...)` | A constraint is being added. |
| `store c#N: C(...)` | The constraint has been added to the store with id `c#N` (late: on the first fire that keeps it, or when its activation ends). |
| `activate c#N: C(...)` | The constraint becomes the active constraint. |
| `try occurrence T #J (rule R)` | Entering the `J`-th occurrence of constraint `T` (in rule `R`). |
| `partner c#N: C(...)` | A partner constraint matched in a head loop. |
| `history hit R [c#…]` | Propagation history blocked the rule firing again. |
| `fire R [c#…]` | The rule `R` is firing with the listed constraints. |
| `kill c#N` | The constraint has been removed from the store. |
| `reactivate c#N: C(...)` | A stored constraint is being re-activated because a variable it observes was bound. |
| `unify L = R (K constraints reactivated)` | A tell-side unification succeeded, enqueueing `K` constraints for reactivation. |
| `call F(...)` / `return V` | A user-defined function or lambda was called and returned. |
| `host call F(...) = V` | A host primitive was called. |

## One-shot queries

Outside a live session each input is a goal run against a fresh
store, discarded when the query returns. Bindings are printed, except
for variables whose name starts with `_` (`_X`) — Prolog convention;
they are still bound, only the output is filtered.

`ychr run -g GOAL` takes exactly one declared constraint (`cake`,
`compute(5, R)`, `bakery:egg`); a bare expression, an `is`/`=` form, a
conjunction or a function call is `YCHR-20013`. `--show-bindings`
prints the bindings one per line, sorted. The REPL accepts any goal:
`1 + 1.`, `X = 2.`, `X is 1 + 1.`, conjunctions, constraint calls.

A query that adds a constraint and fires nothing succeeds silently;
the constraint goes with the store:

```ychr-repl
ychr> egg.
ychr>
```

## Live sessions

Inside `:begin … :end` the store persists between inputs; `:end`
discards it. A live query may not contain a lambda (`YCHR-50003`); put
it in a `:- function` in a file. `print_store/0` (meta library) prints
every alive constraint, module-qualified. Transcript:
[Getting started §4](../tutorials/01-getting-started.md#4-try-it-in-a-live-session).

## History

`$XDG_DATA_HOME/ychr/history` (usually `~/.local/share/ychr/history`).

If that history file cannot be used — the data directory is not
writable, so it cannot be created, or the file itself is read-only,
unreadable, or a directory — the REPL starts with history disabled
rather than failing to start. It reports `REPL history not available` on
stderr; `--quiet` suppresses the report, as it does compile warnings.
Everything else about the session (queries, prompts, live sessions, tab
completion) is unaffected.
