# REPL Reference

## Starting the REPL

```sh
ychr repl [--repl-backend BACKEND] [--quiet] [--show-store] [--no-check] [--Werror] [--dump-splices] [FILES...]
```

`ychr FILES...` (no subcommand) is short for `ychr repl FILES...` with
default flags. Flags go after the subcommand: `ychr --quiet repl` is
a usage error.

Loads the files (or none), prints warnings and type-check messages,
shows the `ychr> ` prompt. The full standard library is auto-loaded;
no `:- use_module(library(...))` is needed for prelude, meta, search or
state names.

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
constraints `alt/1`, `choose/2`, `between/3`, `try_unify/2`; the
functions `fail/0`, `solve/1`, `findall/2`, `fold_solutions/4`,
`forall/3`, `find_n/3`; and the type `step/1` with constructors
`continue/1`, `stop/1`, `commit/1` — so a bare `continue(1)` is
`search:continue(1)`. Constructors match by name alone, at any arity:
a bare `stop` at the prompt is `search:stop` too (and a type error,
`YCHR-60008`), and if a loaded file exports its own `stop` it is
ambiguous (`YCHR-20012`). Qualify it. `library(state)` declares no constraints: it puts
the functions `run_state/3` and `run_states/2` in query scope, while
`:- state(Key, Type).` is a declaration macro that can only be used in a
file, so a state key must come from a loaded module
([state.md](state.md)).

`--quiet` drops the prompt, the warnings and the type-check report,
except under `--Werror`,
where warnings are still printed. Under `--Werror` a warning on the
initial load aborts startup; on `:recompile` it keeps the previous
program; while renaming a query's arguments it aborts that query and
leaves the store alone. Exhaustiveness warnings (YCHR-20103) are part
of the type-check report, so `--Werror` doesn't make them fatal here.

`--no-check` skips the type checker entirely: no type-check report on
startup or `:recompile`, and every query runs unchecked, so a goal the
checker would reject reaches the runtime instead. Compilation errors —
parse, collect, rename, resolve, desugar — still fail, and `--Werror`
still treats the remaining compile and rename warnings as fatal.
`ychr check` — whose whole purpose is type checking — does not accept
the flag.

`--show-store` prints the constraints left in the store after each
query; see [Showing the store](#showing-the-store).

`--dump-splices` prints the clauses the loaded files' declaration
macros spliced, to stderr, on startup and on `:recompile`. It is an
explicit debugging request, so `--quiet` does not suppress it. See
[macros.md](macros.md#dumping-the-splices).

## REPL backends

`--repl-backend` selects where queries run. The values are `interpreter`
(the default) and `chez`.

`interpreter` runs everything in the Haskell runtime, as before.

`chez` starts one persistent Chez Scheme process with the `scheme`
command and runs every query there. Haskell still parses, renames,
type-checks and prepares the query; it compiles the prepared goals to
Scheme and sends one expression per query. The constraint store, rule
execution, user functions, search and live-session state all stay in
Chez, so a query crosses the process boundary once, not once per
constraint or function. Set `YCHR_SCHEME` to use a Chez executable with
another name, and `YCHR_SCHEME_LIB_DIR` to the `scheme/` directory of a
YCHR source checkout when the REPL is not run from the checkout root
(the directory must contain `ychr/runtime.sls` and
`ychr/repl-server.scm`). The installed package does not ship the Scheme
runtime.

The Chez backend keeps the rest of the REPL unchanged: `--quiet`,
`--Werror`, `--no-check`, `:info`, `:list_*`, history and tab
completion are Haskell-side, and live sessions persist their store in
Chez. `:recompile` starts a new Chez process with the newly compiled
program. `:trace` is not available with this backend; it reports that
and does not run the query. `:time` is measured by the Chez process, as
process CPU time.

Runtime errors use the same `YCHR-60001` envelope as the interpreter.
Some existing Scheme/Haskell differences remain — for example float
pretty-printing and the absence of a Haskell call stack on a Scheme
runtime error — so diagnostics can differ in those details.

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
| `:recompile` | `:r` | Reload the source files. On failure the previous program stays loaded. |
| `:list_files` | | List the loaded files. |
| `:list_modules` | | List the loaded modules. |
| `:list_declarations` | | List visible constraint and function declarations. |
| `:list_operators` | | List defined operators, one `op/3` term per line. |
| `:info NAME` | `:i NAME` | Show information about an identifier (see below). |
| `:trace [OPTION...] GOAL` | | Run `GOAL` with tracing, then print the bindings (interpreter backend only; see below). |
| `:time GOAL` | | Run `GOAL` and print its execution time in seconds, then the bindings (see below). |
| `:begin` | | Enter a live CHR session. End with `:end`. |
| `:end` | | Leave the current live session. The session's store is discarded. |
| `:quit` | `:q` | Exit the REPL. |

### `:info`

`:info NAME` prints the fully qualified name, then an equivalent
declaration. Built-in types (`int`, `float`, `string`, `type_name`, `any`) print
`built-in type`, qualified by the type checker's internal module.
`NAME` may be bare (`foo`), an operator atom (`'+'`), `name/arity`
(`call/2`), qualified (`prelude:max`), or any combination. A bare name
matching several arities prints all of them; a bare `name/arity`
exported by more than one module is reported as ambiguous — qualify it.
A `requiring` bound prints qualified (`lib:gt`) unless it names
something in `NAME`'s own module; two or more bounds each print in
parens, so the output parses back.

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

`:trace [OPTION...] GOAL` runs `GOAL` printing one event per step of
the refined operational semantics (ωr) plus user-function, lambda and
search events, indented by nesting. After the trace it prints what a
plain query prints: the bindings and, with `--show-store`, the store.
Works at the outer prompt and inside a live session (the handler lasts
one query). It is available only with the default `interpreter`
backend.

By default library modules (`prelude`, `lists`, …) and host calls are
hidden. `--all` shows them:

```ychr-repl
ychr> :trace R is 1 + 2.
R = 3.
ychr> :trace --all R is 1 + 2.
call prelude:+(1, 2)
  host call +(1, 2) = 3
return 3
R = 3.
```

Options come before the goal; `--` ends them. `-c`, `-r` and `-e` take
a comma-separated list with no spaces, and may repeat.

| Option | Shows |
|--------|-------|
| `-c C[,C]` | Only events about these constraints: `name`, `name/N`, `mod:name` or `mod:name/N`. |
| `-r R[,R]` | Only events of these rules: their occurrences and what happens inside them, the body included, but not an occurrence of another rule nested in it. A name matches a rule of that name in any module. |
| `-e KIND[,KIND]` | Only these kinds: `tell`, `activate`, `try`, `partner`, `history`, `fire`, `store`, `kill`, `reactivate`, `unify`, `call` (call and return), `host`, `search` (all six search events). |
| `--depth N` | Only events nested less than `N` levels deep. Every level counts, shown or not, so a cut hides a whole subtree. |
| `--all` | Library modules and host calls too. |

An event is shown if its kind is selected, it is above the depth
limit, and it matches `-c` and `-r` when they are given. A name given
with `-c` or `-r` is shown even in a library module. Without them, an
event in a library module is hidden; an event that names no module
(`unify`, `host call`) takes the module of the event it is nested in.
Search events always count as the query's. A rule's events take the
module of the constraint whose occurrence is running, so a user rule
over a library constraint is hidden too.

Hidden events don't take up a level: an event is indented by the
number of shown events above it. So `-e fire,store` is a flat list
(over `examples/leq.chr`):

```ychr-repl
ychr> :trace -e fire,store order:leq(1, 2), order:leq(2, 3).
store c#0: order:leq(1, 2)
fire transitivity [c#1, c#0]
store c#1: order:leq(2, 3)
store c#2: order:leq(1, 3)
```

Only rules with a propagation history print `fire`; a plain
simplification or simpagation fires without one. A bad option or kind
prints an error and runs nothing; a `-c` or `-r` name the program does
not have prints a warning and runs the goal anyway.

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

### `:time`

`:time GOAL` runs `GOAL` like an ordinary one-shot query, but prints
its execution time before the result:

```ychr-repl
ychr> :time R is 1 + 2.
Time: 0.000038s
R = 3.
```

The number is CPU time in seconds with microsecond resolution (six
decimals). It covers query execution — including the fresh session a
one-shot query builds — and not preparation: parsing, renaming,
resolution, desugaring, lambda-lifting and type-checking of the query
itself are all excluded. A query rejected before execution (a parse,
rename, resolution or desugar error, a type error, a `--Werror`
warning) prints no timing line, because nothing ran; a query that fails
at run time prints the timing line before the diagnostic — after
whatever the query itself printed. Available at the outer prompt only:
inside a live session `:time GOAL` is not a meta-command and is read as
a query.

## One-shot queries

Outside a live session each input is a goal run against a fresh
store, discarded when the query returns. Bindings are printed, except
for variables whose name starts with `_` (`_X`) — Prolog convention;
they are still bound, only the output is filtered. This holds for
every binding printer, the Scheme `tell` helper included (see
[scheme-repl.md](../how-to/scheme-repl.md)).

`ychr run -g GOAL` takes exactly one declared constraint (`cake`,
`compute(5, R)`, `bakery:egg`); a bare expression, an `is`/`=` form, a
conjunction or a function call is `YCHR-20013`. `--show-bindings`
prints the visible bindings one per line, sorted, as `K = V` with no
trailing dot. The REPL accepts any goal:
`1 + 1.`, `X = 2.`, `X is 1 + 1.`, conjunctions, constraint calls.

A query that adds a constraint and fires nothing succeeds silently;
the constraint goes with the store:

```ychr-repl
ychr> egg.
ychr>
```

## Showing the store

With `--show-store`, every query also prints the
constraints left in the store, one per line, after the bindings. The
format is `print_store`'s. A variable that is a visible query variable
(not `_`-prefixed) shows under its name; any other unbound variable is `_G1`, `_G2`, … in order
of first appearance. With `ychr repl --show-store examples/leq.chr`:

```ychr-repl
ychr> leq(A, B), leq(B, C).
A = _,
B = _,
C = _.
order:leq(A, B)
order:leq(B, C)
order:leq(A, C)
ychr> leq(A, B), leq(B, A).
A = B,
B = A.
ychr> leq(A, _).
A = _.
order:leq(A, _G1)
```

At most 50 lines are printed, then `... and N more`. It applies to
one-shot queries, `:time`, `:trace` and live-session queries (where
the store also holds what earlier inputs left), on both backends.
There is no `:set` yet, so the flag is the only switch.

`ychr run --show-store -g GOAL` prints the store the same way, after
the bindings if `--show-bindings` is also given:

```sh
$ ychr run --show-store -g 'leq(A, B)' examples/leq.chr
order:leq(A, B)
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
