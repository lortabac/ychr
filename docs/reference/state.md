# State

`library(state)` emulates mutable variables with constraints. A stateful
variable is declared with a declaration macro:

```prolog
:- use_module(library(state)).
:- use_module(library(pairs)).

:- chr_type key ---> count ; name.

:- state(count, int).
:- state(name, string).
```

`:- state(Key, Type).` expands to a per-key API in the module that uses
it, with the value type fixed at the declaration:

| Name | Meaning |
|---|---|
| `new_Key(V)` | creates `Key` with initial value `V` |
| `get_Key(R)` | unifies `R` with the current value of `Key` |
| `put_Key(V)` | replaces the value of `Key` with `V` |
| `modify_Key(F)` | replaces the value `V` of `Key` with `F(V)` |
| `close_Key` | deletes `Key`, which may then be created again |

The value is held by a private `state_Key(Type)` constraint, and the
requests are declared `event`: they are consumed when they are told. The
generated names are `state_`, `new_`, `get_`, `put_`, `modify_` and
`close_` prefixed to the key, so `:- state(count, int).` gives
`new_count/1`, `get_count/1`, `put_count/1`, `modify_count/1` and
`close_count/0`.

Import `macro(state/2)` as above: a narrowed import list fails, starting
with `UnknownDirective` for `:- state(k, int).` itself. A full import also
brings in `new_goal/2`, `get_goal/2`, `not_initialized/0` and
`already_initialized/0`: a macro body must name only exported names, so
they are public by construction. Treat them as internal.

## The runner

`new_Key` and `close_Key` are the low-level API, exposed for
completeness. The way to use a state variable is the scoped runner,
after Haskell's runState:

```prolog
counted(R) <=> R is run_state(count, 1, quote([step, step])).

pair_run(A, B) <=>
    [kv(count, A), kv(name, B)] is
        run_states([kv(count, 1), kv(name, "x")], quote([swap])).
```

`run_state(K, V, quote(Goal))` creates `K` at `V`, runs `Goal` and
returns the final value. `run_states(KVs, quote(Goal))` does the same for
every `kv(K, V)` of `KVs` and returns the final `kv` list; a `KVs` that
is not a proper list of `kv` pairs is a runtime error. The goal is a
constraint term or a list of them, as for `search:solve/1`, and runs as
`solve/1` runs it, against a fork of the calling session
([search.md](search.md#scope-search-forks-the-calling-session)): the keys
are created there before the goal and read back after it, so no key has
to be closed by hand, and the run's store is discarded when it returns.
The goal sees the caller's constraints, its keys included. The reads
happen before any choice point the goal leaves is explored, so write the
goal deterministically: a goal that searches does not give the values of
its solution.

The runner takes `kv(K, V)`, so a key named in it is also a data
constructor: `:- chr_type key ---> k ; n.` makes `kv(k, 1)` a value.
Without the declaration the generated dispatch reports the key as an
undeclared data constructor (`YCHR-20101`), which `--Werror` rejects. An
integer key (`:- state(1, int).`, `kv(1, V)`) needs no declaration. The
key of `:- state(Key, Type).` itself must be an atom or an integer, since
the expansion builds the generated names from it.

## Runtime behavior

Misuse of the low-level requests is a runtime error, raised when the
request is made:

- `new_Key` on a key that already exists;
- `get_Key`, `put_Key`, `modify_Key` or `close_Key` on a key that does not
  exist.

The message is generic: the request that failed is a generated name with
the key in it, so repeating the key in the message would mean passing a
bare key atom in an evaluated argument, which the renamer reports as an
undeclared data constructor.

```
YCHR-60001
state: key is not initialized
```

A run whose goal has no solution is a runtime error too:

```
YCHR-60001
state: the goal of a run has no solution
```

A request written directly in a rule is type-checked, so a mismatch is a
compile-time error:

```prolog
new_count(1), put_count("a").   % type error: string vs int
```

`Type` must be a ground type (`int`, `string`, `list(int)`, …). A type
variable makes the holder polymorphic, and the generated rules then fail
the type checker.

The runner's own values are not checked. `KVs` is a `list(pair(K, any))`,
and the goal's constraints are told by their bare name with the prelude's
`tell_list/1`, so a dynamically told goal bypasses the checker: a
`kv(K, V)` of the wrong type is accepted and runs, and only a goal that
names no constraint is an error. That bare-name resolution is
program-wide: keep every generated name unique across the program. Two
modules declaring `:- state(k, int).` both generate `new_k/1`, and every
`run_states` call then reports the ambiguity rather than picking one. The
runner tells its goals one by one, so a `;` disjunction is not a tellable
element: write its branches as separate constraints.
