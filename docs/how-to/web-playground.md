# Run the YCHR playground in a browser

The playground is a static page holding the whole compiler: the CHR
front end, the VM compiler, the Haskell interpreter and the optional type
checker, compiled to WebAssembly by [MicroHs](https://github.com/augustss/MicroHs)
and [Emscripten](https://emscripten.org/). Nothing runs on a server —
only the runtime libraries the page loads do, and both are plain files
served over HTTP.

```
program editor          REPL
┌───────────────┐      ┌───────────────┐
│ leq(X, X) <=> …│      │ ychr> leq(X,2)│
│                │      │ X = _.        │
└───────────────┘      └───────────────┘
     │  Reload               ▲  goals
     ▼                       │
   WASM: ychr library (compile → VM → run)
```

## Prerequisites

- **The MicroHs compiler** (`mhs` on `PATH`, or `MHS=path/to/mhs`). MicroHs
  compiles the library and the bridge straight from `src/`, not through
  mcabal.
- **GHC and cabal**, for `make resources`, which generates the built-in
  standard library and type checker (`generated/`).
- **The Emscripten SDK.** MicroHs emits WebAssembly by shelling out to a
  C compiler, so `emcc` is required and there is no pure-JavaScript
  backend to fall back on. `make playground-emsdk` fetches it into
  `.emsdk/` (gitignored, about 1 GB) and activates the version pinned in
  the `Makefile` (`EMSDK_VERSION`).
- **Node**, for the headless test of the built module. The page itself
  needs nothing but a browser.

## Build and run

```sh
make playground-emsdk      # once: fetch emscripten into .emsdk/
make playground-wasm       # build playground/build/ychr-pg.{js,wasm}
make playground-serve      # serve playground/ at http://localhost:8080/
```

Open <http://localhost:8080/>, edit the program, press **Reload**, then
type a goal in the REPL box.

`playground-wasm` first runs `make resources` (a GHC build of
`ychr-codegen`), which writes the standard library and the compiled type
checker as Haskell modules under `generated/`. They are compiled into
the module, so the page reads no library source, parses nothing at
start-up and never compiles the checker.

The build takes about six minutes, most of it MicroHs compiling the
generated checker module; `emcc` then compiles and links the generated C.
The result is roughly 830 KB of JavaScript and WebAssembly.

Two flags matter in `playground-wasm` and are worth knowing about if you
adapt it:

- `-sINVOKE_RUN=0` with `-sEXPORTED_FUNCTIONS=…_mhs_init…`: the Haskell
  `main` never runs. JavaScript calls `mhs_init()` to bring the MicroHs
  runtime up and then calls the exported functions, which is the flow
  MicroHs's own `tests/ForExp.hs` uses for a C host.
- `-sSTACK_SIZE=16MB`: with emscripten's 64 KB default stack, the
  MicroHs runtime crashed ("memory access out of bounds") while it
  compiled the type checker. Not re-tested now that the checker is
  built in.

## What the page does

| Control | Effect |
|---|---|
| **Examples** menu | Replaces the editor's contents with one of the examples the repository ships (`bakery.chr`, `leq.chr`, `fib_memo.chr`, `gcd.chr`, `shortest_path.chr`) and reloads it. |
| **Reload** | Compiles the editor's text as a one-file program and makes it the loaded program. Never type-checks. |
| **Typecheck** | Reloads the editor first, then runs the CHR type checker over the program. |
| Enter in the REPL box | Runs one goal (or colon command) against the loaded program, in a fresh CHR session. |

A reload that fails keeps the previously loaded program — the same
policy the terminal REPL applies to `:recompile` — so a typo never costs
you a working program.

The **Examples** menu has no program text of its own: `make playground-wasm`
copies the five files under `examples/` into `playground/build/`, and the
page fetches them from there (the page is served from `playground/` alone,
so it cannot reach `examples/`). Selecting an entry replaces the editor
and reloads in one step; editing the buffer afterwards returns the menu to
its placeholder, and a copy that cannot be fetched leaves both the editor
and the loaded program alone and reports the failure in the REPL pane.

The REPL box takes a goal, or one of these colon commands: `:help` (or
`:h`), `:list_modules`, `:list_files`, `:list_declarations`, `:info <id>`
(or `:i <id>`). They are the terminal REPL's own commands, rendered by the
same code. What a terminal-only REPL has and the page does not is
`:recompile` (the **Reload** button does that), `:list_operators`,
`:begin` (live sessions), `:trace` and `:time`; `:quit` is accepted and
does nothing, since there is nothing to exit.

Type checking is deliberately *not* automatic. `Reload` and goals behave
like `ychr repl --no-check`; only the **Typecheck** button runs the checker,
and it reloads first so that what it checks is what the editor says — a
reload that does not compile ends the action, since the check would
otherwise describe the program still loaded from before.

## What it costs

Measured 2026-11-19 on one AMD64 machine (Node 22, Emscripten 6.0.10,
MicroHs 0.17.1.0), on the starter program. The shape of the numbers
rather than a contract:

| Step | WASM (Node) |
|---|---|
| Instantiate + `mhs_init()` | ~0.1 s |
| `ychr_pg_init` | ~0.01 s |
| Reload a small program | ~0.1 s |
| One query | ~20 ms |
| First Typecheck | ~5.5 s |
| Later Typechecks | ~4 s |

The page is usable as soon as the module loads. Before the resources
were built into the module, start-up parsed the standard library (~2 s)
and the first Typecheck compiled the checker (~11 s in total).

Type checking is still the expensive part: the checker is itself a CHR
program of ~900 procedures, and each check builds a fresh CHR session
over it and runs it to quiescence. The first check also pays for
materializing the built-in checker. Hence the button, and hence the page
saying what it is doing before going quiet.

MicroHs-compiled code is much slower than the GHC-built compiler (see
`dev-docs/MICROHS_PERFORMANCE.md`), and the browser adds its own factor
on top of the native MicroHs build.

One choice is worth calling out because it moves the last two rows a
long way: the reload compiles with `includeStdlib = False`, as every CLI
command does. The bundled libraries are then pulled in only as far as
the program's own `:- use_module(library(…))` clauses reach, so what the
checker sees is the program, not the standard library.

## The bridge

Five C entry points, exported with `foreign export ccall` from
`playground/YCHR/Playground/Wasm.hs`. Each takes and returns a UTF-8 C
string, allocated on the Haskell side and released by the page with
`ychr_pg_free`:

| Export | Argument | Meaning |
|---|---|---|
| `ychr_pg_init` | — | make the playground ready on the built-in resources |
| `ychr_pg_compile` | program text | reload; never type-checks |
| `ychr_pg_query` | one REPL line | run a goal or colon command |
| `ychr_pg_check` | — | type-check what is loaded |
| `ychr_pg_free` | a returned string | release it |

Every call answers with a *response envelope*:

```
ok\n\n<payload>
error\n\n<payload>
```

The payload is the text the CLI would have printed, ANSI colour
sequences included, which the page turns into spans — with one addition:
a successful *reload* also reports how many constraint types the
program's own modules declare (`Loaded 1 constraint: leq/2`), a line no
CLI command prints, because the page has no other way to say "the editor
compiled". Everything else — diagnostics, warnings, query bindings, the
colon commands — is byte-for-byte what the terminal REPL writes. Keeping
the payload plain text is what makes that true, and what lets the
protocol do without an escaping layer.

The logic behind the exports is `playground/YCHR/Playground.hs`, which
knows nothing about FFI or browsers. `playground/Main.hs` drives that
same module over a line protocol on stdin, and `test/playground/`
asserts the harness and the WASM module against **one** table of
expectations, so the two front ends cannot drift apart unnoticed.

`make test-playground` runs both halves — the WASM tests skip themselves
unless `playground/build/ychr-pg.js` exists — and
`make playground-check` is the full sequence: build the module, then run
both. Nothing in CI builds the WASM bundle (it needs the emscripten SDK),
so `make playground-check` is what a change to the bridge or the page
should be verified with locally.

## Files

| Path | What it is |
|---|---|
| `playground/index.html`, `playground.css`, `playground.js` | the page: two panes, a toolbar, and an ANSI-to-HTML converter |
| `playground/YCHR/Playground.hs` | the engine: state, reload, queries, colon commands, type checking |
| `playground/YCHR/Playground/Wasm.hs` | the `foreign export ccall` bridge (WASM build only) |
| `playground/Main.hs` | the native harness used by the tests |
| `playground/build/` | the generated bundle (gitignored): the module, plus `starter.chr` and the preset copies of `examples/*.chr` the page loads |
| `test/playground/` | the native and WASM test suites, with their shared expectations |

## Limits

- One program at a time, compiled from a single buffer;
  `:- use_module(library(...))` of the bundled libraries works,
  importing files from disk does not.
- One-shot queries only. A live session (the terminal REPL's `:begin`)
  would need the session environment to be held across calls, which the
  bridge does not do yet.
- The editor is a `textarea`: no syntax highlighting, completion or
  diagnostics in place.
- Long compiles block the page. The status line is painted before the
  call, but the browser cannot repaint while the WASM runs; a Web Worker
  would fix that.
- Each check runs in a fresh CHR session over the checker (about 4 s).
  Caching the session would remove most of that.
