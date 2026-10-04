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

- **The MicroHs compiler** (`mhs` on `PATH`, or `MHS=path/to/mhs`). The
  build never goes through cabal: MicroHs compiles the library and the
  bridge straight from `src/`.
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
make playground-wasm       # build playground/build/ychr-pg.{js,wasm,data}
make playground-serve      # serve playground/ at http://localhost:8080/
```

Open <http://localhost:8080/>, edit the program, press **Reload**, then
type a goal in the REPL box.

The build takes about two minutes: MicroHs compiles the library, and
`emcc` compiles and links the generated C. The result is roughly 800 KB
of JavaScript, WebAssembly and preloaded library sources.

Two flags matter in `playground-wasm` and are worth knowing about if you
adapt it:

- `-sINVOKE_RUN=0` with `-sEXPORTED_FUNCTIONS=…_mhs_init…`: the Haskell
  `main` never runs. JavaScript calls `mhs_init()` to bring the MicroHs
  runtime up and then calls the exported functions, which is the flow
  MicroHs's own `tests/ForExp.hs` uses for a C host.
- `-optl --preload-file=libraries@/libraries` (and the same for
  `typechecker`): the two source directories are packed into
  `ychr-pg.data` and mounted in the module's file system at `/libraries`
  and `/typechecker`, which is where `YCHR.Internal.Resources` looks when
  the page passes `/` as the resource root.

`--preload-file` is an emcc flag, not an mhs one, which is why it is
passed through `-optl`.

## What the page does

| Control | Effect |
|---|---|
| **Reload** | Compiles the editor's text as a one-file program and makes it the loaded program. Never type-checks. |
| **Typecheck** | Reloads the editor first, then runs the CHR type checker over the program. The checker itself is compiled on first use. |
| Enter in the REPL box | Runs one goal (or colon command) against the loaded program, in a fresh CHR session. |

A reload that fails keeps the previously loaded program — the same
policy the terminal REPL applies to `:recompile` — so a typo never costs
you a working program.

The REPL box takes a goal, or one of these colon commands: `:help` (or
`:h`), `:list_modules`, `:list_files`, `:list_declarations`, `:info <id>`
(or `:i <id>`). They are the terminal REPL's own commands, rendered by the
same code. What a terminal-only REPL has and the page does not is
`:recompile` (the **Reload** button does that), `:list_operators`,
`:begin` (live sessions), `:trace` and `:time`; `:quit` is accepted and
does nothing, since there is nothing to exit.

Type checking is deliberately *not* automatic. `Reload` and goals behave
like `ychr --no-check`; only the **Typecheck** button runs the checker,
and it reloads first so that what it checks is what the editor says — a
reload that does not compile ends the action, since the check would
otherwise describe the program still loaded from before.

## What it costs

Measured 2026-10-02 on one AMD64 machine (Node 24, Emscripten 6.0.10,
MicroHs 0.16.6.0): the shape of the numbers rather than a contract — they
move as the compiler and the checker are optimized, and the point of the
columns is the ratios between them, not the absolute values.

| Step | WASM (Node) | Native MicroHs | Native GHC |
|---|---|---|---|
| Instantiate + `mhs_init()` | ~30 ms | — | — |
| Load and parse the standard library | ~3 s | ~0.7 s | ~0.02 s |
| Reload a small program | ~0.3 s | ~0.15 s | ~0.01 s |
| One query | ~75 ms | ~5 ms | ~0.1 ms |
| **First Typecheck** (builds the checker) | **~30 s** | ~7.5 s | ~0.2 s |
| Later Typechecks | ~13 s | ~4 s | ~0.07 s |

The page is usable about three seconds after the module loads. Type
checking is the expensive part for a different reason than one might
guess: the checker is itself a CHR program of ~900 procedures compiled
into the session before any program is checked (that is the ~30 s), and
running it costs ~13 s per call, because each check builds a fresh CHR
session over the checker and runs it to quiescence. Hence the button,
and hence the page saying what it is doing before going quiet.

MicroHs-compiled code is roughly an order of magnitude slower than the
GHC-built compiler, and the browser adds a factor of about three on top
of the native MicroHs build; the columns above are the honest
consequence, measured on one AMD64 machine.

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
| `ychr_pg_init` | resource root (`/`) | load `libraries/` and `typechecker/`, parse the standard library |
| `ychr_pg_compile` | program text | reload; never type-checks |
| `ychr_pg_query` | one REPL line | run a goal or colon command |
| `ychr_pg_check` | — | type-check what is loaded, building the checker on first call |
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
| `playground/build/` | generated bundle (gitignored) |
| `test/playground/` | the native and WASM test suites, with their shared expectations |

## Limits

- One program at a time, compiled from a single buffer; `:- use_module`
  of the bundled libraries works, importing files from disk does not.
- One-shot queries only. A live session (the terminal REPL's `:begin`)
  would need the session environment to be held across calls, which the
  bridge does not do yet.
- The editor is a `textarea`: no syntax highlighting, completion or
  diagnostics in place.
- Long compiles block the page. The status line is painted before the
  call, but the browser cannot repaint while the WASM runs; a Web Worker
  would fix that.
- The whole type checker is compiled on first use (about 30 s), and each
  check runs in a fresh CHR session over it (about 13 s). Embedding a
  precompiled `typechecker.vm` (the VM program has a serializer) would
  remove the first cost; caching the session would remove the second.
