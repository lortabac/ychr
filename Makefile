PYTEST_PY ?= python3
PYTEST ?= $(PYTEST_PY) -m pytest
# Prefer the Fedora binary name, fall back to Debian/Ubuntu's.
GUILE ?= $(shell command -v guile3.0 >/dev/null 2>&1 && echo guile3.0 || echo guile-3.0)
# Chez Scheme, used only by `bench-scheme-chez` (the test suite runs on
# Guile). `scheme` is the Chez binary name on a typical install; override
# it if a different Scheme owns that name.
CHEZ ?= scheme

# The nine test suites are independent; `test` overlaps them by default.
# JOBS=1 restores the ordered, sequential behaviour. (The Haskell suite is
# also threaded with Tasty on all cores — see ychr.cabal; its tests are
# independent and mutate no process-global state, so keep new tests free
# of cwd, environment and handle changes.) `$(or …)` keeps an empty JOBS
# from turning the recipe's `-j` into "no limit".
JOBS ?= $(shell nproc 2>/dev/null || echo 1)

# pytest-xdist is optional: when the interpreter running pytest can import
# it, the subprocess-heavy suites are sharded across worker processes.
# Override PYTEST_XDIST= to force it off, or set a worker count explicitly
# (e.g. PYTEST_XDIST='-n 8'). Probed through PYTEST_PY so it matches the
# interpreter PYTEST uses.
PYTEST_XDIST ?= $(shell $(PYTEST_PY) -c 'import xdist' 2>/dev/null && printf '%s' '-n auto')

.PHONY: test test-haskell test-scheme test-scheme-runtime test-repl test-stlc
.PHONY: test-typecheck test-docs test-style test-playground playground-check
.PHONY: bench bench-haskell bench-scheme bench-scheme-chez bench-scheme-all
.PHONY: scheme-bench-compile
.PHONY: playground-emsdk playground-wasm playground-serve
.PHONY: resources resources-check mhs-build mhs-install
.PHONY: build install format clean coverage

# ---------------------------------------------------------------------------
# Web playground (MicroHs -> WASM)
#
# `make playground-wasm` compiles the ychr library together with the bridge
# in playground/ to JavaScript and WebAssembly through MicroHs and
# emscripten, with libraries/ and typechecker/ preloaded into the module's
# file system. `make playground-serve` then serves playground/ as a static
# site. See docs/how-to/web-playground.md.
#
# Emscripten is the only toolchain MicroHs can emit WASM with (it shells out
# to a C compiler; there is no pure-JavaScript backend), and it is not
# vendored here, so `playground-emsdk` fetches it into .emsdk/ — gitignored,
# and only needed by the targets below.
# ---------------------------------------------------------------------------
PLAYGROUND_DIR = playground
PLAYGROUND_BUILD = $(PLAYGROUND_DIR)/build
EMSDK ?= $(CURDIR)/.emsdk
EMSDK_VERSION ?= 6.0.10
# The MicroHs compiler whose data directory holds mhs.conf and src/runtime.
# `mhs` on PATH is the installed one (~/.mcabal/bin/mhs); override to point
# at a checkout's bin/mhs.
MHS ?= mhs
# `mcabal`, the MicroHs build front end, used only by `make mhs-build`.
MCABAL ?= mcabal
# -sINVOKE_RUN=0: main never runs; JavaScript calls mhs_init() and then the
# exported functions, which is the flow MicroHs's own tests/ForExp.hs uses.
PLAYGROUND_EMCCFLAGS ?= \
	-O2 \
	-sMODULARIZE=1 \
	-sEXPORT_NAME=createYchr \
	-sINVOKE_RUN=0 \
	-sALLOW_MEMORY_GROWTH=1 \
	-sENVIRONMENT=web,node \
	-sFORCE_FILESYSTEM=1 \
	-sEXPORTED_FUNCTIONS=_mhs_init,_malloc,_free,_ychr_pg_init,_ychr_pg_compile,_ychr_pg_query,_ychr_pg_check,_ychr_pg_free \
	-sEXPORTED_RUNTIME_METHODS=stringToNewUTF8,UTF8ToString

build:
	cabal build

install:
	cabal install --overwrite-policy=always

# ---------------------------------------------------------------------------
# Generated resources (MicroHs)
#
# `make resources` runs ychr-codegen, which decodes libraries/*.chr and
# typechecker/*.chr once and writes them as literal Haskell modules under
# generated/ (gitignored). The MicroHs executable compiles those instead
# of re-parsing the standard library and re-compiling the type-checker in
# every process; a GHC build never looks at them. `--check` re-emits in
# memory and reports a stale or missing tree without rewriting it. See
# dev-docs/MICROHS_PERFORMANCE.md, option B, and generated/README.md.
#
# The generator is resolved like YCHR in the Scheme benchmark: only after
# `build`, because `cabal list-bin` needs the component to exist.
# ---------------------------------------------------------------------------
GENERATED_DIR ?= generated
GENERATED_MODULES = $(GENERATED_DIR)/YCHR/Embedded/Generated/StdLib.hs \
                  $(GENERATED_DIR)/YCHR/Embedded/Generated/TypeCheck.hs

resources: build
	@test -n "$$(cabal list-bin ychr-codegen 2>/dev/null)" || { \
	  echo "cannot resolve ychr-codegen; run 'cabal build' first" >&2; \
	  exit 1; }
	$$(cabal list-bin ychr-codegen) --root . --out $(GENERATED_DIR)

# Also parses and typechecks the generated modules with GHC: they are
# only ever compiled by MicroHs in a normal build, so nothing else would
# catch an emitter change that produces Haskell MicroHs happens to
# accept but GHC does not — or, more to the point, unparsable output.
resources-check: build
	@test -n "$$(cabal list-bin ychr-codegen 2>/dev/null)" || { \
	  echo "cannot resolve ychr-codegen; run 'cabal build' first" >&2; \
	  exit 1; }
	$$(cabal list-bin ychr-codegen) --root . --out $(GENERATED_DIR) --check
	cabal exec -- ghc -fno-code -i$(GENERATED_DIR) $(GENERATED_MODULES)

# ---------------------------------------------------------------------------
# MicroHs environment (pinned)
#
# ychr's MicroHs build needs an mhs/mcabal at a known revision and the
# packages ychr depends on, neither of which a MicroHs install ships.
# `make mhs-install` provides both, from the pins in
# tools/mhs-install.sh and the versions in tools/mhs-packages.txt; it is
# what CI runs before `make mhs-build`, so a developer who runs it and CI
# compile against the same environment. The script installs only while
# what it provides is not already in place, so a machine that is up to
# date runs it in no time.
#
# `make mhs-build` itself only compiles: nothing at build time reads the
# lock file, mcabal only checks that each dependency is installed. The
# package set is the subset of MicroHs's Makefile.packages that ychr
# needs, in that file's order (dependency order).
# https://github.com/augustss/MicroHs/blob/master/Makefile.packages
# ---------------------------------------------------------------------------
# The installation to provision. Override it, as a variable or from the
# environment, to install somewhere else: `make mhs-install
# MHS_HOME=/tmp/mhs`.
MHS_HOME ?= $(HOME)/.mcabal

mhs-install:
	@MHS_HOME="$(MHS_HOME)" tools/mhs-install.sh

# The documented MicroHs build order: regenerate, then compile. The
# toolchain and package set come from `make mhs-install`.
mhs-build: resources
	$(MCABAL) build

test:
	$(MAKE) -j$(or $(JOBS),1) test-haskell test-scheme-runtime test-scheme test-repl \
	  test-stlc test-typecheck test-docs test-style test-playground

test-haskell: build
	cabal test

test-scheme: build
	GUILE=$(GUILE) $(PYTEST) $(PYTEST_XDIST) test/scheme/ -v

test-scheme-runtime:
	cd scheme/test && $(GUILE) -L .. -x .sls run-all.scm

test-repl: build
	$(PYTEST) $(PYTEST_XDIST) test/repl/ -v

test-stlc: build
	$(PYTEST) test/stlc/ -v

test-typecheck: build
	$(PYTEST) $(PYTEST_XDIST) test/typecheck/ -v

test-docs:
	$(PYTEST) test/docs/ -v

test-style:
	$(PYTEST) test/style/ -v

# The native half of the playground suite always runs; the WASM half needs
# the module to have been built and `node`, and skips itself otherwise.
# `playground-check` is the full verification: build, then test.
test-playground: build
	$(PYTEST) test/playground/ -v

playground-check: playground-wasm test-playground

bench: bench-haskell bench-scheme

bench-haskell: build
	cabal bench

# ---------------------------------------------------------------------------
# Scheme backend benchmarks
#
# `bench-scheme` measures the generated code and the Scheme runtime under
# Guile 3, the implementation the test suite uses; `bench-scheme-chez`
# runs the same programs under Chez Scheme. Programs, sampling policy and
# reporting are shared (bench/scheme/bench/harness.sls) — only the clock
# differs (bench/scheme/run-guile.scm vs run-chez.scm). See
# dev-docs/BENCHMARKS.md.
#
# Each entry below is "<library-name>:<source .chr>". The library name is
# what `ychr compile -n` sets, and the harness imports it as
# (ychr generated <library-name>). The `bench_` prefix is not cosmetic: a
# generated library whose binding is named after the program can collide
# with an R6RS/core binding, and a library exporting `guard`, for one,
# refuses to load in Guile.
# ---------------------------------------------------------------------------
YCHR ?= $(shell cabal list-bin ychr 2>/dev/null)
# Export the resolved binary so recursive make and the pytest suites reuse
# it instead of each calling `cabal list-bin` while `cabal test` is running
# (the test fixtures fall back to `cabal list-bin` when this is empty).
export YCHR
SCHEME_BENCH_DIR ?= dist-scheme-bench
SCHEME_BENCH_ARGS ?=

SCHEME_BENCH_CASES = \
	bench_guard:test/golden/guard/guard.chr \
	bench_graph:test/golden/graph_test/graph_test.chr \
	bench_fib:test/golden/fib/fib.chr \
	bench_leqc:test/golden/leq_closure/leq_closure.chr \
	bench_list:bench/scheme/bench_list.chr \
	bench_maplist:bench/scheme/bench_maplist.chr \
	bench_sum:bench/scheme/bench_sum.chr

# Depends on `build`, so that resolving the binary and compiling the
# programs cannot race a concurrent `cabal build` under `make -j`.
scheme-bench-compile: build
	@test -n "$(YCHR)" || { \
	  echo "cannot resolve the ychr binary; run 'cabal build' or set YCHR" \
	       "(and CABAL_DIR, if that is how cabal is configured here)" >&2; \
	  exit 1; }
	rm -rf $(SCHEME_BENCH_DIR)
	@mkdir -p $(SCHEME_BENCH_DIR)
	@for c in $(SCHEME_BENCH_CASES); do \
	  name=$${c%%:*}; src=$${c#*:}; \
	  echo "  compile $$src -> (ychr generated $$name)"; \
	  $(YCHR) compile -t scheme -n $$name -d $(SCHEME_BENCH_DIR) $$src >/dev/null || exit 1; \
	done

bench-scheme: scheme-bench-compile
	$(GUILE) --r6rs --no-auto-compile \
	  -L $(CURDIR)/scheme -L $(CURDIR)/bench/scheme -L $(CURDIR)/$(SCHEME_BENCH_DIR) -x .sls \
	  bench/scheme/run-guile.scm $(SCHEME_BENCH_ARGS)

bench-scheme-chez: scheme-bench-compile
	$(CHEZ) --libdirs \
	  $(CURDIR)/bench/scheme:$(CURDIR)/scheme:$(CURDIR)/$(SCHEME_BENCH_DIR) \
	  --libexts .sls --program bench/scheme/run-chez.scm \
	  $(if $(SCHEME_BENCH_ARGS),-- $(SCHEME_BENCH_ARGS))

bench-scheme-all: bench-scheme bench-scheme-chez

# ---------------------------------------------------------------------------
# Web playground build
# ---------------------------------------------------------------------------

# The example programs the page's preset dropdown offers, by file name under
# examples/. The page is served from $(PLAYGROUND_DIR) alone, so the examples
# it offers have to be copied into the bundle; examples/ stays their source of
# truth.
PLAYGROUND_PRESETS = bakery.chr leq.chr fib_memo.chr gcd.chr

# Fetch and activate the emscripten SDK, pinned to $(EMSDK_VERSION). Idempotent.
playground-emsdk:
	@test -d $(EMSDK) || \
	  git clone --depth 1 https://github.com/emscripten-core/emsdk.git $(EMSDK)
	@cd $(EMSDK) && ./emsdk install $(EMSDK_VERSION) >/dev/null && \
	  ./emsdk activate $(EMSDK_VERSION) >/dev/null
	@echo "emscripten $(EMSDK_VERSION) ready in $(EMSDK)"

playground-wasm:
	@if ! command -v emcc >/dev/null 2>&1 && \
	    ! test -x $(EMSDK)/upstream/emscripten/emcc; then \
	  echo "emcc not found: run 'make playground-emsdk', or put emscripten on PATH" >&2; \
	  exit 1; \
	fi
	@command -v $(MHS) >/dev/null 2>&1 || { \
	  echo "the MicroHs compiler '$(MHS)' not found; set MHS=path/to/mhs" >&2; \
	  exit 1; \
	}
	@mkdir -p $(PLAYGROUND_BUILD)
	@cp examples/leq.chr $(PLAYGROUND_BUILD)/starter.chr
	@for name in $(PLAYGROUND_PRESETS); do \
	  echo "  preset $$name"; \
	  cp examples/$$name $(PLAYGROUND_BUILD)/$$name || exit 1; \
	done
	. $(EMSDK)/emsdk_env.sh >/dev/null 2>&1 || true; \
	CC=emcc MHSCONF=unix MHSCCLIBS=-lm MHSCCFLAGS="$(PLAYGROUND_EMCCFLAGS)" \
	$(MHS) -tenvironment -z \
	  -isrc -isrc/mhs -i$(PLAYGROUND_DIR) \
	  -optl --preload-file=libraries@/libraries \
	  -optl --preload-file=typechecker@/typechecker \
	  -o$(PLAYGROUND_BUILD)/ychr-pg.js YCHR.Playground.Wasm
	@echo "built $(PLAYGROUND_BUILD)/ychr-pg.js"

# Serve the page. The bundle is static, so any file server works; this one
# needs nothing but Python. Open http://localhost:8080/.
playground-serve:
	@echo "serving $(PLAYGROUND_DIR)/ at http://localhost:8080/ (Ctrl-C to stop)"
	python3 -m http.server 8080 --directory $(PLAYGROUND_DIR)

coverage:
	cabal test --enable-coverage
	@echo
	@echo "Coverage HTML report:"
	@find dist-newstyle -path '*/hpc/vanilla/html/hpc_index.html' -print -quit

format:
	ormolu -i $$(find src embed app codegen test bench examples playground -name '*.hs')

clean:
	cabal clean
	rm -rf $(GENERATED_DIR)/YCHR
	rm -rf $(SCHEME_BENCH_DIR)
