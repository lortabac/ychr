PYTEST ?= python3 -m pytest
# Prefer the Fedora binary name, fall back to Debian/Ubuntu's.
GUILE ?= $(shell command -v guile3.0 >/dev/null 2>&1 && echo guile3.0 || echo guile-3.0)
# Chez Scheme, used only by `bench-scheme-chez` (the test suite runs on
# Guile). `scheme` is the Chez binary name on a typical install; override
# it if a different Scheme owns that name.
CHEZ ?= scheme

.PHONY: test test-haskell test-scheme test-scheme-runtime test-repl test-stlc
.PHONY: test-typecheck test-docs test-style
.PHONY: bench bench-haskell bench-scheme bench-scheme-chez bench-scheme-all
.PHONY: scheme-bench-compile
.PHONY: build install format clean coverage

build:
	cabal build

install:
	cabal install --overwrite-policy=always

test: test-haskell test-scheme-runtime test-scheme test-repl test-stlc test-typecheck test-docs test-style

test-haskell: build
	cabal test

test-scheme: build
	GUILE=$(GUILE) $(PYTEST) test/scheme/ -v

test-scheme-runtime:
	cd scheme/test && $(GUILE) -L .. -x .sls run-all.scm

test-repl: build
	$(PYTEST) test/repl/ -v

test-stlc: build
	$(PYTEST) test/stlc/ -v

test-typecheck: build
	$(PYTEST) test/typecheck/ -v

test-docs:
	$(PYTEST) test/docs/ -v

test-style:
	$(PYTEST) test/style/ -v

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
SCHEME_BENCH_DIR ?= dist-scheme-bench
SCHEME_BENCH_ARGS ?=

SCHEME_BENCH_CASES = \
	bench_guard:test/golden/guard/guard.chr \
	bench_graph:test/golden/graph_test/graph_test.chr \
	bench_fib:test/golden/fib/fib.chr \
	bench_leqc:test/golden/leq_closure/leq_closure.chr \
	bench_list:bench/scheme/bench_list.chr \
	bench_maplist:bench/scheme/bench_maplist.chr

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

coverage:
	cabal test --enable-coverage
	@echo
	@echo "Coverage HTML report:"
	@find dist-newstyle -path '*/hpc/vanilla/html/hpc_index.html' -print -quit

format:
	ormolu -i $$(find src embed app test bench examples -name '*.hs')

clean:
	cabal clean
	rm -rf $(SCHEME_BENCH_DIR)
