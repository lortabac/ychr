PYTEST ?= python3 -m pytest
GUILE ?= guile3.0

.PHONY: test test-haskell test-scheme test-scheme-runtime test-repl test-typecheck test-docs test-style bench build install format clean

build:
	cabal build

install:
	cabal install --overwrite-policy=always

test: test-haskell test-scheme-runtime test-scheme test-repl test-typecheck test-docs test-style

test-haskell: build
	cabal test

test-scheme: build
	$(PYTEST) test/scheme/ -v

test-scheme-runtime:
	cd scheme/test && $(GUILE) -L .. -x .sls run-all.scm

test-repl: build
	$(PYTEST) test/repl/ -v

test-typecheck: build
	$(PYTEST) test/typecheck/ -v

test-docs:
	$(PYTEST) test/docs/ -v

test-style:
	$(PYTEST) test/style/ -v

bench: build
	cabal bench

format:
	ormolu -i $$(find src app -name '*.hs')

clean:
	cabal clean
