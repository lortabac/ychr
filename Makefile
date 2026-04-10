PYTEST ?= python3 -m pytest
GUILE ?= guile3.0

.PHONY: test test-haskell test-scheme test-scheme-runtime test-repl build install format clean

build:
	cabal build

install:
	cabal install --overwrite-policy=always

test: test-haskell test-scheme-runtime test-scheme test-repl

test-haskell: build
	cabal test

test-scheme: build
	$(PYTEST) test/scheme/ -v

test-scheme-runtime:
	cd scheme/test && $(GUILE) -L .. -x .sls run-all.scm

test-repl: build
	$(PYTEST) test/repl/ -v

format:
	ormolu -i $$(find src app -name '*.hs')

clean:
	cabal clean
