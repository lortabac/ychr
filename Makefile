PYTEST ?= python3 -m pytest

.PHONY: test test-haskell test-scheme build install format clean

build:
	cabal build

install:
	cabal install --overwrite-policy=always

test: test-haskell test-scheme

test-haskell: build
	cabal test

test-scheme: build
	$(PYTEST) test/scheme/ -v

format:
	ormolu -i $$(find src app -name '*.hs')

clean:
	cabal clean
