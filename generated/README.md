# Generated resources

This directory holds the precomputed bundled resources the MicroHs
`ychr` executable runs on: the decoded standard library and the decoded
type-checker, emitted as literal Haskell data by `ychr-codegen`.

Nothing here is committed. Regenerate it with:

```
make resources
```

and check that an existing tree is current with:

```
make resources-check
```

Both targets need the repository's Makefile. From an sdist, which has
none, run the generator directly instead:

```
cabal run ychr-codegen -- --root . --out generated
```

The generated modules are listed in `exe:ychr`'s `other-modules` and
`autogen-modules` under `if impl(mhs)`, so `mcabal build` compiles them
and a plain GHC `cabal build` never looks at them. The `README.md` you
are reading exists so that the directory itself is always present: Cabal
rejects an `hs-source-dirs` entry that names a missing directory, even
one inside a conditional for another compiler
(`dev-docs/MICROHS_PERFORMANCE.md`, option B).
