# Project: YCHR

## Project description

An efficient CHR compiler with multiple backends.
See @dev-docs/PROJECT.md

## Resources

- `dev-docs/` contains contributor-oriented documentation:
  `PROJECT.md` (architecture and design) and the paper
  this compiler is based on.
- `docs/` contains user-facing documentation: language
  reference, VM specification, type system specification,
  and roadmap.

## Formatting

After a task is completed, format the whole code base with
`ormolu -i $(find src test -name '*.hs')`.
