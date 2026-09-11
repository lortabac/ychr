# Documentation Conventions

Author-facing conventions for the user documentation under `docs/`.

## Code fences

CHR source is fenced `prolog`; interactive REPL sessions are fenced
`ychr-repl`. Blocks that are neither — grammars, inference rules,
generated VM s-expressions, shell output — carry no info-string or the
obvious one (`sh`, `scheme`, `haskell`).

## REPL transcripts

The REPL uses two prompts:

- `ychr> ` — normal mode.
- `ychr live> ` — inside a `:begin … :end` live session, where the
  constraint store persists between inputs.

Both prompts appear in transcripts. Every output line is copied
verbatim from a real REPL run; nothing is paraphrased or guessed.

```
ychr> :begin
ychr live> egg.
ychr live> egg.
ychr live> print_store.
bakery:egg
bakery:egg
ychr live> :end
ychr>
```

A test harness that executes these fences will land later. Until then,
the convention is the contract.

## Examples

Runnable, self-contained programs that the docs reference live under
[`../examples/`](../examples/) at the repo root, with a
`% Used by docs/...` header comment. They are pedagogical, not
regression tests — for edge cases see `test/golden/`.
