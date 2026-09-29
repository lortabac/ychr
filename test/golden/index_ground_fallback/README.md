# index_ground_fallback

The store's per-argument indexes (the paper's *Indexing* optimization,
`YCHR.Internal.Runtime.Index`) narrow a partner lookup to the suspensions
whose value at the looked-up argument position can match, and the
per-candidate condition check then decides. Narrowing is only allowed to
be a *superset* of the matches, which the goals here exercise on the two
cases where that is hard: a suspension stored while the indexed argument
was still an unbound variable, and a lookup keyed by a ground compound.

`step` reads its `q` partner through the repeated head variable `X`, which
the compiler lifts into a `Foreach` index condition on `q`'s first
argument. What the store does with it depends entirely on when `q` was
stored:

- `run` — `q(X, 1)` is stored with `X` unbound, so it lands in the
  position's non-ground fallback set and *stays there*: binding `X = 1`
  afterwards does not re-file it, because the index is written once, at
  store time. `p(1)`'s lookup is for the ground key `1`, so it must
  consult the fallback set as well as the key's bucket. An index that
  only consulted buckets would miss the partner, `step` would not fire,
  `done/1` would never be told and `R` would stay unbound.

- `sample` — the same rule with `q(2, 2)` stored ground, so the lookup is
  answered from the key bucket.

- `compound` — `q([1, 2], 7)` stored ground, so the lookup is keyed by a
  ground *compound*. Key equality has to be structural, because that is
  what ask-equality (`equal`) is over terms; a key that compared terms by
  identity would file this suspension under a bucket no lookup could
  reach.

The goals tell fifteen padding `q/2` suspensions first, so that the
target `q` is the store that takes the `q` bucket past `indexThreshold` —
the index is built on demand, and below that threshold the lookup is the
plain scan, which would exercise nothing. The count is one less than the
threshold and has to be kept in step with it. What this directory
therefore pins down is that the indexed path is *correct*, not that it is
taken: the index may narrow a lookup but never change its answer, so no
golden test can tell the two apart from the outside.
`test/YCHR/Runtime/IndexTest.hs` is where the candidate lists themselves
are checked, and `scheme/test/test-index.scm` is its Scheme counterpart.

All three goals are also run through the Scheme backend by the Scheme
harness. Both runtimes implement the index with the same threshold, so
these goals exercise the indexed path on either backend; what they check
is that the answer does not depend on it — the expected bindings are the
same on both.
