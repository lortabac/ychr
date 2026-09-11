# What Is CHR?

## Origins

Thom Frühwirth introduced Constraint Handling Rules in the early 1990s
as a language for writing *constraint solvers*. Instead of hand-coding
propagation and fixpoint logic in the host, you state it as rules and
the runtime does the rest.

CHR is *committed-choice*: a firing is never undone. That is why it
runs on hosts with no search built in, and why it compiles to ordinary
procedural code.

It has since become a general-purpose rule language. It is
Turing-complete, and any algorithm can be written in it with its
expected time and space complexity — rare among rule-based languages.

## The whole language in one idea

The only state is a multiset of constraints, the *store*. A program is
a set of rules that rewrite it. Rules fire until none can; what is left
is the answer. Euclid's algorithm
([`examples/gcd.chr`](../../examples/gcd.chr)):

```prolog
:- module(gcd, [gcd/1]).
:- chr_constraint gcd/1.

zero     @ gcd(0) <=> true.
subtract @ gcd(N) \ gcd(M) <=> M >= N, N > 0 | gcd(M - N).
```

```ychr-repl
ychr> :begin
ychr live> gcd(12).
ychr live> gcd(8).
ychr live> print_store.
gcd:gcd(4)
ychr live> :end
ychr>
```

(`:begin` opens a live session, where the store persists between
inputs — see the [REPL reference](../reference/repl.md).)

No loop, no accumulator, no base-case plumbing. "Zero is not an
answer"; "given two, replace the larger by the difference". The
runtime decides when and how often to apply them.

## What CHR is good at

Problems that are naturally *facts plus rules that combine them*:

- **Constraint solvers.** The original use, still the best fit:
  intervals, finite domains, union-find, Gaussian elimination.
- **Type inference.** Type checking is constraint solving. YCHR's own
  checker is a CHR program, and the
  [embedding guide](../how-to/embed-a-chr-module.md) builds a
  lambda-calculus inferencer.
- **Incremental algorithms.** Adding a fact re-triggers only the work
  it affects.
- **Business rules.** Rules that come from a spec, change often, and
  must stay readable to non-programmers.
- **Multiset rewriting.** "Keep applying these transformations until
  nothing changes."

Poor fit: problems that want *search* (CHR commits and never
backtracks; YCHR adds search as an opt-in
[library](../reference/search.md)), and straight-line computation, where
a function is simpler.

## How it relates to other paradigms

**Prolog** is backward-chaining with backtracking; CHR is
forward-chaining and never backtracks. The two are complements, which is
why CHR was first embedded in Prolog. YCHR keeps Prolog's syntax and
logical variables, not its search.

**Production-rule systems** (OPS5, Rete engines like Drools) are also
forward-chaining over a working memory. CHR differs in three ways:
removing a constraint is a first-class act, not a side effect; it has a
declarative semantics with a confluence and termination theory; and its
propagation history is part of the language, not a conflict-resolution
heuristic.

**Term-rewriting systems** rewrite one term toward a normal form. CHR
rewrites a multiset, and one head matches several constraints at once,
as `subtract` does. Multi-headed matching is what makes CHR hard to
compile well.

## Why compile CHR

Executed naively, every step is a join over the store: for each rule,
find a combination of constraints matching its head.

The refined operational semantics (ωr) is deterministic enough to
compile: each constraint becomes a procedure, each head occurrence a
nested loop over candidate partners, and the program becomes procedural
code with no matching engine at run time. Van Weert, Wuille, Schrijvers
and Demoen worked this out for imperative hosts, with a catalogue of
optimizations; YCHR implements that scheme.

A compiled program needs only logical variables, a store, and a
propagation history from its host. That is what makes a Scheme or
JavaScript backend possible, and what lets YCHR be an ordinary Haskell
library instead of a language to move your whole program into.

## See also

- [CHR primer](../tutorials/02-chr-primer.md) — hands-on intro to the
  three rule kinds.
- Reference paper: `dev-docs/chr-for-imperative-host-languages.pdf`.
- Frühwirth, T. *Constraint Handling Rules*. Cambridge University Press,
  2009.
