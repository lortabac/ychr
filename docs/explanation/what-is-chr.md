# What Is CHR?

> **Audience:** readers who want background and context, not a how-to.
> **You will:** learn where Constraint Handling Rules came from, what it
> is good at, how it differs from neighbouring paradigms, and why it is
> worth compiling.
> **Skip if:** you want to start writing programs — go to the
> [CHR primer](../tutorials/02-chr-primer.md) instead.

## Origins

Constraint Handling Rules was introduced by Thom Frühwirth in the early
1990s. The original purpose was narrow: a high-level language for writing
*constraint solvers*. If you wanted your Prolog system to understand a new
constraint domain — intervals, finite domains, a lattice of your own — you
had to write the propagation and simplification logic by hand, in the host
language, and get the fixpoint behaviour right yourself. CHR let you state
that logic as rules and let the runtime handle the rest.

It was designed as a *committed-choice* language: when a rule fires, the
choice is final, with no backtracking. That single decision is why CHR sits
comfortably on top of hosts that have no search built in, and it is what
makes CHR compilable to ordinary procedural code.

CHR has since outgrown its origin as a solver-writing tool and is used as a
general-purpose rule-based language. It is Turing-complete, and any
algorithm can be implemented in it with the expected time and space
complexity — a property most rule-based languages do not have.

## The whole language in one idea

A CHR program's only state is a multiset of constraints, the *store*.
A program is a set of rules that rewrite that store. Rules fire until none
can fire any more, and whatever is left in the store is the answer.

That is the whole model. Here is Euclid's algorithm
([`examples/gcd.chr`](../../examples/gcd.chr)):

```prolog
:- module(gcd, [gcd/1]).
:- chr_constraint gcd/1.

zero     @ gcd(0) <=> true.
subtract @ gcd(N) \ gcd(M) <=> M >= N, N > 0 | gcd(M - N).
```

Put `gcd(12)` and `gcd(8)` in the store and the rules grind them together
until one number remains:

```ychr-repl
ychr> :begin
ychr live> gcd(12).
ychr live> gcd(8).
ychr live> print_store.
gcd:gcd(4)
ychr live> :end
ychr>
```

(`:begin` opens a live session, in which the store persists between
inputs — see the [REPL reference](../reference/repl.md).)

No loop, no recursion, no accumulator, no base-case plumbing. The first
rule says "zero is not an answer, drop it"; the second says "if you have
two of these, replace the larger with their difference". The runtime
works out when and how often to apply them.

## What CHR is good at

CHR fits wherever the problem is naturally stated as *facts plus rules
that combine them*.

- **Constraint solvers.** The original use case, still the best fit.
  Interval propagation, finite-domain solving, union-find, Gaussian
  elimination — all are a handful of rules.
- **Type inference.** Type checking is constraint solving. YCHR's own type
  checker is a CHR program, and the
  [embedding guide](../how-to/embed-a-chr-module.md) walks through a
  lambda-calculus type inferencer written this way.
- **Incremental algorithms.** Because rules react to what is in the store,
  adding a fact re-triggers only the work that fact affects. Recomputing
  from scratch is not required.
- **Business rules and reasoning systems.** Domains where the rules come
  from a specification document and change often, and where you want them
  readable by someone who is not the programmer.
- **Multiset rewriting generally.** Anything you would otherwise express as
  "keep applying these transformations until nothing changes".

Where CHR is a poor fit: problems that want *search* (CHR commits and never
backtracks — that is the host's job), and straight-line computation with no
rule interaction, where an ordinary function is simpler.

## How it relates to other paradigms

**Prolog** is backward-chaining: it starts from a goal and works backwards
looking for facts that support it, backtracking on failure. CHR is
forward-chaining: it starts from the facts and pushes forward, and never
backtracks. The two are complements, which is why CHR was originally
embedded *in* Prolog rather than competing with it. YCHR keeps Prolog's
syntax and its logical variables, but not its search.

**Production-rule systems** (OPS5, Rete-based engines like Drools) are also
forward-chaining over a working memory, and the resemblance is real. The
differences that matter: CHR rules can *remove* constraints as a
first-class act, not merely as a side effect; CHR has a formal declarative
semantics and well-studied confluence and termination theory; and CHR's
propagation history is part of the language definition rather than a
conflict-resolution heuristic.

**Term-rewriting systems** rewrite a single term toward a normal form. CHR
rewrites a *multiset*, and a rule head can match several constraints at
once — which is exactly what the `gcd` rule above relies on. That
multi-headed matching is CHR's distinguishing feature and the main source
of difficulty in compiling it well.

## Why compile CHR

CHR is usually run by an interpreter embedded in a host, and the naive
execution strategy is expensive: for each rule, look for a combination of
stored constraints matching its head. Done literally, that is a join over
the store on every step.

The refined operational semantics (ωr) makes execution deterministic enough
to compile properly: each constraint becomes a procedure, each occurrence
in a rule head becomes a nested loop over candidate partners, and the whole
program becomes ordinary procedural code with no rule-matching engine at
run time. Van Weert, Wuille, Schrijvers, and Demoen showed how to do this
for imperative hosts, together with a catalogue of optimizations that
remove most of the remaining overhead. That scheme is what YCHR implements.

Compiling rather than interpreting also means CHR does not need to live
inside Prolog. A compiled program needs only logical variables, a store,
and a propagation history from its host — which a dynamically-typed
procedural language can provide. That is what makes a Scheme or JavaScript
backend possible, and what lets YCHR act as an ordinary Haskell library
rather than a language you have to move your whole program into.

## See also

- Tutorial: [CHR primer](../tutorials/02-chr-primer.md) — quick, hands-on
  intro with the three rule kinds.
- [The refined operational semantics](operational-semantics.md) — precisely
  when a rule fires.
- [Design rationale](design-rationale.md) — why YCHR is built the way it is.
- Reference paper: `dev-docs/chr-for-imperative-host-languages.pdf`.
- Frühwirth, T. *Constraint Handling Rules*. Cambridge University Press,
  2009 — the definitive treatment.
