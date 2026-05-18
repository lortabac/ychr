# Agent-Driven QA

A QA mode in which an LLM agent stress-tests the language by writing
adversarial tests against the *documentation*, not the code. Automated
golden tests under `test/golden/` already cover the happy paths; this
mode exists to find the cases the spec author did not think about.

The agent reads `docs/`, treats every claim there as a contract, and
tries to break it. When it finds a divergence between the documented
behavior and what the implementation does, it **reports** the
divergence and stops. It does **not** patch the code, the docs, or the
test suite. Deciding whether a failure is an implementation bug, a
documentation gap, or an ambiguity in the spec is reserved for the
human reviewer.

## How to invoke

Hand an agent the prompt below (paraphrasing is fine):

> Perform an agent-driven QA pass on YCHR. Read everything under
> `docs/` and treat each documented claim as a contract. Construct a
> handful of *edge-case* tests that try to falsify those contracts —
> not happy paths. Use the `ychr` CLI to run them. Report every
> divergence you find; do not fix anything. See
> `dev-docs/AGENT_DRIVEN_QA.md` for the full protocol.

The agent should run for as long as it can productively generate
*new* edge cases. Quality beats quantity: ten genuinely tricky tests
that exercise interactions across features are worth far more than a
hundred minor variations on the tutorials.

## Reading list

In rough priority order:

1. `docs/reference/language.md` — feature-level reference.
2. `docs/reference/syntax.md` — lexical and grammatical rules.
3. `docs/reference/type-system.md` — gradual type-system spec.
4. `docs/reference/prelude.md` — built-in functions and constraints.
5. `docs/reference/repl.md` and `docs/reference/cli.md` — invocation
   surface.
6. `docs/reference/errors.md` — promised diagnostics.
7. `docs/how-to/*.md` and `docs/explanation/*.md` — secondary claims,
   often more specific than the reference.
8. `docs/tutorials/*.md` — only as a quick map of features; tutorials
   describe happy paths and are not the test target.

Skim `examples/` and `test/golden/` to learn the *idiom* but not for
test ideas — those are the cases that already pass. Look in
`dev-docs/BUGS.md` and `dev-docs/SCHEME_BACKEND_GAPS.md` so you do not
re-report known issues.

## What to test

Aim adversarially. Promising categories:

- **Boundary conditions.** Empty modules, single-rule programs with
  no body, zero-arity constraints, zero-arity functions, lambdas with
  no parameters, very long argument lists, deeply nested compound
  terms, large integers near host limits.
- **Interactions between features.** A lambda that closes over a
  logical variable that later gets unified; a polymorphic
  `requiring`-bounded function called with a partially-bound term; an
  `extend_function` whose equation pattern shadows an earlier one;
  a `'$call'` whose target is itself the result of a `'$call'`.
- **Module boundaries.** Qualified vs unqualified names; importing a
  module that re-exports another; `extend_class` /
  `extend_function` from a third module; constraint visibility
  across module hops; collisions between an imported function and a
  local constructor of the same name.
- **Tell-side evaluation.** Compound arguments in rule bodies and
  top-level goals are *evaluated* — exercise the boundary between
  evaluated expressions and quoted `term(...)` forms, especially when
  variables are still unbound at tell time (should be a runtime
  error, per `PROJECT.md`).
- **Guard vs body semantics.** `==` (ask) and `=` (tell) must not be
  interchangeable; build cases that fail only if one is silently
  substituted for the other.
- **Reactivation.** Construct programs where a unification fires a
  later rule only if the reactivation queue is drained in the
  documented order.
- **Error codes.** For every `YCHR-NNNNN` code mentioned in
  `docs/reference/errors.md` or `PROJECT.md`, build the smallest
  program that should provoke it, and confirm the actual diagnostic
  matches. Wrong code, missing code, or a successful compile when an
  error was promised all count as divergences.
- **REPL contracts.** The REPL prompt strings (`ychr> ` vs
  `ychr live> `), the `--quiet` and `--Werror` flag behaviors, and
  the `:begin … :end` store-persistence contract are all documented.
- **CLI contracts.** `ychr run` accepts exactly one goal; `ychr
  check` exits silently on success; `--Werror` interactions with
  `--quiet`. Each is a claim that can be falsified.
- **Backend parity.** When the Haskell and Scheme backends both
  support a feature, run the same program through each and compare —
  but consult `SCHEME_BACKEND_GAPS.md` first to filter known gaps.

Bias toward **multi-module, multi-feature** scenarios. A test that
combines `open_class` extension, bounded polymorphism, a lambda, and
a reactivation across two modules is much more likely to surface a
real issue than ten one-liners.

## Workflow

1. **Build once.**

   ```sh
   make build
   ```

   Use the installed `ychr` from `$PATH`. If invocation looks stale,
   `make install` and try again.

2. **Work in a scratch directory.** Create one per session and put
   every generated `.chr` file there. Do not commit anything; do not
   edit files inside `src/`, `test/`, `docs/`, `dev-docs/`, or
   `examples/`.

   ```sh
   SCRATCH=$(mktemp -d -t ychr-qa.XXXX)
   ```

3. **Run tests through the CLI.** The primary tools are:

   - `ychr check FILES…` for static checks (type errors, name
     resolution, declaration-kind validation).
   - `ychr run -g 'GOAL' FILES…` (with `--show-bindings` when
     binding output is the assertion).
   - `ychr repl FILES…` for interactive scenarios — feed input via a
     here-doc when scripting.

   Multi-file programs: pass every `.chr` file as an argument to one
   invocation; goals are module-qualified.

   `ychr run` accepts a **single** goal. To chain steps, wrap them in
   a helper constraint whose body posts the rest, or use a REPL live
   session.

4. **Compare against the spec, not against intuition.** Every
   reported divergence must cite the documented claim it falsifies —
   a file path and, where possible, a section heading or quoted line.

5. **Cross-check before reporting.** If the result looks wrong, try
   two or three variations of the same scenario before flagging it.
   Many surprises come from a misread of the spec, not from a bug.

## Report format

Emit one Markdown report per session, structured as follows. Keep
each finding self-contained so the human reviewer can triage without
context from the rest of the report.

```markdown
# Agent-Driven QA Report — YYYY-MM-DD

Sessions: <one-line summary of areas exercised>
Findings: <count>

## Finding 1 — <short title>

**Documented claim.** <quote or close paraphrase, with file:section
or file:line>.

**Test.** What the test does, in one or two sentences.

    <minimal .chr program, inline>

    Goal: <goal expression>

**Expected.** <what the doc says should happen>

**Actual.** <copy-pasted output, including any error codes>

**Notes.** Anything that helps triage: variations tried, related
findings, suspected interaction.
```

If the agent finds *nothing* in a given area after a serious attempt,
say so — a clean negative result on a tricky corner is useful
information.

## Hard constraints

- **Do not modify the repo.** No edits to source, docs, tests, the
  example directory, or settings files. Scratch files live outside
  the tree.
- **Do not fix anything.** Even if the fix looks one-line obvious.
- **Do not file issues, PRs, or commits.** The report is the
  deliverable.
- **Do not invent test infrastructure.** No new golden-test
  directories, no new pytest files. Use the CLI directly.
- **Do not assume.** If the spec is silent on a corner, that is a
  finding ("spec silent on X; implementation does Y") — not a license
  to guess what the spec "must have meant."
- **Do not chase known issues.** Cross-check `dev-docs/BUGS.md` and
  `dev-docs/SCHEME_BACKEND_GAPS.md` before reporting.

## When in doubt

If a result is ambiguous — for example, the spec genuinely admits
two readings, or the diagnostic is *almost* the promised one but
with a different code — report it as a finding and tag it
`ambiguous`. Triage is the reviewer's job; the agent's job is to
surface the question.
