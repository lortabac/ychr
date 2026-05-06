# Haskell Style Guide

This guide documents the Haskell conventions used in YCHR. It mostly codifies
practices already universal in `src/`; treat the rules as defaults with
rationale, not as obligations. Deviating is fine when there's a reason — but
the reason should be explicit (a comment, a `Note`, a commit message).

For project architecture, see `PROJECT.md`. For formatting, see the Reminders
section of `CLAUDE.md` (`ormolu -i $(find src test -name '*.hs')`).

## Simplicity over cleverness

Prefer direct, easy-to-read code over abstractions that pay off only in
hypothetical futures. If DRY would make a piece of code substantially harder to
follow, accept some duplication. If achieving full type safety requires types
that obscure intent, give up some safety in exchange for clarity.

The yardstick is whether a reader new to the module can follow the code without
chasing several layers of indirection. Three similar lines side by side beat a
clever combinator that nobody will reach for again.

## Named, unique data types

Prefer `newtype` over naked types for identifiers and semantic scalars.
Examples in the codebase: `ConstraintType`, `RuleId`, `Name`, `Label`,
`OccurrenceNumber`, `HeadPosition`, `PartnerIndex`. The wrapping costs nothing
at runtime and turns a slip like passing a head position where an occurrence
number is expected into a type error.

Prefer records over tuples for product types. Field names act as inline
documentation, and adding a field later doesn't break call sites that pattern
match on shape. Tuples are reasonable for genuinely structural pairs (e.g., a
local zip), not for domain values.

## Records use bare field names

`OverloadedRecordDot`, `NoFieldSelectors`, and `DuplicateRecordFields` are
enabled globally in `ychr.cabal`. Field names are bare and unprefixed; access
is via `x.field`. Two records in the same module can share a field name;
that's the whole point of the extension trio.

Do not prefix field names with an abbreviation of the type (e.g. `cArgs`).

## Track effects with `effectful`

Use `effectful` wherever it makes the side-effect surface clearer — there's no
rule confining it to the runtime. A pass that accumulates diagnostics, threads
a counter, or talks to mutable state is usually clearer with a dedicated effect
than with a hand-rolled monad transformer stack.

Define new effects following the pattern in `src/YCHR/Runtime/Store.hs`:

```haskell
data CHRStore :: Effect
type instance DispatchOf CHRStore = Static WithSideEffects
```

Keep effect rows narrow: a function should only list the effects it actually
uses. If a function is genuinely pure, leave it pure — wrapping pure
computations in `Eff` for uniformity adds noise without payoff.

## Errors as data

Each compilation pass defines its own error ADT — `ParseValidationError`,
`RenameError`, `DesugarError`, `CompileError`, and so on. Failures are reported
through `Either` or effectful's `Error` effect, never thrown as exceptions.
This keeps the type signature honest about what a pass can return and lets
callers handle errors structurally.

Reserve exceptions (and `error`) for genuinely unexpected runtime failures —
broken invariants, impossible cases — not for predictable user-facing
problems.

## Documentation

Every public definition gets a Haddock `-- |` comment explaining what it is
and, where non-obvious, why it exists. Comments should explain rationale and
constraints; don't restate what the type signature already says.

For decisions that span multiple definitions, use GHC-style notes:

```haskell
{- Note [Reactivation queue ordering]

The reactivation queue is FIFO so that constraints affected by the same
`Unify` are dispatched in the order they were registered as observers...
-}
```

Anchor a `Note [Title]` in one module and reference it from others:

```haskell
-- See Note [Reactivation queue ordering] in YCHR.Runtime.Reactivation.
```

This keeps long-form rationale in one place and avoids the same paragraph
drifting out of sync across modules.

## Module hygiene

Every module has an explicit export list. Organize exports and internal
helpers with Haddock section comments (`-- * Types`, `-- * Operations`,
`-- * Internal`). The export list is the module's public contract; reading it
should answer "what does this module offer" without scrolling the body.

Use qualified imports for container and utility modules:

```haskell
import Data.IntMap.Strict qualified as IntMap
import Data.Sequence qualified as Seq
import Data.Text qualified as Text
```

Open imports are reserved for modules whose names are part of the codebase's
shared vocabulary (the project's own AST modules, `Effectful`, etc.).

## Mind compilation times

Avoid features that pay a large compile-time cost unless the payoff is clear.
`Generic` and `DeriveGeneric` are absent from `src/` for this reason; reach
for explicit instances or small helper functions instead.

`TypeFamilies` is the standard way to declare an effect's dispatch
(`type instance DispatchOf E = Static WithSideEffects`) — that use is fine
and won't show up in profiles. Avoid type families in domain logic, where the
same problem usually has a simpler solution with ordinary data types.

Template Haskell is allowed where it genuinely earns its keep (the type
checker uses it), but treat it as a last resort.

## Formatting

`ormolu` is the canonical formatter, with default settings. Run it before
committing:

```
ormolu -i $(find src test -name '*.hs')
```

This is also listed in `CLAUDE.md` alongside the test and benchmark commands.

Keep lines to roughly 90 characters or fewer. `ormolu` does not enforce a hard
limit, so this is on the author: break long expressions, signatures, and
comments before they wrap. The only acceptable exception is an unusually long
literal (a URL, a fixture string, a generated identifier) that cannot be split
without harming readability.
