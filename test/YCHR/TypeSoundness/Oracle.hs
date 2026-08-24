{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | The oracle: what counts as a soundness violation, and why nothing
-- else can masquerade as one.
module YCHR.TypeSoundness.Oracle
  ( conforms,
    describeException,
    describeBad,
  )
where

import Control.Exception (SomeException, fromException)
import Data.Text (Text)
import Data.Text qualified as T
import YCHR.Internal.Display (Display (..))
import YCHR.Internal.Types (Name (..), Term (..))
import YCHR.Run (Error (..))
import YCHR.TypeSoundness.Observe (Bad (..))
import YCHR.TypeSoundness.Types

{- Note [Why benign failures are impossible]

The oracle is strict: any exception at all is a failure, and any
recorded observation that is not `Inhabits` is a violation. That is
only justified if the generated fragment cannot fail, or observe an
absent value, for a reason unrelated to soundness. The argument rests
on one invariant: every in-scope variable is ground.

  * Goal tells carry closed expressions, so the initial store is ground.
    Both producers keep that so: the free arguments come from
    `genExprRoot` under an empty environment, and the seeded ones from
    `patInstance`, whose holes are filled by `genClosedLeaf`.
  * Head matching therefore binds head variables to ground values.
  * `BIs` and `BUnify` bind a *fresh* variable from ground inputs;
    guards bind nothing.

From groundness the rest follows:

  * No evaluated position ever sees an unbound variable, so the
    "unbound variable in evaluated position" runtime error cannot fire,
    and no observation can come back `NotYetBound`. This is why an
    unbound observation is a *violation* here rather than the expected
    outcome it becomes once the generator stores unbound values on
    purpose (see `docs/reference/type-system.md` §No mode checking for
    the axis it belongs to).
  * `BUnify` cannot fail: its left-hand side is always a fresh variable,
    which unifies with anything. (Failed body unification *is* a runtime
    error — see `unifyOrError` in the interpreter — so this matters.)
  * Nothing observes an unbound variable, so no reactivation ever
    happens.
  * Every function a generated module can call is total. The preamble
    predicates are exhaustive, and of the prelude functions the
    generator emits — `+ - *`, `< > >= =<`, `==`, `not` — all are
    host-backed and total on the ground values reaching them.
    `div`/`mod` are excluded because they are partial, and `not/1` is
    only ever applied to a ground `bool`. So "no matching equation"
    cannot arise at all: it is not a signal the oracle has to
    interpret, it is a case that cannot occur.
  * No form in `Expr`/`STerm` can widen to `any`: no host calls, no
    `quote`, no undeclared constructors, no evaluable head under `=`,
    and never a bare-variable `is` right-hand side (which the spec
    widens to `any`).

The instrumentation itself introduces the one `host:` call in a
generated module, and it is total: it records and returns `true`, so it
can neither raise nor change the meaning of the guard it sits in. A
message beginning `host call ts_obs:` would mean the observer *did*
raise, which is a harness bug and is classified as a failure rather
than quietly tolerated.

What cannot masquerade as what:

  * A benign event cannot look like a violation: every family above is
    closed by construction, not by classification, so the oracle never
    has to decide whether a given crash was "expected".
  * A violation cannot look benign: the observer records rather than
    raises, so a violation is a datum in the log rather than the
    absence of one. Every branch of the property — normal return and
    exception alike — reads the log before deciding, so a violation is
    never lost to an unrelated failure, and always outranks it.
  * A violation cannot be lost to short-circuiting: the head
    observation is the *first* guard conjunct, so it runs for every
    candidate match that survived HNF's own match and equality guards,
    including the matches a user guard then rejects.
-}

-- | The name a runtime 'Term' carries, without its module. Answers come
-- back qualified (@gen:k0@, @prelude:[]@) or bare depending on how the
-- value was built, so only the final component is compared.
baseOf :: Name -> Text
baseOf n = case n of
  Unqualified t -> t
  Qualified _ t -> t

-- | Does a returned goal binding structurally inhabit its static type?
--
-- This is the Haskell-side half of the oracle. It is not subsumed by
-- the host observer: the observer sees values *inside* a run, and this
-- sees the bindings that come back *out* of one, which is the only
-- look at the goal's own results.
conforms :: Ty -> Term -> Bool
conforms ty t = case ty of
  TInt -> case t of
    IntTerm _ -> True
    _ -> False
  TBool -> case t of
    CompoundTerm n [] -> baseOf n == "true" || baseOf n == "false"
    _ -> False
  TListInt -> case t of
    CompoundTerm n [] -> baseOf n == "[]"
    CompoundTerm n [h, tl] ->
      baseOf n == "." && conforms TInt h && conforms TListInt tl
    _ -> False
  TAdt def -> case t of
    CompoundTerm n as -> case findCtor def (baseOf n) of
      Just c -> length c.fields == length as && and (zipWith conforms c.fields as)
      Nothing -> False
    _ -> False

-- | Render a recorded violation for the counterexample.
describeBad :: Bad -> String
describeBad b =
  T.unpack
    ( "violation at "
        <> b.badWhere
        <> " (site "
        <> tshow b.badCode
        <> "): "
        <> b.badWhy
        <> "\n  observed: "
        <> tshow b.badSnaps
    )

-- | Classify a failure so the counterexample says which stage of the
-- claim broke. A 'TypeErrors' here comes from the query type-check
-- inside @prepareQuery@, not from running: the program itself was
-- checked separately and cleanly at that point.
describeException :: SomeException -> String
describeException exc = case fromException exc of
  Just (TypeErrors errs) ->
    "goal rejected by the query type-check: " ++ unlines (map displayMsg errs)
  Just (err :: Error) -> "run failed: " ++ displayMsg err
  Nothing -> "unexpected exception: " ++ show exc
