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
import Data.Map.Strict qualified as Map
import Data.Text (Text)
import Data.Text qualified as T
import YCHR.Internal.Display (Display (..))
import YCHR.Internal.Types (Name (..), Term (..))
import YCHR.Run (Error (..))
import YCHR.TypeSoundness.Observe (Bad (..))
import YCHR.TypeSoundness.Types

{- Note [Why benign failures are impossible]

The oracle is strict: any exception at all is a failure, and any
observation its position's contract does not tolerate is a violation.
That is only justified if the generated fragment cannot fail, or see an
absent value, for a reason unrelated to soundness. The two regimes earn
it differently.

CLOSED: every in-scope variable is ground.

  * Goal tells carry closed expressions, so the initial store is ground.
    Both producers keep that so: the free arguments come from
    `genExprRoot` under an empty environment, and the seeded ones from
    `patInstance`, whose holes are filled by `genClosedLeafAt`.
  * Head matching therefore binds head variables to ground values.
  * `BIs` and `BUnify` bind a *fresh* variable from ground inputs;
    guards bind nothing.

From groundness the rest follows: no evaluated position sees a free
variable, so the "unbound variable in evaluated position" error cannot
fire and no observation can come back `NotYetBound`; `BUnify` cannot
fail, because its left-hand side is a fresh variable and unifies with
anything; and nothing observes a free variable, so no reactivation
happens.

OPEN: free variables exist, and are *confined*.

Groundness is given up deliberately — a value has to be stored without
one before another unit can supply it. What replaces it is a mode
discipline, tracked as a taint (`ctxTainted`) and enforced
structurally rather than classified after the fact:

  * A variable matched at a `MayBeUnbound` position is tainted, as is
    anything a structural `=` binds from one.
  * `varsAt` — the variables an *evaluated* position may draw on —
    excludes tainted ones. So arithmetic, comparison, `not`, a library
    predicate, a class call and an `is` right-hand side can never
    receive one.
  * A tainted variable may appear only where a free value is harmless:
    a structural `=` operand (which evaluates neither side), an
    ask-equality (which compares structure and returns false on two
    distinct free variables), a boundness or type predicate (all of
    which are total on any value), a head pattern, and a *bare* tell
    argument at another `MayBeUnbound` position — bare because a
    compound argument is evaluated, while a lone variable evaluates to
    itself.
    Verified by mutation rather than asserted: dropping the filter
    from `varsAt` makes the open property fail within a few hundred
    programs, with the "argument is not sufficiently instantiated
    (unbound variable)" this paragraph exists to prevent. The witness
    is an evaluated position outside a guard — a tell argument, an `is`
    right-hand side — because a rule guard catches that failure and
    answers false (docs/reference/language.md §Soft guard failure).
    Confining the taint is what keeps the *unguarded* positions safe;
    the guard boundary is a second line, not the first.
  * A `nonvar`/`ground` guard clears the taint for everything to its
    right, and only then may the value be evaluated. This is the
    discipline `docs/reference/type-system.md` §No mode checking
    prescribes, and it is why the open regime's rules are quieter: such
    a rule does not fire until something binds the value, and
    reactivation retries it then.

Two failure modes the closed argument ruled out by groundness are
therefore re-argued here:

  * `BUnify` may now bind a variable that is not fresh — that is the
    binder the corner is about. Every such item is gated by a
    `unifiable` conjunct in the same rule's guard. `unifiable` is a
    trailed trial unification that restores every cell it touches, so
    it decides exactly the question the body item will ask, and guards
    are pure, so nothing between the two can change the answer. A
    failed body unification is a hard runtime error, so this matters.
  * Reactivation now happens. It introduces no new failure mode: a
    rule re-runs from the start, and every activation is observed like
    any other.

BOTH regimes:

  * Every function a generated module can call is total. The preamble
    predicates are exhaustive, a generated class has a catch-all, and
    of the prelude functions emitted — `+ - *`, `< > >= =<`, `==`,
    `not`, `copy_term`, `unifiable`, `var`, `nonvar`, `ground`,
    `integer`, `boolean` — all are host-backed and total on the values
    that can reach them. `div`/`mod` are excluded because they are
    partial, and `not/1` is only ever applied to a ground `bool`. So
    "no matching equation" is not a signal the oracle has to interpret;
    it is a case that cannot occur.
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
  * A free value cannot hide a violation. `NotYetBound` is tolerated
    only where the position's declared boundness allows it, and it is
    counted either way, so a run cannot look like it exercised the
    open regime when it did not.
  * A violation cannot be lost to short-circuiting. The head
    observation is the *first* guard conjunct, so it runs for every
    candidate match that survived HNF's own match and equality guards,
    including the matches a user guard then rejects — and it is judged
    against what matching alone establishes (`ruleSkHead`,
    `ruleTaintedHead`), never against what a later guard adds.
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
conforms :: GTy -> Term -> Bool
conforms ty@(GTy con args) t = case (con, args) of
  (CInt, []) -> case t of
    IntTerm _ -> True
    _ -> False
  (CBool, []) -> case t of
    CompoundTerm n [] -> baseOf n == "true" || baseOf n == "false"
    _ -> False
  (CList, [el]) -> case t of
    CompoundTerm n [] -> baseOf n == "[]"
    CompoundTerm n [h, tl] ->
      baseOf n == "." && conforms el h && conforms ty tl
    _ -> False
  (CAdt def, _) -> case t of
    CompoundTerm n as -> case findCtor def (baseOf n) of
      Just c ->
        length c.ctorFields == length as
          && and (zipWith conforms (fieldGTys def args c) as)
      Nothing -> False
    _ -> False
  _ -> False

-- | A constructor's field types at a ground instantiation.
fieldGTys :: AdtDef -> [GTy] -> CtorDef -> [GTy]
fieldGTys def args c = map (groundD sub) c.ctorFields
  where
    sub = Map.fromList (zip def.adtParams args)

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
