{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | The oracle: what counts as a soundness violation, and why nothing
-- else can masquerade as one.
module YCHR.TypeSoundness.Oracle
  ( conforms,
    describeException,
  )
where

import Control.Exception (SomeException, fromException)
import Data.Text (Text)
import YCHR.Internal.Display (Display (..))
import YCHR.Internal.Types (Name (..), Term (..))
import YCHR.Run (Error (..))
import YCHR.TypeSoundness.Types

{- Note [Why benign failures are impossible]

The strict oracle (any exception is a failure) is only justified if the
generated fragment cannot fail for a reason unrelated to soundness. The
argument rests on one invariant: every in-scope variable is ground.

  * Goal tells carry closed expressions, so the initial store is ground.
    Both producers keep that so: the free arguments come from
    `genExprRoot` under an empty environment, and the seeded ones from
    `patInstance`, whose holes are filled by `genClosedLeaf`.
  * Head matching therefore binds head variables to ground values.
  * `BIs` and `BUnify` bind a *fresh* variable from ground inputs;
    guards bind nothing.

From groundness the rest follows:

  * No evaluated position ever sees an unbound variable, so the
    "unbound variable in evaluated position" runtime error cannot fire.
  * `BUnify` cannot fail: its left-hand side is always a fresh variable,
    which unifies with anything. (Failed body unification *is* a runtime
    error — see `unifyOrError` in the interpreter — so this matters.)
  * Nothing observes an unbound variable, so no reactivation ever
    happens.
  * The preamble predicates and the prelude functions used (`+ - *`,
    `< > >= =<`, `==`, `not`, and `integer/1` under `assert_int`) are
    total. `div`/`mod` are excluded because they are partial.
  * No form in `Expr`/`STerm` can widen to `any`: no host calls, no
    `quote`, no undeclared constructors, no evaluable head under `=`,
    and never a bare-variable `is` right-hand side (which the spec
    widens to `any`).

The only deliberately partial functions in a generated module are the
`assert_τ` instrumentation predicates, and their "no matching equation"
failure happens exactly when a runtime value falls outside its static
type — that is the property violation being detected, not noise.
-}

-- | The name a runtime 'Term' carries, without its module. Answers come
-- back qualified (@gen:k0@, @prelude:[]@) or bare depending on how the
-- value was built, so only the final component is compared.
baseOf :: Name -> Text
baseOf n = case n of
  Unqualified t -> t
  Qualified _ t -> t

-- | Does a returned binding structurally inhabit its static type?
--
-- This is the Haskell-side half of the oracle; the in-language
-- @assert_τ@ calls are the other half. They check the same thing from
-- opposite sides of the runtime boundary.
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
