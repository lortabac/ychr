{-# LANGUAGE NumericUnderscores #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Everything a generated program needs between being drawn and being
-- rendered: the runtime type assertions, and the static cap on how much
-- it may derive.
--
-- Both passes are pure functions of the generated value, so applying
-- them after @forAllWith@ keeps shrinking well-behaved.
module YCHR.TypeSoundness.Instrument
  ( prepare,
    instrument,
    pruneTells,
    derivationBound,
    maxInstances,
  )
where

import Data.List.NonEmpty qualified as NE
import Data.Map.Strict qualified as Map
import YCHR.TypeSoundness.Types

{- Note [Termination]

Every generated program terminates, by strict stratification: a rule
body may only tell constraints whose stratum is strictly below every
stratum appearing in the rule's head.

Induction downward from the top stratum. Instances at the top stratum
can only come from the goal (a rule telling it would need every head
stratum strictly above it), so there are finitely many. Given finitely
many instances at all strata above k, each rule whose heads all sit
above k fires finitely often — a propagation rule at most once per tuple
of constraint identifiers (propagation history), a simplification or
simpagation rule at most once per tuple as well, since each firing
consumes one of the tuple's members. So stratum k receives finitely many
instances, and the induction goes through.

Termination alone is not enough for a 60s test budget, though: the
per-level bound is quadratic in the level above, so a four-stratum
program can in principle derive hundreds of thousands of constraints.
'pruneTells' caps that statically — see its haddock.
-}

-- | Everything a generated program needs before it is rendered.
prepare :: Program -> Program
prepare = instrument . pruneTells

-- | Weave the runtime type assertions into every rule body.
--
-- Each rule opens with an @assert_τ(V)@ per pattern-bound head
-- variable: that is the store-typing invariant, i.e. that head matching
-- really did deliver values of the declared argument types. Each @is@
-- or @=@ binding is followed by an assertion on the variable it just
-- bound.
--
-- Goal probes are instrumented at render time
-- ('YCHR.TypeSoundness.Render.renderQuery'), where each @R is E@ picks
-- up a @B is assert_τ(R)@ conjunct.
instrument :: Program -> Program
instrument prog = prog {rules = map instrumentRule prog.rules}

instrumentRule :: Rule -> Rule
instrumentRule r = r {body = headAsserts ++ concatMap expand r.body}
  where
    headAsserts = [BAssert n t | (n, t) <- ruleVars r]
    expand it = case it of
      BIs w t _ -> [it, BAssert w t]
      BUnify w t _ -> [it, BAssert w t]
      _ -> [it]

-- | Ceiling on the number of constraint instances a generated program
-- may derive.
maxInstances :: Integer
maxInstances = 200

-- | Per-stratum saturation point, so the bound computation itself
-- cannot produce astronomically large 'Integer's before deciding to
-- prune.
capLimit :: Integer
capLimit = 1_000_000

-- | Drop body tells until the derivation is provably small.
--
-- Stratification (see @Note [Termination]@) guarantees termination but
-- not speed: each stratum can hold up to the /product/ of the instance
-- counts of the strata above it, so a four-stratum program can derive
-- six figures' worth of constraints and blow the 60s per-test budget.
--
-- 'derivationBound' computes that recurrence exactly (it is a genuine
-- upper bound: a rule fires at most once per tuple of head instances,
-- by propagation history for propagation rules and by consumption for
-- the others). While the bound is over 'maxInstances', the tells of the
-- last rule that still has any are dropped. Being a deterministic
-- function of the generated program, this composes with shrinking.
pruneTells :: Program -> Program
pruneTells prog
  | derivationBound prog <= maxInstances = prog
  | otherwise = case lastTellingRule prog.rules of
      Nothing -> prog
      Just i -> pruneTells prog {rules = dropTellsAt i prog.rules}
  where
    lastTellingRule rs =
      case [i | (i, r) <- zip [0 :: Int ..] rs, any isTell r.body] of
        [] -> Nothing
        is -> Just (last is)
    dropTellsAt i rs =
      [ if j == i then r {body = filter (not . isTell) r.body} else r
      | (j, r) <- zip [0 :: Int ..] rs
      ]

-- | Upper bound on the constraint instances a program can ever create.
--
-- Because a body may only tell strata strictly below its head, the cap
-- at a stratum depends only on strata above it, so one top-down fold
-- suffices. At stratum @s@ the instances are the goal's own tells there
-- plus, for each rule whose heads all sit above @s@, its firings times
-- the tells it makes to @s@. Firings are over-approximated by the
-- product of the head strata's caps — a rule fires at most once per
-- tuple of head instances, by propagation history for a propagation
-- rule and by consumption for the other two — which ignores the
-- id-distinctness discount and so can only overshoot.
--
-- Caps saturate at 'capLimit' so that a program headed for an
-- astronomical bound does not build an astronomical 'Integer' before
-- 'pruneTells' notices. 'capLimit' is far above 'maxInstances', so
-- saturation can never hide a program that needed pruning.
derivationBound :: Program -> Integer
derivationBound prog = sum (Map.elems caps)
  where
    top = maximum [s.stratum | s <- NE.toList prog.sigs]
    caps = foldl step Map.empty [top, top - 1 .. 0]
    step acc s = Map.insert s (min capLimit (goalCount s + fromRules acc s)) acc
    goalCount s =
      toInteger (length [() | (sig, _) <- NE.toList prog.goal.tells, sig.stratum == s])
    fromRules acc s =
      sum [firings acc r * tellsTo r s | r <- prog.rules, minHeadStratum r > s]
    firings acc r =
      product [Map.findWithDefault 0 h.headSig.stratum acc | h <- ruleHeads r]
    tellsTo r s =
      toInteger (length [() | BTell sig _ <- r.body, sig.stratum == s])
