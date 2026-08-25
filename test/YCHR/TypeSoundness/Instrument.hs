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

import Data.IntMap.Strict qualified as IntMap
import Data.List (mapAccumL)
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

-- | Weave the observation points into every rule, and build the table
-- the observer looks them up in.
--
-- Three kinds of point, each answering a different question:
--
--   [Head, in /guard/ position] @host:ts_obs(c, V…)@ as the first
--     guard conjunct, over every pattern-bound head variable. This is
--     the store-typing invariant — that head matching really did
--     deliver values of the declared argument types — and putting it
--     in the guard rather than the body checks it at every /candidate
--     match/, not only at the matches that go on to fire. It doubles
--     as the \"this rule was reached\" counter.
--
--   [Fired, in body position] A bare @host:ts_obs(c)@ as the first
--     body item. The difference between this site's hit count and the
--     head site's is exactly how often the guards rejected a match,
--     and its hit count is what makes the firing rates of
--     @Note [Firing rates]@ assertable with @cover@ instead of
--     measured out of band.
--
--   [Binding, in body position] After each @is@ or @=@, over the
--     variable it just bound.
--
-- Codes are allocated by a left-to-right numbering over the rules, so
-- they are a deterministic function of the program and survive
-- shrinking.
instrument :: Program -> Program
instrument prog = prog {rules = rs, obs = IntMap.fromList (concat tables)}
  where
    (_, annotated) = mapAccumL instrumentRule 0 prog.rules
    rs = map fst annotated
    tables = map snd annotated

-- | Instrument one rule, threading the next free site code.
instrumentRule :: Int -> Rule -> (Int, (Rule, [(Int, ObsSite)]))
instrumentRule code0 r =
  ( codeN,
    ( r
        { guards = EHostObs headCode headArgs : r.guards,
          body = BObs firedCode [] : bodyItems
        },
      (headCode, headSite) : (firedCode, firedSite) : bindSites
    )
  )
  where
    headCode = code0
    firedCode = code0 + 1
    vars = ruleVars r
    headArgs = [EVar n t | (n, t) <- vars]
    headSite =
      ObsSite
        { osWhere = r.ruleName <> " head",
          osCheck = ExpectPos (map (posCheck r.ruleSk . snd) vars)
        }
    firedSite =
      ObsSite {osWhere = r.ruleName <> " fired", osCheck = ExpectPos []}
    (codeN, expanded) = mapAccumL expand (code0 + 2) r.body
    bodyItems = concatMap fst expanded
    bindSites = concatMap snd expanded
    expand c it = case bound it of
      Nothing -> (c, ([it], []))
      Just (w, t) ->
        ( c + 1,
          ( [it, BObs c [EVar w t]],
            [ ( c,
                ObsSite
                  { osWhere = r.ruleName <> " binds " <> w,
                    osCheck = ExpectPos [posCheck r.ruleSk t]
                  }
              )
            ]
          )
        )
    bound it = case it of
      BIs w t _ -> Just (w, t)
      BUnify w t _ -> Just (w, t)
      _ -> Nothing

-- | What the observer can be told to check at one position.
--
-- A position whose type still mentions a rigid variable has no static
-- type to compare against: the store chose the instance, and the rule
-- was checked for every instance. All that can be asserted there is
-- that a value arrived at all.
posCheck :: SkolemEnv -> STy -> PosCheck
posCheck sk t = maybe MustBeBound MustInhabit (groundOf sk t)

-- | Ceiling on the number of constraint instances a generated program
-- may derive.
--
-- Lower than it would need to be for termination alone, because a
-- guard-position observation runs once per candidate match: a two-head
-- rule over an n-instance store makes O(n²) host calls, and at 200 the
-- worst case ran into 'YCHR.TypeSoundness.Observe.obsLimit'.
maxInstances :: Integer
maxInstances = 120

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
      toInteger (length [() | BTell sig _ _ <- r.body, sig.stratum == s])
