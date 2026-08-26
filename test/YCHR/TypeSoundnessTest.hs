{-# LANGUAGE OverloadedStrings #-}

-- | Property test for the first of the two correctness claims the type
-- system rests on (@docs\/reference\/type-system.md@, §Soundness):
--
-- > Soundness of the fully-typed fragment — if no expression is typed
-- > @any@ and the program type-checks, every value that is /bound/ at
-- > runtime is bound within its static type.
--
-- The test generates a random CHR program that is well-typed /by
-- construction/ (a typed core AST, "YCHR.TypeSoundness.Types"),
-- pretty-prints it to @.chr@ source, pushes it through the real
-- pipeline (@compileModules@ → @typeCheckProgram@ → run), and requires
-- the whole round trip to succeed.
--
-- Absence of a crash is a weak oracle on its own — an operation could
-- receive a wrong-typed value and happen not to mind. So generated
-- programs are /instrumented/ with calls to a host function the test
-- registers ("YCHR.TypeSoundness.Observe"), which snapshots the runtime
-- values it is handed and checks them against the static types the
-- generator gave those positions. It records rather than raises, so one
-- run yields every witness, and it makes runtime facts — did this rule
-- fire? — directly assertable ('coverRuntime').
--
-- The oracle is /strict/: any exception at all is a failure, as is any
-- observation that is not @Inhabits@ and any diagnostic beyond a clean
-- compile. See @Note [Why benign failures are impossible]@ in
-- "YCHR.TypeSoundness.Oracle" for why the generated fragment cannot
-- fail for any reason other than a real violation.
--
-- The second claim (the gradual guarantee) is a separate property; the
-- core AST keeps annotations as data
-- ('YCHR.TypeSoundness.Types.ArgSpec') so that generator can be reused
-- by erasing annotations to @any@.
--
-- Polymorphism /is/ generated: parametric algebraic types, polymorphic
-- constraint declarations, per-occurrence rigid variables at every
-- head, the skolem merge a variable shared between head positions
-- forces, and guard-derived evidence — a literal or constructor
-- pattern at a rigid scrutinee, and @integer@ \/ @boolean@ guards.
-- Because the generator models rigidity itself and the checker is the
-- thing under test, a type error is a failure rather than a discard:
-- the two disagreeing is exactly what these stages look for. (This
-- property earned its keep once already: it found the unsound
-- parameter pinning of @GuardEqual@ evidence, fixed by the
-- constructor-only pin discipline of §What evidence does that
-- 'YCHR.TypeSoundness.Types.eqUnifySTy' now models.)
--
-- Evidence is /positional/, and the instrumentation respects that: the
-- head observation asserts only what matching alone guarantees, and a
-- second observation after the evidence guards asserts what they add.
-- See 'YCHR.TypeSoundness.Instrument.instrument'.
--
-- Two regimes are generated, as two properties. In the /closed/ one
-- every argument position is ground, nothing unbound is ever stored,
-- and the oracle is at its strictest. In the /open/ one some positions
-- are willing to hold a term that is not bound yet, so a constraint
-- can sit in the store waiting for a later unit to bind it — the
-- store-interleaving regime §No mode checking describes. There the
-- claim under test is the sharpened one: __every value that is bound
-- is bound within its static type__. A term still holding no value is
-- a statement about mode, so it is a violation only at a position
-- whose declared boundness said it would be ground.
--
-- What this version deliberately leaves out, so the coverage is not
-- overread:
--
--   * /Bounded polymorphism/. No @requiring@ clause is generated, so
--     nothing exercises ambient signatures or bound discharge, and an
--     overloaded operation is never reached at a rigid type.
--   * Floats, strings, lambdas and @'$call'@; rules with three or more
--     heads; simpagations other than @1 \\ 1@; recursive generated
--     algebraic types (@list(int)@ is the one recursive shape);
--     same-symbol recursion in rule bodies (forbidden by the
--     stratification that gives termination).
module YCHR.TypeSoundnessTest (tests) where

import Control.Exception (SomeException, try)
import Control.Monad (unless)
import Data.IORef (newIORef, readIORef)
import Data.IntMap.Strict qualified as IntMap
import Data.List.NonEmpty qualified as NE
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Text (Text)
import Data.Text qualified as T
import Hedgehog
  ( Property,
    PropertyT,
    annotate,
    cover,
    discard,
    evalIO,
    failure,
    forAllWith,
    property,
    withTests,
  )
import Hedgehog.Internal.Property (CoverPercentage, LabelName)
import System.Timeout (timeout)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Hedgehog (testProperty)
import YCHR.Internal.Compile.Pipeline (CompiledProgram (..))
import YCHR.Internal.Display (Display (..))
import YCHR.Internal.TypeCheck (TypeCheckResult (..), typeCheckProgram)
import YCHR.Internal.Types (Term (..))
import YCHR.Run (Error (..), compileModules, runProgramWithQuery)
import YCHR.TypeSoundness.Gen (Mode (..), genProgramWith)
import YCHR.TypeSoundness.Instrument (prepare)
import YCHR.TypeSoundness.Observe
import YCHR.TypeSoundness.Oracle (conforms, describeBad, describeException)
import YCHR.TypeSoundness.Render (renderModule, renderQuery, renderSkolemNote)
import YCHR.TypeSoundness.Types

-- | How long one generated program may run before the property gives
-- up on it.
--
-- Stratification bounds the derivation and
-- 'YCHR.TypeSoundness.Instrument.pruneTells' bounds its size, so in the
-- ground fragment this should never fire; it is here so that a
-- generator change which breaks that assumption degrades into a
-- discard rather than into the suite-wide 60s tasty timeout, which
-- takes the whole run down with it.
runBudgetMicros :: Int
runBudgetMicros = 5_000_000

-- | The closed regime: every argument position is 'Ground', nothing
-- unbound is ever stored, and the oracle is at its strictest.
prop_soundness :: Property
prop_soundness = withTests 300 (property (soundnessProperty Closed))

-- | The open regime: some positions are willing to hold a term that is
-- not bound yet, so a constraint can sit in the store waiting for a
-- later unit to bind it.
--
-- The claim under test is the sharpened one
-- (@docs\/reference\/type-system.md@ §Soundness): __every value that
-- is bound is bound within its static type__. A term still holding no
-- value is a statement about /mode/, which the type system
-- deliberately does not track (§No mode checking), so it is a
-- violation only at a position whose contract said it would be ground.
--
-- The goal's own bindings carry the sharpest form of that check: a
-- query variable passed unbound into a declared position comes back
-- with whatever the run eventually bound it to, and that value has to
-- inhabit the type the declaration gave the position — however many
-- units and reactivations it passed through in between.
prop_soundness_open :: Property
prop_soundness_open = withTests 300 (property (soundnessProperty Open))

soundnessProperty :: Mode -> PropertyT IO ()
soundnessProperty mode = do
  raw <- forAllWith (T.unpack . showProgram) (genProgramWith mode)
  let prog = prepare raw
      src = renderModule prog
      query = renderQuery prog
  coverShape mode prog
  cp <- case compileModules False [("gen.chr", src)] of
    Left err -> annotate ("compile error: " ++ displayMsg (err :: Error)) >> failure
    Right (cp, ws) -> do
      -- A generated module contains no partial function and no
      -- construct the checker has anything to say about, so any
      -- diagnostic at all means the generator and the compiler
      -- disagree about what it built.
      mapM_ (annotate . ("compile warning: " ++) . displayMsg) ws
      unless (null ws) failure
      pure cp
  tc <- evalIO (typeCheckProgram cp.desugaredProgram)
  mapM_ (annotate . ("typecheck warning: " ++) . displayMsg) tc.warnings
  mapM_ (annotate . ("type error: " ++) . displayMsg) tc.errors
  unless (null tc.warnings && null tc.errors) failure
  ref <- evalIO (newIORef emptyLog)
  outcome <-
    evalIO
      ( timeout
          runBudgetMicros
          ( try @SomeException
              (runProgramWithQuery cp (observerRegistry prog.obs ref) query)
          )
      )
  -- The log is read before anything else is decided, so a violation is
  -- never lost to an unrelated failure or to the budget running out.
  lg <- evalIO (readIORef ref)
  coverRuntime mode prog lg
  mapM_ (annotate . describeBad) (reverse lg.logBad)
  unless (null lg.logBad) failure
  -- The interleaving itself: a value the goal put into the store
  -- without one, that some later unit bound. Everything else in the
  -- open regime is setup for this.
  let laterBound = case outcome of
        Just (Right bs) -> any (wasBound bs . fst) prog.goal.unbounds
        _ -> False
  coverOpen mode 15 "a stored unbound value was later bound" laterBound
  case outcome of
    Nothing -> annotate "timed out" >> discard
    Just (Left exc) -> annotate (describeException exc) >> failure
    Just (Right bindings) -> do
      mapM_ (checkProbe bindings) prog.goal.probes
      mapM_ (checkUnbound bindings) prog.goal.unbounds
  where
    showProgram p =
      let q = prepare p
       in renderModule q
            <> "\n?- "
            <> renderQuery q
            <> "\n"
            <> renderSkolemNote q

-- | Assert that the generated programs are structurally rich enough for
-- the property to mean anything.
--
-- Without this the property can go quietly vacuous: a size-scaled
-- 'Hedgehog.Range.linear' whose span is 1 or 2 truncates to its lower
-- bound over most of hedgehog's size sweep, which once left the first
-- ~40% of every run with a single-constraint store, no guards, no body
-- tells and no probes — nothing that could observe a soundness
-- violation.
--
-- The floors are therefore set /between/ the current rates and the
-- rates that same degeneration would produce, not merely somewhere
-- above zero — a floor of 20% would have let the original defect
-- through. Measured rates (n = 3000) against the rate the degeneration
-- would give:
--
-- > join two heads  85% (would be 53%)   floor 65
-- > body tell       52% (would be 37%)   floor 30
-- > body bind       82% (would be 53%)   floor 62
-- > guard           83% (would be 52%)   floor 62
-- > probe           70% (would be 39%)   floor 45
-- > algebraic type  66% (would be 41%)   floor 46
--
-- Only the body-tell floor is loose: its rate sits near 50%, where the
-- binomial spread at @withTests 100@ is widest, so a discriminating
-- floor would flake. The other five bind, and the degeneration trips
-- all of them at once.
--
-- It reads the /prepared/ program, because the body-tell label has to
-- see how much 'YCHR.TypeSoundness.Instrument.pruneTells' dropped. That
-- means it also sees the instrumentation, so the guard label filters
-- the observation conjunct back out: counting it would make the label
-- unconditionally true and silently vacuous.
coverShape :: Mode -> Program -> PropertyT IO ()
coverShape mode prog = do
  cover 65 "a rule joins two head constraints" (any ((> 1) . length . ruleHeads) rs)
  cover 30 "a rule body tells a constraint" (any (any isTell . (.body)) rs)
  cover 62 "a rule body binds a variable" (any (any isBind . (.body)) rs)
  -- Lower in the open regime: a boundness guard lives in the leading
  -- guard list, not in the rule's own, so a rule whose only condition
  -- is @nonvar(X)@ does not count here.
  cover (byMode mode 62 45) "a rule has a guard" (any (any ownGuard . (.guards)) rs)
  cover 45 "the goal has a probe" (not (null prog.goal.probes))
  cover 46 "the program declares an algebraic type" (not (null prog.adts))
  -- Polymorphism. Without these the zero-rejection soak gate would be
  -- satisfied just as well by a generator that had quietly stopped
  -- emitting any, which is the failure mode they exist to catch — so
  -- the floors sit a few standard deviations under the measured rate
  -- rather than at some token value. Measured over 1000 programs:
  --
  -- > polymorphic constraint  85%  floor 70
  -- > parametric type         33%  floor 15
  -- > rigid head occurrence   70%  floor 55
  -- > rigid merge              7%  floor  2
  -- > tell at a rigid type     5%  floor  1
  -- > literal pin             18%  floor  8
  -- > match pin               29%  floor 15
  -- > shared-variable pin     20%  floor 10
  -- > type-predicate pin      25%  floor 12
  --
  -- The two rigid rows are low by construction rather than by accident,
  -- and both got lower in the evidence stage: every pin turns a rigid
  -- variable concrete, so evidence competes for exactly the variables a
  -- merge or a tell would otherwise use. Both draws are already
  -- weighted towards the rigid case (see
  -- 'YCHR.TypeSoundness.Gen.pickTarget' and @pickTellTarget@, and the
  -- @merging@ split in @maybeAlias@).
  --
  -- Rates near 5% are why this property runs @withTests 300@ rather
  -- than 100: at 100 a 5% event is absent from a whole run about once
  -- in 170, which is too flaky for a floor to be worth having, and
  -- floors are the only thing standing between this property and going
  -- quietly vacuous.
  cover 70 "the program declares a polymorphic constraint" anyPolySig
  cover 15 "the program declares a parametric algebraic type" anyParamTy
  cover 55 "a head occurrence allocates rigid variables" anyRigidHead
  cover (byMode mode 2 1) "an alias merged two rigid variables" anyMerge
  cover 1 "a body tell instantiates a parameter at a rigid type" anyTellAtRigid
  -- One label per evidence form, because they are reached by quite
  -- different routes and a single "something was pinned" label would
  -- hide three of them going to zero.
  -- Bounded polymorphism. The last label is the one that matters: an
  -- overloaded call at a rigid type is the only thing a @requiring@
  -- clause makes possible that is not possible without one — without
  -- the ambient signature it is YCHR-60006 — and it is the route
  -- Stage 4's finding could not take.
  --
  -- The four before it are the chain that has to hold for it, and they
  -- are kept as separate labels because a zero on the last one says
  -- nothing about which link broke. Measured over 1000 programs:
  --
  -- > declares a class                75%  floor 55
  -- > declares a bounded constraint   38%  floor 22
  -- > head contributes an ambient     28%  floor 15
  -- > variable at the bounded rigid   14%  floor  6
  -- > overloaded call anywhere        28%  floor 15
  -- > overloaded call at a rigid       9%  floor  3
  --
  -- The last two together are what says the mechanism is exercised
  -- rather than merely declared: most class calls land at a ground
  -- instance type, where no bound is involved at all.
  cover 55 "the program declares a class" (not (null prog.classes))
  cover 22 "the program declares a bounded constraint" anyBounded
  cover 15 "a rule head contributes an ambient signature" anyAmbientHead
  cover 6 "a variable is bound at an ambient-covered rigid type" anyAmbientVar
  cover 15 "an overloaded call is made at all" anyClassCall
  cover 3 "an overloaded call is made at a rigid type" anyAmbientCall
  -- The open regime. Without these the open property could be green
  -- and say nothing: a run in which nothing was ever stored unbound
  -- exercises exactly the closed fragment over again.
  coverOpen mode 40 "a position may hold an unbound value" anyOpenPos
  coverOpen mode 25 "the goal stored an unbound value" (not (null prog.goal.unbounds))
  coverOpen mode 20 "a boundness guard cleared a variable" anyModeGuard
  cover 8 "a literal pinned a rigid variable" (pinnedBy PinLit)
  cover 15 "a pattern match pinned a rigid variable" (pinnedBy PinMatch)
  cover 10 "a shared variable pinned a rigid variable" (pinnedBy PinMergeConcrete)
  cover 12 "a type predicate pinned a rigid variable" (pinnedBy PinTypePred)
  -- The case the GuardEqual soundness fix opened up: an alias whose
  -- pair meets a parameter position (a parametric pin's fresh betas,
  -- or two types meeting inside a shared constructor). The checker
  -- derives nothing there; the instance generator carries the
  -- identification in 'skForce'. Measured at 23% over 3000 programs.
  cover 10 "an alias forced a parameter identification" anyForce
  where
    rs = prog.rules
    sigList = NE.toList prog.sigs
    anyPolySig = any (not . null . (.sigTvs)) sigList
    anyParamTy = any (not . null . (.adtParams)) prog.adts
    anyRigidHead = any (not . null . (.headSkolems)) occs
    -- A merge proper: one rigid variable aliased to another. Counting
    -- 'skBind' alone would also count every pin, which lands in the
    -- same map and is a different thing.
    anyMerge = any (any isSk . Map.elems . (.skBind) . (.ruleSk)) rs
    anyForce = any (not . Map.null . (.skForce) . (.ruleSk)) rs
    pinnedBy src =
      any ((src `elem`) . Map.elems . (.skPinned) . (.ruleSk)) rs
    anyBounded = any (not . null . (.sigBounds)) sigList
    anyOpenPos =
      any (any ((== MayBeUnbound) . (.argBound)) . NE.toList . (.sigArgs)) sigList
    anyModeGuard = any (any isModeGuard . (.ruleEvidence)) rs
    isModeGuard e = case e of
      EModePred _ _ -> True
      _ -> False
    anyAmbientHead =
      any (not . null . (.headSig.sigBounds)) occs
    -- A class call whose first argument is /still/ rigid under the
    -- rule's final skolem state. Resolving matters: a variable an
    -- evidence guard pinned still carries a skolem in the expression
    -- the generator built, but by then the call is at a concrete type
    -- and resolves against a declared signature rather than an
    -- ambient. Counting those would inflate the one label that says
    -- the bound machinery was exercised at all.
    anyAmbientVar = any ruleHasAmbientVar rs
    ruleHasAmbientVar r =
      or
        [ resolveSTy r.ruleSk t == SSk sk
        | (_, t) <- ruleVars r,
          h <- ruleHeads r,
          b <- h.headSig.sigBounds,
          (tv, sk) <- zip h.headSig.sigTvs h.headSkolems,
          tv == b.bsTv
        ]
    anyClassCall = any (\r -> any anyClass (r.ruleEvidence ++ r.guards)) rs
    anyClass e = case e of
      EClass _ _ -> True
      EArith _ x y -> anyClass x || anyClass y
      ECmp _ x y -> anyClass x || anyClass y
      EEq _ x y -> anyClass x || anyClass y
      ENot x -> anyClass x
      ECall _ es -> any anyClass es
      ECtor _ es -> any anyClass es
      EListLit es -> any anyClass es
      ECopy x -> anyClass x
      EHostObs _ es -> any anyClass es
      _ -> False
    anyAmbientCall = any ruleHasAmbientCall rs
    ruleHasAmbientCall r =
      any (hasAmbientCall r) (r.ruleEvidence ++ r.guards)
        || any (bodyHasAmbientCall r) r.body
    bodyHasAmbientCall r it = case it of
      BTell _ _ es -> any (hasAmbientCall r) es
      BIs _ _ e -> hasAmbientCall r e
      BObs _ es -> any (hasAmbientCall r) es
      _ -> False
    hasAmbientCall r e = case e of
      EClass _ es -> any (rigidUnder r) es || any (hasAmbientCall r) es
      EArith _ x y -> hasAmbientCall r x || hasAmbientCall r y
      ECmp _ x y -> hasAmbientCall r x || hasAmbientCall r y
      EEq _ x y -> hasAmbientCall r x || hasAmbientCall r y
      ENot x -> hasAmbientCall r x
      ECall _ es -> any (hasAmbientCall r) es
      ECtor _ es -> any (hasAmbientCall r) es
      EListLit es -> any (hasAmbientCall r) es
      ECopy x -> hasAmbientCall r x
      EHostObs _ es -> any (hasAmbientCall r) es
      _ -> False
    rigidUnder r e = case e of
      EVar _ t -> case resolveSTy r.ruleSk t of
        SSk _ -> True
        _ -> False
      _ -> False
    anyTellAtRigid = any tellAtRigid rs
    occs = concatMap ruleHeads rs
    tellAtRigid r = any atRigid r.body
    atRigid it = case it of
      BTell _ sub _ -> any isSk (Map.elems sub)
      _ -> False
    isSk t = case t of
      SSk _ -> True
      _ -> False
    isBind it = case it of
      BIs {} -> True
      BUnify {} -> True
      _ -> False
    ownGuard g = case g of
      EHostObs _ _ -> False
      _ -> True

-- | Assert that the generated programs actually /did/ something.
--
-- This is the half 'coverShape' cannot see. A program whose rules never
-- fire runs none of the observations that carry the property, so it
-- costs a test iteration and observes nothing — and whether a rule
-- fires is a runtime fact. Before the host observer it had to be
-- measured out of band with a canary (see @Note [Firing rates]@ in
-- "YCHR.TypeSoundness.Gen"); the observer's per-site hit counts make it
-- assertable here instead, so CI enforces continuously what used to be
-- a measurement someone had to remember to redo.
--
-- Floors are set the same way as 'coverShape'\'s: measured first, then
-- placed below the measured rate but above what the degeneration
-- @Note [Firing rates]@ documents would give. Measured over 3000
-- programs (three independent 1000-program chunks), against the
-- note's \"before\" column where it has a comparable row:
--
-- > some rule was reached     95 96 95            floor 85
-- > some rule fired           68 68 66  (was 42)  floor 55
-- > a joined rule fired       46 44 43  (was ~29) floor 32
-- > a rule body ran a bind    51 51 46            floor 30
-- > the program observed      88 89 88  (was 77)  floor 80
--
-- Two of these are the cross-check that retires the canary. The note
-- puts \"program fires some rule\" at 70% and \"vacuous\" at 8% —
-- i.e. 92% observed something — measured out of band by splicing a
-- raising body into every rule and counting the runs that failed. The
-- observer reproduces both to within a few points from inside the same
-- run. The residual gap is expected: 'maxInstances' came down from 200
-- to 120 when the guard-position observations landed, so
-- 'YCHR.TypeSoundness.Instrument.pruneTells' strips marginally more
-- body tells than it did when the note was written.
--
-- The joined-rule row has no directly comparable \"before\" number —
-- the note's are per-rule, not per-program — so its degenerate value
-- is scaled from the note's two-head rows (22\/34 of the measured
-- rate). The bind row sits near 50%, where the binomial spread at
-- @withTests 100@ is widest, so its floor is deliberately loose for
-- the same reason the body-tell floor is.
coverRuntime :: Mode -> Program -> ObsLog -> PropertyT IO ()
coverRuntime mode prog lg = do
  -- Lower in the open regime: a constraint stored holding nothing
  -- matches fewer structured patterns, and a rule gated on @nonvar@
  -- is not reached until something binds the value.
  cover (byMode mode 85 65) "some rule was reached" (any hit reachedCodes)
  cover 55 "some rule fired" (any hit firedCodes)
  -- Lower in the open regime: a constraint holding nothing matches
  -- fewer patterns, so a join is satisfied less often.
  cover (byMode mode 32 18) "a rule joining two heads fired" (any hit joinFiredCodes)
  cover 30 "a rule body binding a variable ran it" (any hit bindCodes)
  -- The complement of @Note [Firing rates]@'s "vacuous" row, and so
  -- defined the same way: a program is vacuous when it neither fires a
  -- rule nor carries a goal probe, and has therefore observed nothing
  -- at all. Reaching a rule without firing it does not count.
  cover 80 "the program observed something" (any hit firedCodes || not (null prog.goal.probes))
  cover 28 "a rule with rigid head variables fired" (any hit rigidFiredCodes)
  -- The evidence criterion, made observable. This site sits after the
  -- evidence guards and asserts the type they pinned; if it never ran,
  -- the check that guard-derived evidence holds at run time would be
  -- theatre.
  cover 4 "an evidence pin was checked at runtime" (any hit evidenceCodes)
  -- The one that says the store-interleaving regime was actually
  -- entered, rather than merely declared: a rule was reached with a
  -- position holding no value yet.
  coverOpen mode 10 "an unbound value reached a rule head" (not (IntMap.null lg.logUnbound))
  -- Lower in the open regime: an unbound value fires fewer rules, so
  -- more candidate matches are examined and rejected, and every one of
  -- them is observed.
  cover (byMode mode 99 95) "the observation log did not overflow" (not lg.logOverflow)
  where
    hit c = IntMap.findWithDefault 0 c lg.logHits > 0
    sites = IntMap.toList prog.obs
    codesWhere p = [c | (c, s) <- sites, p s.osWhere]
    reachedCodes = codesWhere (T.isSuffixOf " head")
    evidenceCodes = codesWhere (T.isSuffixOf " evidence")
    firedCodes = codesWhere (T.isSuffixOf " fired")
    bindCodes = codesWhere (T.isInfixOf " binds ")
    joinNames =
      [ r.ruleName
      | r <- prog.rules,
        length (ruleHeads r) > 1
      ]
    joinFiredCodes = firedCodesOf joinNames
    rigidNames =
      [ r.ruleName
      | r <- prog.rules,
        any (not . null . (.headSkolems)) (ruleHeads r)
      ]
    rigidFiredCodes = firedCodesOf rigidNames
    firedCodesOf names =
      [ c
      | (c, s) <- sites,
        Just n <- [T.stripSuffix " fired" s.osWhere],
        n `elem` names
      ]

checkProbe :: Map Text Term -> Probe -> PropertyT IO ()
checkProbe bindings p = case Map.lookup p.probeVar bindings of
  Nothing ->
    annotate ("probe " ++ T.unpack p.probeVar ++ " has no binding") >> failure
  Just t
    | conforms p.probeTy t -> pure ()
    | otherwise -> do
        annotate
          ( "probe "
              ++ T.unpack p.probeVar
              ++ " : "
              ++ T.unpack (renderGTy p.probeTy)
              ++ " is bound to a value outside that type: "
              ++ show t
          )
        failure

-- | Pick a floor per regime: the closed one first.
byMode :: Mode -> a -> a -> a
byMode m closed open = case m of
  Closed -> closed
  Open -> open

-- | A label that only means anything in the open regime. In the closed
-- one the event is impossible by construction, so the floor is zero
-- rather than the label being absent — keeping both properties on the
-- same list makes the difference between them visible.
coverOpen ::
  Mode ->
  CoverPercentage ->
  LabelName ->
  Bool ->
  PropertyT IO ()
coverOpen m pct name b = cover (byMode m 0 pct) name b

-- | A query variable that went unbound into a declared position.
--
-- Still free at the end is fine — nothing was obliged to bind it. What
-- is not fine is a value outside the type of the position it was
-- stored at, whatever route it took to get there.
checkUnbound :: Map Text Term -> (Text, GTy) -> PropertyT IO ()
checkUnbound bindings (n, g) = case Map.lookup n bindings of
  Nothing -> pure ()
  Just t
    | isStillFree t -> pure ()
    | conforms g t -> pure ()
    | otherwise -> do
        annotate
          ( "query variable "
              ++ T.unpack n
              ++ ", stored at a position declared "
              ++ T.unpack (renderGTy g)
              ++ ", was bound to a value outside that type: "
              ++ show t
          )
        failure

-- | Did this query variable end the run holding a value?
wasBound :: Map Text Term -> Text -> Bool
wasBound bindings n = maybe False (not . isStillFree) (Map.lookup n bindings)

isStillFree :: Term -> Bool
isStillFree t = case t of
  Wildcard -> True
  VarTerm _ -> True
  _ -> False

tests :: TestTree
tests =
  testGroup
    "TypeSoundness"
    [ testProperty
        "fully-typed programs run without type errors"
        prop_soundness,
      testProperty
        "stored unbound values stay within their static type"
        prop_soundness_open
    ]
