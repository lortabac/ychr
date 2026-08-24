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
-- core AST keeps annotations as data ('YCHR.TypeSoundness.Types.Ann')
-- so that generator can be reused by erasing annotations to @any@.
--
-- What this version deliberately leaves out, so the coverage is not
-- overread:
--
--   * /Polymorphism/. Every generated declaration is monomorphic, so
--     the rigid-variable machinery §Soundness credits for polymorphic
--     declarations — @requiring@ bounds, skolem merging — is untouched.
--     That is the most valuable next increment.
--   * /Mode/. Goals are ground and nothing unbound is ever stored, so
--     the axis §No mode checking describes — a free variable reaching
--     an operation that demands a value — is out of scope by
--     construction. The strict oracle depends on that; see
--     @Note [Why benign failures are impossible]@.
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
import System.Timeout (timeout)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Hedgehog (testProperty)
import YCHR.Internal.Compile.Pipeline (CompiledProgram (..))
import YCHR.Internal.Display (Display (..))
import YCHR.Internal.TypeCheck (TypeCheckResult (..), typeCheckProgram)
import YCHR.Internal.Types (Term (..))
import YCHR.Run (Error (..), compileModules, runProgramWithQuery)
import YCHR.TypeSoundness.Gen (genProgram)
import YCHR.TypeSoundness.Instrument (prepare)
import YCHR.TypeSoundness.Observe
import YCHR.TypeSoundness.Oracle (conforms, describeBad, describeException)
import YCHR.TypeSoundness.Render (renderModule, renderQuery)
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

prop_soundness :: Property
prop_soundness = withTests 100 $ property $ do
  raw <- forAllWith (T.unpack . showProgram) genProgram
  let prog = prepare raw
      src = renderModule prog
      query = renderQuery prog
  coverShape prog
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
  coverRuntime prog lg
  mapM_ (annotate . describeBad) (reverse lg.logBad)
  unless (null lg.logBad) failure
  case outcome of
    Nothing -> annotate "timed out" >> discard
    Just (Left exc) -> annotate (describeException exc) >> failure
    Just (Right bindings) -> mapM_ (checkProbe bindings) prog.goal.probes
  where
    showProgram p =
      let q = prepare p in renderModule q <> "\n?- " <> renderQuery q <> "\n"

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
coverShape :: Program -> PropertyT IO ()
coverShape prog = do
  cover 65 "a rule joins two head constraints" (any ((> 1) . length . ruleHeads) rs)
  cover 30 "a rule body tells a constraint" (any (any isTell . (.body)) rs)
  cover 62 "a rule body binds a variable" (any (any isBind . (.body)) rs)
  cover 62 "a rule has a guard" (any (any ownGuard . (.guards)) rs)
  cover 45 "the goal has a probe" (not (null prog.goal.probes))
  cover 46 "the program declares an algebraic type" (not (null prog.adts))
  where
    rs = prog.rules
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
coverRuntime :: Program -> ObsLog -> PropertyT IO ()
coverRuntime prog lg = do
  cover 85 "some rule was reached" (any hit reachedCodes)
  cover 55 "some rule fired" (any hit firedCodes)
  cover 32 "a rule joining two heads fired" (any hit joinFiredCodes)
  cover 30 "a rule body binding a variable ran it" (any hit bindCodes)
  -- The complement of @Note [Firing rates]@'s "vacuous" row, and so
  -- defined the same way: a program is vacuous when it neither fires a
  -- rule nor carries a goal probe, and has therefore observed nothing
  -- at all. Reaching a rule without firing it does not count.
  cover 80 "the program observed something" (any hit firedCodes || not (null prog.goal.probes))
  cover 99 "the observation log did not overflow" (not lg.logOverflow)
  where
    hit c = IntMap.findWithDefault 0 c lg.logHits > 0
    sites = IntMap.toList prog.obs
    codesWhere p = [c | (c, s) <- sites, p s.osWhere]
    reachedCodes = codesWhere (T.isSuffixOf " head")
    firedCodes = codesWhere (T.isSuffixOf " fired")
    bindCodes = codesWhere (T.isInfixOf " binds ")
    joinNames =
      [ r.ruleName
      | r <- prog.rules,
        length (ruleHeads r) > 1
      ]
    joinFiredCodes =
      [ c
      | (c, s) <- sites,
        Just n <- [T.stripSuffix " fired" s.osWhere],
        n `elem` joinNames
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
              ++ T.unpack (renderTy p.probeTy)
              ++ " is bound to a value outside that type: "
              ++ show t
          )
        failure

tests :: TestTree
tests =
  testGroup
    "TypeSoundness"
    [ testProperty
        "fully-typed programs run without type errors"
        prop_soundness
    ]
