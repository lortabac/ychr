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
-- programs are /instrumented/: every variable whose static type is known
-- carries an in-language @assert_τ\/1@ call that deep-checks the runtime
-- value against that type (see
-- 'YCHR.TypeSoundness.Instrument.instrument'). The assertion functions
-- have no catch-all equation, so a value outside its static type raises
-- \"no matching equation\", which the oracle catches. That makes the
-- property statement observable rather than merely hoped for.
--
-- The oracle is /strict/: any exception at all is a failure. See
-- @Note [Why benign failures are impossible]@ in
-- "YCHR.TypeSoundness.Oracle" for why the generated fragment cannot
-- fail for any reason other than a real violation.
--
-- The second claim (the gradual guarantee) is a separate property; the
-- core AST keeps annotations as data ('YCHR.TypeSoundness.Types.Ann')
-- so that generator can be reused by erasing annotations to @any@.
--
-- What v1 deliberately leaves out, so the coverage is not overread:
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
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Text (Text)
import Data.Text qualified as T
import Hedgehog
  ( Property,
    PropertyT,
    annotate,
    cover,
    evalIO,
    failure,
    forAllWith,
    property,
    withTests,
  )
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Hedgehog (testProperty)
import YCHR.Internal.Compile.Pipeline (CompiledProgram (..))
import YCHR.Internal.Display (Display (..))
import YCHR.Internal.Meta (metaHostCallRegistry)
import YCHR.Internal.Runtime.Interpreter (baseHostCallRegistry)
import YCHR.Internal.TypeCheck (TypeCheckResult (..), typeCheckProgram)
import YCHR.Internal.Types (Term (..))
import YCHR.Run (Error (..), compileModules, runProgramWithQuery)
import YCHR.TypeSoundness.Gen (genProgram)
import YCHR.TypeSoundness.Instrument (prepare)
import YCHR.TypeSoundness.Oracle (conforms, describeException)
import YCHR.TypeSoundness.Render (renderModule, renderQuery)
import YCHR.TypeSoundness.Types

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
      mapM_ (annotate . ("compile warning: " ++) . displayMsg) ws
      pure cp
  tc <- evalIO (typeCheckProgram cp.desugaredProgram)
  mapM_ (annotate . ("typecheck warning: " ++) . displayMsg) tc.warnings
  unless (null tc.errors) $ do
    mapM_ (annotate . ("type error: " ++) . displayMsg) tc.errors
    failure
  outcome <-
    evalIO
      ( try @SomeException
          (runProgramWithQuery cp (baseHostCallRegistry <> metaHostCallRegistry) query)
      )
  bindings <- case outcome of
    Left exc -> annotate (describeException exc) >> failure
    Right bs -> pure bs
  mapM_ (checkProbe bindings) prog.goal.probes
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
-- Five of these six events are decided by generators the goal- and
-- guard-seeding of @Note [Firing rates]@ does not touch, so the rates
-- above are as first measured. The exception is the body-tell label,
-- which reads the /prepared/ program and so depends on how much
-- 'YCHR.TypeSoundness.Instrument.pruneTells' dropped, and hence on the
-- goal size that work widened; measured, the extra pruning is nil and
-- the rate is unchanged. Re-measuring all six after that work
-- reproduced them to within two points.
--
-- Only the body-tell floor is loose: its rate sits near 50%, where the
-- binomial spread at @withTests 100@ is widest, so a discriminating
-- floor would flake. The other five bind, and the degeneration trips
-- all of them at once.
--
-- What these do /not/ measure is whether a rule actually fires — that
-- is a runtime fact, and nothing observable crosses back from the CHR
-- session. It is measured out of band by splicing a body that always
-- raises (@Z = 1, Z = 2@) into the rules of interest and counting the
-- runs that then fail; see @Note [Firing rates]@ in
-- "YCHR.TypeSoundness.Gen". Redo that measurement rather than trusting
-- the labels below if the generator's firing behaviour is ever in
-- question.
coverShape :: Program -> PropertyT IO ()
coverShape prog = do
  cover 65 "a rule joins two head constraints" (any ((> 1) . length . ruleHeads) rs)
  cover 30 "a rule body tells a constraint" (any (any isTell . (.body)) rs)
  cover 62 "a rule body binds a variable" (any (any isBind . (.body)) rs)
  cover 62 "a rule has a guard" (any (not . null . (.guards)) rs)
  cover 45 "the goal has a probe" (not (null prog.goal.probes))
  cover 46 "the program declares an algebraic type" (not (null prog.adts))
  where
    rs = prog.rules
    isBind it = case it of
      BIs {} -> True
      BUnify {} -> True
      _ -> False

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
