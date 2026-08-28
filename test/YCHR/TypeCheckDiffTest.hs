{-# LANGUAGE OverloadedStrings #-}

-- | Differential harness for the two type-checkers.
--
-- The all-CHR checker ("YCHR.Internal.TypeCheck.V2") is being ported
-- from the Haskell-driven one ("YCHR.Internal.TypeCheck") a milestone
-- at a time. This runs both over the same corpus — every program under
-- @test\/golden@ that compiles, which is every directory except the
-- compilation-negative ones — and compares their diagnostics as
-- multisets: same payloads, same labels, same locations, same origins,
-- and the same split between errors and warnings (which is what pins
-- per-unit warning suppression).
--
-- Until the port is finished the V2 checker reports strictly less than
-- the old one, so the harness runs in /report/ mode by default: it
-- prints how far along the corpus is and passes regardless. Setting
--
-- > YCHR_TC_DIFF=strict
--
-- turns every mismatch into a failure. The intent is to flip the
-- default once V2 is complete; until then the printed counts are the
-- progress metric, and the timings are the performance one.
module YCHR.TypeCheckDiffTest (tests) where

import Control.Monad (filterM)
import Data.List (delete, sort)
import GHC.Clock (getMonotonicTime)
import System.Directory (doesDirectoryExist, listDirectory)
import System.Environment (lookupEnv)
import System.FilePath (dropExtension, takeExtension, (</>))
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertBool, assertFailure, testCase)
import YCHR.Internal.Compile.Pipeline (CompiledProgram (..), compileFiles)
import YCHR.Internal.Desugared qualified as D
import YCHR.Internal.Loc (dummyLoc)
import YCHR.Internal.Parsed (AnnP (..))
import YCHR.Internal.TypeCheck (typeCheckProgram)
import YCHR.Internal.TypeCheck.Error (TypeCheckResult (..))
import YCHR.Internal.TypeCheck.V2 (typeCheckGoalsV2, typeCheckProgramV2)

-- | What one corpus program contributed.
data Outcome
  = -- | The program does not compile — a compilation-negative golden
    -- test. Nothing to type-check.
    Skipped
  | Matched
  | -- | Rendered difference, ready to print.
    Mismatch String

-- | One program's verdict and what each checker spent reaching it.
data Checked = Checked
  { outcome :: Outcome,
    oldSeconds :: Double,
    newSeconds :: Double
  }

tests :: IO TestTree
tests = do
  strict <- (== Just "strict") <$> lookupEnv "YCHR_TC_DIFF"
  pure
    ( testGroup
        "TypeCheckDiff"
        [testCase "golden corpus" (runCorpus strict)]
    )

runCorpus :: Bool -> IO ()
runCorpus strict = do
  dirs <- corpusDirs
  checks <- mapM checkDir dirs
  let outcomes = map (.outcome) checks
      mismatches = [(d, m) | (d, Mismatch m) <- zip dirs outcomes]
      matched = length [() | Matched <- outcomes]
      skipped = length [() | Skipped <- outcomes]
      checkedCount = length dirs - skipped
      summary =
        "typecheck diff over "
          ++ show (length dirs)
          ++ " golden programs: "
          ++ show matched
          ++ " matched, "
          ++ show (length mismatches)
          ++ " differing, "
          ++ show skipped
          ++ " uncompilable (skipped)\n  "
          ++ show checkedCount
          ++ " checked in "
          ++ millis (sum (map (.oldSeconds) checks))
          ++ " ms (old) vs "
          ++ millis (sum (map (.newSeconds) checks))
          ++ " ms (V2)"
  if strict && not (null mismatches)
    then assertFailure (unlines (summary : map renderMismatch mismatches))
    else putStrLn ("\n  " ++ summary)
  where
    millis s = show (round (s * 1000) :: Int)
    renderMismatch (d, m) = "  " ++ d ++ ":\n" ++ m

-- | Every golden test directory, by path. A directory without @.chr@
-- files is not a test.
corpusDirs :: IO [FilePath]
corpusDirs = do
  let root = "test/golden"
  entries <- sort <$> listDirectory root
  dirs <- filterM (doesDirectoryExist . (root </>)) entries
  filterM hasChr (map (root </>) dirs)
  where
    hasChr d = any ((== ".chr") . takeExtension) <$> listDirectory d

checkDir :: FilePath -> IO Checked
checkDir dir = do
  entries <- listDirectory dir
  let files = sort [dir </> f | f <- entries, takeExtension f == ".chr"]
  compiled <- compileFiles False files
  case compiled of
    Left err -> do
      -- A program that does not compile is only expected in a
      -- compilation-negative golden — a directory with a `.error` and
      -- no matching `.goal`. Anywhere else it is coverage quietly
      -- leaving the corpus, so say so.
      assertBool
        ("corpus program failed to compile: " ++ dir ++ "\n" ++ show err)
        (isCompilationNegative entries)
      pure Checked {outcome = Skipped, oldSeconds = 0, newSeconds = 0}
    Right (prog, _) -> do
      (old, oldTime) <- timed (typeCheckProgram prog.desugaredProgram)
      (new, newTime) <- timed (typeCheckProgramV2 prog.desugaredProgram)
      smokeGoals prog.desugaredProgram
      pure
        Checked
          { outcome = compareResults old new,
            oldSeconds = oldTime,
            newSeconds = newTime
          }

-- | True when a directory's cases include a compilation-negative one:
-- an @.error@ with no @.goal@ of the same basename (see the golden
-- harness's discovery rules in "YCHR.GoldenTest").
isCompilationNegative :: [FilePath] -> Bool
isCompilationNegative entries =
  any (`notElem` goals) [dropExtension e | e <- entries, takeExtension e == ".error"]
  where
    goals = [dropExtension g | g <- entries, takeExtension g == ".goal"]

timed :: IO a -> IO (a, Double)
timed action = do
  started <- getMonotonicTime
  result <- action
  finished <- getMonotonicTime
  pure (result, finished - started)

-- | Run the goal entry point too, on the program's own rule bodies as
-- a stand-in goal list. Goal checking is not ported yet, so there is
-- nothing to compare against; what this pins is that the second entry
-- point's encoding and decoding round-trip — the goal list, the
-- location, and the label all reach CHR in a shape it accepts. A
-- mis-encoding raises rather than returning, so the assertion is that
-- this returns at all.
-- Both label shapes the driver can build are used, so that neither
-- spelling can rot: a program with rules gets a label, one without
-- gets none. Across the corpus both arms run many times over.
smokeGoals :: D.Program -> IO ()
smokeGoals prog = do
  result <- typeCheckGoalsV2 prog dummyLoc label goals
  case (result.errors, result.warnings) of
    ([], []) -> pure ()
    _ -> assertFailure "the goal stub reported diagnostics"
  where
    goals = concatMap (\r -> r.body.node) prog.rules
    label = if null prog.rules then Nothing else Just "goal"

-- | Compare two results as multisets of rendered diagnostics. The
-- rendering goes through 'show', so it covers the payload, the label,
-- the source location, and the origin p-expr — everything a rendered
-- diagnostic is built from.
compareResults :: TypeCheckResult -> TypeCheckResult -> Outcome
compareResults old new
  | oldErrs == newErrs && oldWarns == newWarns = Matched
  | otherwise =
      Mismatch
        ( unlines
            ( section "errors" oldErrs newErrs
                ++ section "warnings" oldWarns newWarns
            )
        )
  where
    oldErrs = sort (map show old.errors)
    newErrs = sort (map show new.errors)
    oldWarns = sort (map show old.warnings)
    newWarns = sort (map show new.warnings)
    section what lhs rhs
      | lhs == rhs = []
      | otherwise =
          [ "    " ++ what ++ " only in " ++ side ++ ": " ++ show x
          | (side, these, those) <- [("the old checker", lhs, rhs), ("V2", rhs, lhs)],
            x <- these `without` those
          ]
    -- Multiset difference, not 'filter (`notElem` ...)': two checkers
    -- that report the same diagnostic a different number of times
    -- differ, and the report has to say so rather than come out empty.
    without = foldl (flip delete)
