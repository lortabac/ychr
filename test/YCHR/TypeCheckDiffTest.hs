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
-- Three comparisons per directory, all against the same program:
--
--   * the whole program, through @check_program@;
--   * the program's own rule bodies taken as one goal list;
--   * each @.goal@ file, resolved the way a real query is.
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

import Control.Exception (SomeException, try)
import Control.Monad (filterM)
import Data.List (delete, intercalate, sort)
import Data.Text qualified as T
import Data.Text.IO qualified as TIO
import GHC.Clock (getMonotonicTime)
import Hedgehog (Property, annotate, evalIO, failure, forAllWith, property, withTests)
import System.Directory (doesDirectoryExist, listDirectory)
import System.Environment (lookupEnv)
import System.FilePath (dropExtension, takeExtension, takeFileName, (</>))
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertBool, assertFailure, testCase)
import Test.Tasty.Hedgehog (testProperty)
import YCHR.Internal.Compile.Pipeline (CompiledProgram (..), compileFiles)
import YCHR.Internal.Desugared qualified as D
import YCHR.Internal.Display (Display (..))
import YCHR.Internal.Loc (SourceLoc, dummyLoc)
import YCHR.Internal.Parsed (AnnP (..))
import YCHR.Internal.TypeCheck (typeCheckGoals, typeCheckProgram)
import YCHR.Internal.TypeCheck.Error (TypeCheckResult (..))
import YCHR.Internal.TypeCheck.V2 (typeCheckGoalsV2, typeCheckProgramV2)
import YCHR.Run (Error, ResolvedQuery (..), compileModules, resolveQueryGoals)
import YCHR.TypeSoundness.Gen (Mode (..), genProgramWith)
import YCHR.TypeSoundness.Instrument (prepare)
import YCHR.TypeSoundness.Render (renderModule, renderQuery)

-- | What one comparison contributed.
data Outcome
  = -- | Nothing to compare. Either the program does not compile — a
    -- compilation-negative golden test — or a @.goal@ file does not
    -- resolve, which is what a goal-negative case rejecting its query
    -- before type-checking looks like.
    Skipped
  | Matched
  | -- | Rendered difference, ready to print.
    Mismatch String

-- | One comparison: what was compared, how it came out, and what each
-- checker spent reaching it.
data Item = Item
  { name :: String,
    outcome :: Outcome,
    oldSeconds :: Double,
    newSeconds :: Double
  }

-- | One corpus directory's verdicts. 'programItem' is kept apart from
-- the goal comparisons because the two are counted and timed
-- separately: the program corpus is one item per directory, the goal
-- corpus several, and the two entry points cost very different
-- amounts.
data Checked = Checked
  { programItem :: Item,
    goalItems :: [Item]
  }

tests :: IO TestTree
tests = do
  strict <- (== Just "strict") <$> lookupEnv "YCHR_TC_DIFF"
  pure
    ( testGroup
        "TypeCheckDiff"
        [ testCase "golden corpus" (runCorpus strict),
          testProperty "generated programs (closed)" (prop_generated Closed),
          testProperty "generated programs (open)" (prop_generated Open)
        ]
    )

-- | The differential over the type-soundness generator
-- ("YCHR.TypeSoundness.Gen"), which is the strongest oracle the two
-- checkers have for polymorphism, rigid type variables, guard-derived
-- evidence and bounded polymorphism: the golden corpus has a handful
-- of programs exercising those, and this generates a fresh one every
-- test.
--
-- Both entry points are compared on each program — the program itself,
-- and the generated query's goals — and, unlike the corpus
-- comparison above, this one /asserts/ rather than reports. The corpus
-- is a progress metric during the port; a divergence here is a real
-- disagreement on a program neither checker has seen.
--
-- What it does /not/ assert is that the generated program type-checks
-- clean; "YCHR.TypeSoundnessTest" is where that claim lives. This one
-- only cares that the two checkers say the same thing.
prop_generated :: Mode -> Property
prop_generated mode = withTests 200 $
  property $ do
    raw <- forAllWith (T.unpack . renderModule . prepare) (genProgramWith mode)
    let prog = prepare raw
    cp <- case compileModules False [("gen.chr", renderModule prog)] of
      Left err -> annotate ("compile error: " ++ displayMsg (err :: Error)) >> failure
      Right (cp, _) -> pure cp
    programItem <-
      evalIO
        ( diffed
            "program"
            (typeCheckProgram cp.desugaredProgram)
            (typeCheckProgramV2 cp.desugaredProgram)
        )
    assertMatched programItem
    resolved <- evalIO (resolveQueryGoals cp (renderQuery prog))
    goalItem <-
      evalIO
        ( diffGoals
            "query"
            resolved.goalProgram
            dummyLoc
            (Just "query")
            resolved.liftedGoals
        )
    assertMatched goalItem
  where
    assertMatched i = case i.outcome of
      Mismatch m -> annotate m >> failure
      _ -> pure ()

runCorpus :: Bool -> IO ()
runCorpus strict = do
  dirs <- corpusDirs
  checks <- mapM checkDir dirs
  let programs = [(d, c.programItem) | (d, c) <- zip dirs checks]
      goals = [(d, i) | (d, c) <- zip dirs checks, i <- c.goalItems]
      mismatches = [x | x@(_, i) <- programs ++ goals, isMismatch i.outcome]
      summary =
        intercalate
          "\n  "
          [ tally "golden programs" (map snd programs),
            tally "goal lists" (map snd goals)
          ]
  if strict && not (null mismatches)
    then assertFailure (unlines (summary : map renderMismatch mismatches))
    else putStrLn ("\n  " ++ summary)
  where
    millis s = show (round (s * 1000) :: Int)
    renderMismatch (d, i) = "  " ++ d ++ " [" ++ i.name ++ "]:\n" ++ renderOutcome i.outcome
    renderOutcome (Mismatch m) = m
    renderOutcome _ = ""
    isMismatch (Mismatch _) = True
    isMismatch _ = False
    isMatched Matched = True
    isMatched _ = False
    isSkipped Skipped = True
    isSkipped _ = False
    tally what items =
      "typecheck diff over "
        ++ show (length items)
        ++ " "
        ++ what
        ++ ": "
        ++ show (length (filter (isMatched . (.outcome)) items))
        ++ " matched, "
        ++ show (length (filter (isMismatch . (.outcome)) items))
        ++ " differing, "
        ++ show (length (filter (isSkipped . (.outcome)) items))
        ++ " skipped, in "
        ++ millis (sum (map (.oldSeconds) items))
        ++ " ms (old) vs "
        ++ millis (sum (map (.newSeconds) items))
        ++ " ms (V2)"

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
      goalNegative = [dropExtension e | e <- entries, takeExtension e == ".error"]
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
      pure Checked {programItem = skippedItem "program", goalItems = []}
    Right (prog, _) -> do
      programItem <-
        diffed
          "program"
          (typeCheckProgram prog.desugaredProgram)
          (typeCheckProgramV2 prog.desugaredProgram)
      bodyItem <- diffRuleBodyGoals prog.desugaredProgram
      fromFiles <-
        mapM
          (\g -> diffGoalFile prog (dir </> g) (dropExtension g `elem` goalNegative))
          (sort [f | f <- entries, takeExtension f == ".goal"])
      pure Checked {programItem, goalItems = bodyItem : fromFiles}

-- | True when a directory's cases include a compilation-negative one:
-- an @.error@ with no @.goal@ of the same basename (see the golden
-- harness's discovery rules in "YCHR.GoldenTest").
isCompilationNegative :: [FilePath] -> Bool
isCompilationNegative entries =
  any (`notElem` goals) [dropExtension e | e <- entries, takeExtension e == ".error"]
  where
    goals = [dropExtension g | g <- entries, takeExtension g == ".goal"]

-- | Run both checkers over the same input and compare, recording what
-- each spent.
diffed :: String -> IO TypeCheckResult -> IO TypeCheckResult -> IO Item
diffed itemName old new = do
  (oldResult, oldTime) <- timed old
  (newResult, newTime) <- timed new
  pure
    Item
      { name = itemName,
        outcome = compareResults oldResult newResult,
        oldSeconds = oldTime,
        newSeconds = newTime
      }

-- | An item with nothing to compare, and so nothing to time.
skippedItem :: String -> Item
skippedItem itemName =
  Item {name = itemName, outcome = Skipped, oldSeconds = 0, newSeconds = 0}

timed :: IO a -> IO (a, Double)
timed action = do
  started <- getMonotonicTime
  result <- action
  finished <- getMonotonicTime
  pure (result, finished - started)

-- | Compare the two goal entry points over the program's own rule
-- bodies as a stand-in goal list.
--
-- The corpus goal checking is really for is the @.goal@ files, which
-- 'diffGoalFile' runs; this is the broader one. A rule body
-- exercises every 'D.BodyGoal' shape the language has, and the corpus
-- has thousands of them, where the @.goal@ files are nearly all a
-- single tell of ground arguments. Checked as goals the bodies lose
-- their head variables' declared types, so their diagnostics are not
-- the ones the same program produces as a program — which is the
-- point: it is a second, differently shaped population of checking
-- units.
--
-- Both label shapes the driver can build are used, so that neither
-- spelling can rot: a program with rules gets a label, one without
-- gets none. Across the corpus both arms run many times over.
diffRuleBodyGoals :: D.Program -> IO Item
diffRuleBodyGoals prog = diffGoals "rule bodies as goals" prog dummyLoc label goals
  where
    goals = concatMap (\r -> r.body.node) prog.rules
    label = if null prog.rules then Nothing else Just "goal"

-- | Compare the two goal entry points over one @.goal@ file, resolved
-- exactly as 'YCHR.Run.prepareQuery' resolves a real query — including
-- the lambda lifting, so a query that writes @fun(X) -> ... end@ is
-- checked against a program extended with the lifted function.
--
-- A goal that does not resolve at all is skipped, but only when the
-- directory says it should be: a goal-negative golden may reject its
-- query at rename or desugar time, before either checker sees it.
-- Anywhere else an unresolvable goal is coverage quietly leaving the
-- corpus — or a regression in 'resolveQueryGoals' — so it fails
-- instead of counting as a skip. Hence @expectedToFail@, which is
-- whether the case has an @.error@ file.
diffGoalFile :: CompiledProgram -> FilePath -> Bool -> IO Item
diffGoalFile prog path expectedToFail = do
  src <- TIO.readFile path
  resolved <- try @SomeException (resolveQueryGoals prog (T.strip src))
  case resolved of
    Left err -> do
      assertBool
        ("corpus goal failed to resolve: " ++ path ++ "\n" ++ show err)
        expectedToFail
      pure (skippedItem itemName)
    Right query ->
      diffGoals itemName query.goalProgram dummyLoc (Just "query") query.liftedGoals
  where
    itemName = takeFileName path

diffGoals ::
  String -> D.Program -> SourceLoc -> Maybe T.Text -> [D.BodyGoal] -> IO Item
diffGoals itemName prog loc label goals =
  diffed
    itemName
    (typeCheckGoals prog loc label goals)
    (typeCheckGoalsV2 prog loc label goals)

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
