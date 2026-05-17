{-# LANGUAGE OverloadedStrings #-}

module YCHR.GoldenTest (tests) where

import Control.Exception (SomeException, fromException, try)
import Control.Monad (filterM)
import Data.Char (isSpace)
import Data.List (isInfixOf, partition, sort, sortOn)
import Data.Text qualified as T
import Data.Text.IO qualified as TIO
import System.Directory (doesDirectoryExist, listDirectory)
import System.FilePath (dropExtension, takeExtension, (<.>), (</>))
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertBool, assertFailure, testCase, (@?=))
import YCHR.Display (Display (..))
import YCHR.Meta (metaHostCallRegistry)
import YCHR.Pretty (prettyBindings)
import YCHR.Run (CompiledProgram (..), Error, compileFiles, runProgramWithGoal)
import YCHR.Runtime.Interpreter (baseHostCallRegistry)
import YCHR.TypeCheck (typeCheckProgram)

data Case
  = Positive String FilePath FilePath
  | Negative String FilePath
  | -- | Compilation and program-level type-checking succeed, but running
    -- the goal must throw an error whose displayed message contains the
    -- given error code. Encoded by colocating @<basename>.goal@ and
    -- @<basename>.error@ in the same test directory.
    GoalNegative String FilePath FilePath

data TestSpec = TestSpec
  { testName :: String,
    chrFiles :: [FilePath],
    cases :: [Case]
  }

tests :: IO TestTree
tests = do
  let root = "test/golden"
  entries <- sort <$> listDirectory root
  dirs <- filterM (doesDirectoryExist . (root </>)) entries
  trees <- mapM (makeGoldenTest root) dirs
  pure (testGroup "Golden" trees)

makeGoldenTest :: FilePath -> String -> IO TestTree
makeGoldenTest root name = do
  let dir = root </> name
  files <- sort <$> listDirectory dir
  let chrs = [dir </> f | f <- files, takeExtension f == ".chr"]
      goals = [f | f <- files, takeExtension f == ".goal"]
      expecteds = [f | f <- files, takeExtension f == ".expected"]
      errors = [f | f <- files, takeExtension f == ".error"]
  pure $ case validate dir name chrs goals expecteds errors of
    Left msg -> testCase name (assertFailure msg)
    Right spec -> testGroup spec.testName (map (makeCase spec) spec.cases)

validate ::
  FilePath ->
  String ->
  [FilePath] ->
  [FilePath] ->
  [FilePath] ->
  [FilePath] ->
  Either String TestSpec
validate dir name chrs goals expecteds errors
  | null chrs =
      Left ("No .chr files in " ++ dir)
  | null goals && null errors =
      Left ("No .goal or .error files in " ++ dir)
  | not (null goals) && not (null errors) = do
      -- Mixed-mode directory: each .goal must be paired with either a
      -- .expected (positive) or a .error (goal-negative). A bare .error
      -- (with no matching .goal) in the same directory is rejected
      -- because we'd otherwise have to disambiguate it from a regular
      -- compilation-negative case.
      let goalNames = sort (map dropExtension goals)
          expectedNames = map dropExtension expecteds
          errorNames = map dropExtension errors
          (positiveMatched, unmatchedAfterExpected) =
            partition (`elem` expectedNames) goalNames
          (goalNegMatched, orphanGoals) =
            partition (`elem` errorNames) unmatchedAfterExpected
          orphanExpecteds = filter (`notElem` goalNames) expectedNames
          orphanErrors = filter (`notElem` goalNames) errorNames
      case (orphanGoals, orphanExpecteds, orphanErrors) of
        ([], [], []) ->
          let pcases =
                [ Positive c (dir </> c <.> "goal") (dir </> c <.> "expected")
                | c <- positiveMatched
                ]
              gncases =
                [ GoalNegative c (dir </> c <.> "goal") (dir </> c <.> "error")
                | c <- goalNegMatched
                ]
           in Right (TestSpec name chrs (sortCases (pcases ++ gncases)))
        (gs, es, ers) ->
          Left
            ( "Orphan files in "
                ++ dir
                ++ ":"
                ++ concatMap (("\n  missing .expected or .error for " ++) . (<.> "goal")) gs
                ++ concatMap (("\n  missing .goal for " ++) . (<.> "expected")) es
                ++ concatMap
                  ( ("\n  bare .error not paired with a .goal in mixed dir for " ++)
                      . (<.> "error")
                  )
                  ers
            )
  | not (null errors) =
      let ecases =
            [ Negative (dropExtension e) (dir </> e)
            | e <- sort errors
            ]
       in Right (TestSpec name chrs ecases)
  | otherwise = do
      let goalNames = sort (map dropExtension goals)
          expectedNames = sort (map dropExtension expecteds)
          (matched, orphanGoals) =
            partition (`elem` expectedNames) goalNames
          orphanExpecteds = filter (`notElem` goalNames) expectedNames
      case (orphanGoals, orphanExpecteds) of
        ([], []) ->
          let pcases =
                [ Positive c (dir </> c <.> "goal") (dir </> c <.> "expected")
                | c <- matched
                ]
           in Right (TestSpec name chrs pcases)
        (gs, es) ->
          Left
            ( "Orphan files in "
                ++ dir
                ++ ":"
                ++ concatMap (("\n  missing .expected for " ++) . (<.> "goal")) gs
                ++ concatMap (("\n  missing .goal for " ++) . (<.> "expected")) es
            )

sortCases :: [Case] -> [Case]
sortCases = sortOn caseName
  where
    caseName (Positive n _ _) = n
    caseName (Negative n _) = n
    caseName (GoalNegative n _ _) = n

makeCase :: TestSpec -> Case -> TestTree
makeCase spec c = case c of
  Positive cname gf ef -> testCase cname (runPositive spec gf ef)
  Negative cname ef -> testCase cname (runNegative spec ef)
  GoalNegative cname gf ef -> testCase cname (runGoalNegative spec gf ef)

runPositive :: TestSpec -> FilePath -> FilePath -> IO ()
runPositive spec goalFile expectedFile = do
  (prog, _) <-
    compileFiles False spec.chrFiles
      >>= either (assertFailure . show) pure
  typeErrors <- typeCheckProgram prog.desugaredProgram
  case typeErrors of
    [] -> pure ()
    errs ->
      assertFailure
        ("Type errors in " ++ spec.testName ++ ":\n" ++ unlines (map displayMsg errs))
  query <- TIO.readFile goalFile
  expected <- readFile expectedFile
  bindings <-
    runProgramWithGoal prog (baseHostCallRegistry <> metaHostCallRegistry) (T.strip query)
  prettyBindings bindings @?= expected

-- | Compile + program-typecheck must succeed; running the goal must throw
-- an 'Error' whose displayed message contains the expected error code.
-- Any other outcome (success, non-'Error' exception, wrong code) fails
-- the test.
runGoalNegative :: TestSpec -> FilePath -> FilePath -> IO ()
runGoalNegative spec goalFile errorFile = do
  (prog, _) <-
    compileFiles False spec.chrFiles
      >>= either (assertFailure . show) pure
  typeErrors <- typeCheckProgram prog.desugaredProgram
  case typeErrors of
    [] -> pure ()
    errs ->
      assertFailure
        ("Type errors in " ++ spec.testName ++ ":\n" ++ unlines (map displayMsg errs))
  query <- TIO.readFile goalFile
  expectedCode <- trim <$> readFile errorFile
  outcome <-
    try @SomeException $
      runProgramWithGoal
        prog
        ( baseHostCallRegistry
            <> metaHostCallRegistry
        )
        (T.strip query)
  case outcome of
    Right _ ->
      assertFailure
        ("Expected goal to fail with " ++ expectedCode ++ " but it succeeded")
    Left exc -> case fromException exc of
      Just (err :: Error) -> do
        let msg = displayMsg err
        assertBool
          ("Expected error code " ++ expectedCode ++ " in:\n" ++ msg)
          (expectedCode `isInfixOf` msg)
      Nothing ->
        assertFailure
          ("Expected an Error matching " ++ expectedCode ++ " but got: " ++ show exc)
  where
    trim = reverse . dropWhile isSpace . reverse . dropWhile isSpace

runNegative :: TestSpec -> FilePath -> IO ()
runNegative spec errorFile = do
  result <- compileFiles False spec.chrFiles
  expectedCode <- trim <$> readFile errorFile
  case result of
    Left err -> do
      let msg = displayMsg err
      assertBool
        ("Expected error code " ++ expectedCode ++ " in:\n" ++ msg)
        (expectedCode `isInfixOf` msg)
    Right (prog, _) -> do
      typeErrors <- typeCheckProgram prog.desugaredProgram
      case typeErrors of
        [] -> assertFailure "Expected compilation or type checking to fail, but it succeeded"
        errs -> do
          let msg = unlines (map displayMsg errs)
          assertBool
            ("Expected error code " ++ expectedCode ++ " in:\n" ++ msg)
            (expectedCode `isInfixOf` msg)
  where
    trim = reverse . dropWhile isSpace . reverse . dropWhile isSpace
