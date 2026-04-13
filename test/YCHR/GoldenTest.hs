{-# LANGUAGE OverloadedStrings #-}

module YCHR.GoldenTest (tests) where

import Data.Char (isSpace)
import Data.List (isInfixOf, sort)
import Data.Text qualified as T
import Data.Text.IO qualified as TIO
import System.Directory (doesFileExist, listDirectory)
import System.FilePath (dropExtension, takeExtension, (<.>), (</>))
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertBool, assertFailure, testCase, (@?=))
import YCHR.Display (Display (..))
import YCHR.EndToEnd (compileFiles, runProgramWithGoal)
import YCHR.Meta (metaHostCallRegistry)
import YCHR.Pretty (prettyBindings)
import YCHR.Runtime.Interpreter (baseHostCallRegistry)

tests :: IO TestTree
tests = do
  let goalDir = "test/golden/goals"
  names <-
    sort
      . map dropExtension
      . filter ((== ".goal") . takeExtension)
      <$> listDirectory goalDir
  trees <- mapM (makeGoldenTest "test/golden") names
  pure (testGroup "Golden" trees)

makeGoldenTest :: FilePath -> String -> IO TestTree
makeGoldenTest base name = do
  let errorFile = base </> "expected" </> name <.> "error"
      expectedFile = base </> "expected" </> name <.> "expected"
  isNeg <- doesFileExist errorFile
  isPos <- doesFileExist expectedFile
  pure $ case (isPos, isNeg) of
    (True, False) -> makePositiveTest base name
    (False, True) -> makeNegativeTest base name
    (True, True) ->
      testCase name $
        assertFailure "Both .expected and .error files exist"
    (False, False) ->
      testCase name $
        assertFailure "Neither .expected nor .error file found"

makePositiveTest :: FilePath -> String -> TestTree
makePositiveTest base name = testCase name $ do
  (prog, _) <-
    compileFiles False [base </> "programs" </> name <.> "chr"]
      >>= either (assertFailure . show) pure
  query <- TIO.readFile (base </> "goals" </> name <.> "goal")
  expected <- readFile (base </> "expected" </> name <.> "expected")
  (_, bindings) <- runProgramWithGoal prog (baseHostCallRegistry <> metaHostCallRegistry) (T.strip query)
  prettyBindings bindings @?= expected

makeNegativeTest :: FilePath -> String -> TestTree
makeNegativeTest base name = testCase name $ do
  result <- compileFiles False [base </> "programs" </> name <.> "chr"]
  expectedCode <- trim <$> readFile (base </> "expected" </> name <.> "error")
  case result of
    Left err -> do
      let msg = displayMsg err
      assertBool
        ("Expected error code " ++ expectedCode ++ " in:\n" ++ msg)
        (expectedCode `isInfixOf` msg)
    Right _ ->
      assertFailure "Expected compilation to fail, but it succeeded"
  where
    trim = reverse . dropWhile isSpace . reverse . dropWhile isSpace
