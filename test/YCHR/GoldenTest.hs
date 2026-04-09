{-# LANGUAGE OverloadedStrings #-}

module YCHR.GoldenTest (tests) where

import Data.List (sort)
import Data.Text qualified as T
import Data.Text.IO qualified as TIO
import System.Directory (listDirectory)
import System.FilePath (dropExtension, takeExtension, (<.>), (</>))
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertFailure, testCase, (@?=))
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
makeGoldenTest base name = pure $ testCase name $ do
  (prog, _) <-
    compileFiles False [base </> "programs" </> name <.> "chr"]
      >>= either (assertFailure . show) pure
  query <- TIO.readFile (base </> "goals" </> name <.> "goal")
  expected <- readFile (base </> "expected" </> name <.> "expected")
  (_, bindings) <- runProgramWithGoal prog (baseHostCallRegistry <> metaHostCallRegistry) (T.strip query)
  prettyBindings bindings @?= expected
