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
import YCHR.Pretty (prettyBindings)
import YCHR.Runtime.Interpreter (defaultHostCallRegistry)

tests :: IO TestTree
tests = do
  let queryDir = "test/golden/queries"
  names <-
    sort
      . map dropExtension
      . filter ((== ".txt") . takeExtension)
      <$> listDirectory queryDir
  trees <- mapM (makeGoldenTest "test/golden") names
  pure (testGroup "Golden" trees)

makeGoldenTest :: FilePath -> String -> IO TestTree
makeGoldenTest base name = pure $ testCase name $ do
  prog <-
    compileFiles [base </> "programs" </> name <.> "chr"]
      >>= either (assertFailure . show) pure
  query <- TIO.readFile (base </> "queries" </> name <.> "txt")
  expected <- readFile (base </> "expected" </> name <.> "txt")
  (_, bindings) <- runProgramWithGoal prog defaultHostCallRegistry (T.strip query)
  prettyBindings bindings @?= expected
