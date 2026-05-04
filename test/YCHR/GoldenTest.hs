{-# LANGUAGE OverloadedStrings #-}

module YCHR.GoldenTest (tests) where

import Control.Monad (filterM)
import Data.Char (isSpace)
import Data.List (isInfixOf, partition, sort)
import Data.Text qualified as T
import Data.Text.IO qualified as TIO
import System.Directory (doesDirectoryExist, listDirectory)
import System.FilePath (dropExtension, takeExtension, (<.>), (</>))
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertBool, assertFailure, testCase, (@?=))
import YCHR.Display (Display (..))
import YCHR.Meta (metaHostCallRegistry)
import YCHR.Pretty (prettyBindings)
import YCHR.Run (CompiledProgram (..), compileFiles, runProgramWithGoal)
import YCHR.Runtime.Interpreter (baseHostCallRegistry)
import YCHR.TypeCheck (typeCheckProgram)

data Case
  = Positive String FilePath FilePath
  | Negative String FilePath

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
  | not (null goals) && not (null errors) =
      Left ("Test directory " ++ dir ++ " mixes .goal and .error files")
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

makeCase :: TestSpec -> Case -> TestTree
makeCase spec c = case c of
  Positive cname gf ef -> testCase cname (runPositive spec gf ef)
  Negative cname ef -> testCase cname (runNegative spec ef)

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
  (_, bindings) <-
    runProgramWithGoal prog (baseHostCallRegistry <> metaHostCallRegistry) (T.strip query)
  prettyBindings bindings @?= expected

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
