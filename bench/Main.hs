{-# LANGUAGE OverloadedStrings #-}

-- | Criterion benchmarks for the YCHR Haskell interpreter.
--
-- Each benchmark loads a CHR program from @test/golden/programs/@ and the
-- matching goal from @test/golden/goals/@ once at startup, then measures
-- only the call to 'runProgramWithGoalDSL' — i.e. the actual VM execution
-- with runtime initialization, excluding parsing, renaming, desugaring,
-- and CHR-to-VM compilation.
module Main (main) where

import Criterion.Main
import Data.Text qualified as T
import Data.Text.IO qualified as TIO
import System.FilePath ((<.>), (</>))
import YCHR.Run
  ( CompiledProgram,
    compileFiles,
    runProgramWithGoalDSL,
  )
import YCHR.Meta (metaHostCallRegistry)
import YCHR.Parser (parseConstraint)
import YCHR.Runtime.Interpreter (baseHostCallRegistry)
import YCHR.Runtime.Registry (HostCallRegistry)
import YCHR.Types (Constraint)

-- | A benchmark case after all setup work is complete.
data BenchCase = BenchCase
  { name :: String,
    program :: CompiledProgram,
    goal :: Constraint
  }

-- | Programs to benchmark. Each entry is a golden-test program name
-- (without extension); the harness loads @programs/<name>.chr@ and
-- @goals/<name>.goal@ from @test/golden@.
benchmarkPrograms :: [String]
benchmarkPrograms =
  [ "guard",
    "leq",
    "fib",
    "sum_list_test",
    "graph_test",
    "lambda_test"
  ]

goldenDir :: FilePath
goldenDir = "test/golden"

-- | Load a program and parse its goal. All work here is done once, at
-- startup, and is NOT measured by criterion.
loadCase :: String -> IO BenchCase
loadCase name = do
  let chrPath = goldenDir </> "programs" </> name <.> "chr"
      goalPath = goldenDir </> "goals" </> name <.> "goal"
  result <- compileFiles False [chrPath]
  prog <- case result of
    Left err -> fail ("compile failed for " ++ name ++ ": " ++ show err)
    Right (p, _warnings) -> pure p
  goalText <- TIO.readFile goalPath
  goal <- case parseConstraint "<bench>" (T.strip goalText) of
    Left err -> fail ("goal parse failed for " ++ name ++ ": " ++ show err)
    Right c -> pure c
  pure (BenchCase name prog goal)

-- | The host call registry used by all benchmarks. Same combination as the
-- golden test harness in @test/YCHR/GoldenTest.hs@.
benchHostCalls :: HostCallRegistry
benchHostCalls = baseHostCallRegistry <> metaHostCallRegistry

-- | Build one criterion benchmark for a loaded case.
makeBench :: BenchCase -> Benchmark
makeBench bc =
  bench bc.name $
    whnfIO (runProgramWithGoalDSL bc.program benchHostCalls bc.goal)

main :: IO ()
main = do
  cases <- traverse loadCase benchmarkPrograms
  defaultMain (map makeBench cases)
