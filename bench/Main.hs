{-# LANGUAGE OverloadedStrings #-}

-- | Criterion benchmarks for the YCHR Haskell interpreter.
--
-- Each benchmark loads a CHR program and its matching goal from
-- @test/golden/<name>/@ once at startup, then measures only the call to
-- 'runProgramWithGoalDSL' — i.e. the actual VM execution with runtime
-- initialization, excluding parsing, renaming, desugaring, and CHR-to-VM
-- compilation.
module Main (main) where

import Criterion.Main
import Data.Text qualified as T
import Data.Text.IO qualified as TIO
import System.FilePath ((<.>), (</>))
import YCHR.Meta (metaHostCallRegistry)
import YCHR.Parser (parseConstraint)
import YCHR.Rename (renameQueryArgs)
import YCHR.Run
  ( CompiledProgram (..),
    compileFiles,
    resolveQueryConstraint,
    runProgramWithGoalDSL,
  )
import YCHR.Runtime.Interpreter (baseHostCallRegistry)
import YCHR.Runtime.Registry (HostCallRegistry)
import YCHR.Types (Constraint (..))

-- | A benchmark case after all setup work is complete.
data BenchCase = BenchCase
  { name :: String,
    program :: CompiledProgram,
    goal :: Constraint
  }

-- | Programs to benchmark. Each entry is a golden-test directory name
-- under @test/golden@; the harness loads @<name>/<name>.chr@ and
-- @<name>/<name>.goal@ from there.
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
  let chrPath = goldenDir </> name </> name <.> "chr"
      goalPath = goldenDir </> name </> name <.> "goal"
  result <- compileFiles False [chrPath]
  prog <- case result of
    Left err -> fail ("compile failed for " ++ name ++ ": " ++ show err)
    Right (p, _warnings) -> pure p
  goalText <- TIO.readFile goalPath
  Constraint cname cargs <- case parseConstraint "<bench>" (T.strip goalText) of
    Left err -> fail ("goal parse failed for " ++ name ++ ": " ++ show err)
    Right (Left validErr) -> fail ("goal parse failed for " ++ name ++ ": " ++ show validErr)
    Right (Right c) -> pure c
  -- Mirror the query-side canonicalization that runProgramWithGoal does
  -- (rename bare data-constructor references, resolve qualified names),
  -- so the goal's term shapes match the compiled head patterns.
  renamedArgs <- case renameQueryArgs prog.allModules cargs of
    Left errs -> fail ("goal rename failed for " ++ name ++ ": " ++ show errs)
    Right (args, _warnings) -> pure args
  let goal = case resolveQueryConstraint prog (Constraint cname renamedArgs) of
        Right c -> c
        Left _ -> Constraint cname renamedArgs
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
