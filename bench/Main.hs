{-# LANGUAGE OverloadedStrings #-}

-- | Criterion benchmarks for the YCHR Haskell interpreter.
--
-- Each benchmark loads a CHR program and its matching goal from
-- @test/golden/<name>/@ once at startup, then measures only the call to
-- 'runGoalConstraint' — i.e. the actual VM execution with runtime
-- initialization, excluding parsing, renaming, desugaring, and CHR-to-VM
-- compilation.
module Main (main) where

import Criterion.Main
import Data.Text qualified as T
import Data.Text.IO qualified as TIO
import System.FilePath ((<.>), (</>))
import YCHR.Internal.Compile.Pipeline (CompiledProgram (..))
import YCHR.Internal.Meta (metaHostCallRegistry)
import YCHR.Internal.Parser (parseConstraint)
import YCHR.Internal.Runtime.Interpreter (baseHostCallRegistry)
import YCHR.Internal.Runtime.Registry (HostCallRegistry)
import YCHR.Internal.TypeCheck (typeCheckProgram)
import YCHR.Internal.TypeCheck.V2 (typeCheckProgramV2)
import YCHR.Run
  ( compileFiles,
    prepareGoalTerm,
    runGoalConstraint,
  )
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
    -- Transitive-closure leq: a store-heavy workload whose activations run
    -- the partner searches in occurrences 2-7 rather than early-dropping on
    -- reflexivity, so it exercises the passive-occurrences optimization
    -- (unlike the "leq" case, whose leq(X, X) goal fires reflexivity first).
    "leq_closure",
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
  parsedGoal <- case parseConstraint "<bench>" (T.strip goalText) of
    Left err -> fail ("goal parse failed for " ++ name ++ ": " ++ show err)
    Right (Left validErr) -> fail ("goal parse failed for " ++ name ++ ": " ++ show validErr)
    Right (Right c) -> pure c
  -- Canonicalize the goal's arguments here, at setup time, so criterion
  -- measures VM execution only. 'runGoalConstraint' takes the prepared
  -- goal as-is; the convenience entry point 'runProgramWithGoalDSL'
  -- would redo this work on every iteration.
  (goal, _warnings) <- prepareGoalTerm prog parsedGoal
  pure (BenchCase name prog goal)

-- | The host call registry used by all benchmarks. Same combination as the
-- golden test harness in @test/YCHR/GoldenTest.hs@.
benchHostCalls :: HostCallRegistry
benchHostCalls = baseHostCallRegistry <> metaHostCallRegistry

-- | Build one criterion benchmark for a loaded case.
makeBench :: BenchCase -> Benchmark
makeBench bc =
  bench bc.name $
    whnfIO (runGoalConstraint bc.program benchHostCalls bc.goal)

-- | The program the type-checker benchmarks run over: library-heavy, so
-- the declaration environment (prelude + pairs) dominates, which is the
-- workload the checkers spend their time on across the golden corpus.
typeCheckProgramName :: String
typeCheckProgramName = "pairs_library"

-- | Benchmark both type checkers over one compiled program. Compilation
-- happens once at startup; each iteration measures a whole checking
-- session, exactly what @ychr check@ (V1) or the V2 driver pays per
-- program.
makeTypeCheckBenches :: CompiledProgram -> [Benchmark]
makeTypeCheckBenches prog =
  [ bench ("typecheck/" ++ typeCheckProgramName) $
      whnfIO (typeCheckProgram prog.desugaredProgram),
    bench ("typecheck-v2/" ++ typeCheckProgramName) $
      whnfIO (typeCheckProgramV2 prog.desugaredProgram)
  ]

loadTypeCheckProgram :: IO CompiledProgram
loadTypeCheckProgram = do
  let chrPath =
        goldenDir </> typeCheckProgramName </> typeCheckProgramName <.> "chr"
  result <- compileFiles False [chrPath]
  case result of
    Left err ->
      fail ("compile failed for " ++ typeCheckProgramName ++ ": " ++ show err)
    Right (p, _warnings) -> pure p

main :: IO ()
main = do
  cases <- traverse loadCase benchmarkPrograms
  tcProgram <- loadTypeCheckProgram
  defaultMain (map makeBench cases ++ makeTypeCheckBenches tcProgram)
