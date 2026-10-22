-- | Helpers shared across the test suite.
module YCHR.TestHelpers
  ( strip,
    compileOrFail,
    expectErrorContaining,
    countAliveByType,
    countAliveIn,
    runChrIn,
    runChrEmpty,
  )
where

import Control.Exception (SomeException, try)
import Data.Foldable (toList)
import Data.List (isInfixOf)
import Data.Text (Text)
import Test.Tasty.HUnit (assertBool, assertFailure)
import YCHR.Embedded (stdlib)
import YCHR.Internal.Compile.Pipeline (CompiledProgram, compileModules)
import YCHR.Internal.Loc (Ann (..), noAnn)
import YCHR.Internal.PExpr
import YCHR.Internal.Runtime.Monad
  ( Chr,
    SessionConfig,
    emptySessionConfig,
    initSessionEnv,
    runChr,
  )
import YCHR.Internal.Runtime.Store (getStoreSnapshot, isSuspAlive)
import YCHR.Internal.Runtime.Types (Suspension)
import YCHR.Internal.Types (ConstraintType)

-- | Strip source locations from a term for structural comparison.
strip :: Ann PExpr -> PExpr
strip (Ann t _) = case t of
  Compound f args -> Compound f (map (noAnn . strip) args)
  other -> other

-- | Compile source files with the embedded stdlib, failing the test on
-- errors. Warnings are dropped.
compileOrFail :: [(FilePath, Text)] -> IO CompiledProgram
compileOrFail inputs = case compileModules stdlib False inputs of
  Left err -> assertFailure $ show err
  Right (cp, _) -> pure cp

-- | Assert that forcing the given action throws an exception whose
-- message contains the given substring.
expectErrorContaining :: String -> IO a -> IO ()
expectErrorContaining needle act = do
  outcome <- try @SomeException act
  case outcome of
    Left exc ->
      assertBool
        ("expected exception message to contain " ++ show needle ++ ", got: " ++ show exc)
        (needle `isInfixOf` show exc)
    Right _ ->
      assertFailure ("expected exception containing " ++ show needle ++ ", got success")

-- | Count the suspensions of the given constraint type that are still
-- alive in the current session's store.
countAliveByType :: ConstraintType -> Chr Int
countAliveByType cType = do
  snapshot <- getStoreSnapshot cType
  alives <- traverse isSuspAlive (toList snapshot)
  pure (length (filter id alives))

-- | Count how many suspensions in the given list are still alive.
countAliveIn :: [Suspension] -> Chr Int
countAliveIn [] = pure 0
countAliveIn (s : ss) = do
  a <- isSuspAlive s
  rest <- countAliveIn ss
  pure $ (if a then 1 else 0) + rest

-- | Run an action in a fresh session built from the given config.
runChrIn :: SessionConfig -> Chr a -> IO a
runChrIn cfg action = initSessionEnv cfg >>= runChr action

-- | Run an action in a fresh, empty session.
runChrEmpty :: Chr a -> IO a
runChrEmpty = runChrIn emptySessionConfig
