{-# LANGUAGE OverloadedStrings #-}

-- | Helpers shared across the test suite.
module YCHR.TestHelpers
  ( strip,
    compileOrFail,
    expectErrorContaining,
    countAliveByType,
    countAliveIn,
    runChrIn,
    runChrEmpty,
    emptyProgram,
    mkProc,
    histIds,
    leqSource,
    algebraicTD,
    genStringContent,
  )
where

import Control.Exception (SomeException, try)
import Data.Foldable (toList)
import Data.List (isInfixOf)
import Data.Map.Strict qualified as Map
import Data.Text (Text)
import Data.Text qualified as Text
import Hedgehog (Gen)
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import Test.Tasty.HUnit (assertBool, assertFailure)
import YCHR.Embedded (stdlib)
import YCHR.Internal.Compile.Pipeline (CompiledProgram, compileModules)
import YCHR.Internal.Loc (Ann (..), SourceLoc, noAnn)
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
import YCHR.Internal.Types
  ( ConstraintType,
    DataConstructor,
    Name,
    TypeDefinition (..),
    TypeKind (..),
  )
import YCHR.Internal.VM
  ( HistoryIds,
    IdExpr,
    ProcKind (..),
    Procedure (..),
    Program (..),
    Stmt,
    mkHistoryIds,
  )
import YCHR.Internal.VM qualified as VM

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

-- | A VM program with nothing in it. Tests fill in fields with a
-- record update.
emptyProgram :: Program
emptyProgram =
  Program
    { typeNames = [],
      ruleNames = [],
      procedures = [],
      evaluables = [],
      callables = [],
      tellables = [],
      tellablesUnqualified = Map.empty,
      inertTypes = []
    }

-- | Build a 'Procedure' with a placeholder 'procKind'. The kind tag
-- does not matter to the tests that use this, so one neutral value
-- keeps the fixtures short.
mkProc :: VM.Name -> [VM.Name] -> [Stmt] -> Procedure
mkProc n ps body =
  Procedure
    { name = n,
      params = ps,
      body = body,
      procKind = PKReactivateDispatch
    }

-- | A propagation-history tuple in head-position order, the way
-- 'YCHR.Internal.Compile.buildHistoryIds' builds one.
histIds :: [IdExpr] -> HistoryIds
histIds ids = mkHistoryIds (zip [0 :: Int ..] ids)

-- | The leq program.
leqSource :: Text
leqSource =
  ":- module(order, [leq/2]).\n\
  \:- chr_constraint leq/2.\n\
  \\n\
  \reflexivity @ leq(X, X) <=> true.\n\
  \antisymmetry @ leq(X, Y), leq(Y, X) <=> X = Y.\n\
  \idempotence @ leq(X, Y) \\ leq(X, Y) <=> true.\n\
  \transitivity @ leq(X, Y), leq(Y, Z) ==> leq(X, Z).\n"

-- | Build an algebraic type definition positionally (the constructors
-- are wrapped in the 'Algebraic' 'TypeKind').
algebraicTD :: Name -> [Text] -> [DataConstructor] -> SourceLoc -> TypeDefinition
algebraicTD n vs cs loc = TypeDefinition n vs (Algebraic cs) loc

-- | String literal contents, including characters that need escaping.
genStringContent :: Gen Text
genStringContent =
  Text.pack
    <$> Gen.list
      (Range.linear 0 10)
      ( Gen.choice
          [ Gen.alphaNum,
            Gen.element [' ', '"', '\\', '\n', '\t']
          ]
      )
