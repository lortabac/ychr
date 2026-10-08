-- | Helpers shared across the test suite.
module YCHR.TestHelpers
  ( strip,
    expectErrorContaining,
    countAliveByType,
    countAliveIn,
  )
where

import Control.Exception (SomeException, try)
import Data.Foldable (toList)
import Data.List (isInfixOf)
import Test.Tasty.HUnit (assertBool, assertFailure)
import YCHR.Internal.Loc (Ann (..), noAnn)
import YCHR.Internal.PExpr
import YCHR.Internal.Runtime.Monad (Chr)
import YCHR.Internal.Runtime.Store (getStoreSnapshot, isSuspAlive)
import YCHR.Internal.Runtime.Types (Suspension)
import YCHR.Internal.Types (ConstraintType)

-- | Strip source locations from a term for structural comparison.
strip :: Ann PExpr -> PExpr
strip (Ann t _) = case t of
  Compound f args -> Compound f (map (noAnn . strip) args)
  other -> other

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
