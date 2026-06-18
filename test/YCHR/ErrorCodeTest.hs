{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | Guards the uniqueness of error codes (@YCHR-NNNNN@).
--
-- Error codes are assigned by hand in "YCHR.Display": one @*ErrorCode@
-- function per error type maps each constructor to a literal 'ErrorCode',
-- plus a handful of standalone constants for codes not tied to a
-- constructor. Nothing in the production code stops two of those literals
-- from colliding. This module reflects over every error constructor with
-- 'Data.Data' and asserts that no code number is reused (except the small,
-- documented 'intentionalShared' allowlist).
--
-- Using 'Data' to enumerate constructors keeps the check exhaustive
-- automatically: a newly added error constructor is picked up by
-- 'dataTypeConstrs' without anyone touching this file. The orphan 'Data'
-- instances below are test-only — 'src/' (and the MicroHs-compiled
-- library) carries no 'Data'/'Typeable' usage.
module YCHR.ErrorCodeTest (tests) where

import Data.Data
  ( Data,
    dataTypeConstrs,
    dataTypeOf,
    fromConstr,
    gunfold,
    mkNoRepType,
    toConstr,
  )
import Data.List (sort)
import Data.Map.Strict qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertFailure, testCase, (@?=))
import YCHR.Collect (CollectError (..))
import YCHR.Compile (CompileError (..))
import YCHR.Desugar (DesugarError (..))
import YCHR.Display
  ( ErrorCode (..),
    collectErrorCode,
    compileErrorCode,
    desugarErrorCode,
    exhaustivenessWarningCode,
    goalNotAConstraintCode,
    lambdasInLiveQueryCode,
    operatorConflictCode,
    parseErrorCode,
    parseValidationErrorCode,
    renameErrorCode,
    renameWarningCode,
    resolveErrorCode,
    runtimeErrorCode,
    typeCheckErrorCode,
  )
import YCHR.Exhaustiveness (ExhaustivenessWarning (..))
import YCHR.Parser (ParseValidationError (..))
import YCHR.Rename (RenameError (..), RenameWarning (..))
import YCHR.Resolve (ResolveError (..))
import YCHR.Resolved qualified as R
import YCHR.TypeCheck (TypeCheckError (..))
import YCHR.Types (Name, Term)

-- ---------------------------------------------------------------------------
-- Opaque Data instances for the error payload types that are not already
-- Data. These satisfy the constraint that the derived 'gunfold' for each
-- error type imposes on its fields; their methods are never invoked because
-- the @*ErrorCode@ functions are lazy in their payloads, so the values we
-- build with 'fromConstr' fill these fields with bottom and never force them.
-- ---------------------------------------------------------------------------

instance Data Name where
  gunfold _ _ = error "Data Name: gunfold (unused)"
  toConstr _ = error "Data Name: toConstr (unused)"
  dataTypeOf _ = mkNoRepType "YCHR.Types.Name"

instance Data Term where
  gunfold _ _ = error "Data Term: gunfold (unused)"
  toConstr _ = error "Data Term: toConstr (unused)"
  dataTypeOf _ = mkNoRepType "YCHR.Types.Term"

instance Data R.Expr where
  gunfold _ _ = error "Data R.Expr: gunfold (unused)"
  toConstr _ = error "Data R.Expr: toConstr (unused)"
  dataTypeOf _ = mkNoRepType "YCHR.Resolved.Expr"

deriving instance Data CollectError

deriving instance Data ParseValidationError

deriving instance Data ResolveError

deriving instance Data RenameError

deriving instance Data RenameWarning

deriving instance Data ExhaustivenessWarning

deriving instance Data DesugarError

deriving instance Data CompileError

deriving instance Data TypeCheckError

-- ---------------------------------------------------------------------------
-- Code collection
-- ---------------------------------------------------------------------------

-- | Enumerate every constructor of an error type and pair its name with the
-- code number its @*ErrorCode@ function assigns. 'fromConstr' builds a value
-- with bottom payloads, which is safe because the @*ErrorCode@ functions
-- match only on the constructor.
enumCodes :: forall e. (Data e) => (e -> ErrorCode) -> [(String, Int)]
enumCodes f =
  [ (show c, n)
  | c <- dataTypeConstrs (dataTypeOf (undefined :: e)),
    let ErrorCode n = f (fromConstr c)
  ]

constructorCodes :: [(String, Int)]
constructorCodes =
  concat
    [ enumCodes collectErrorCode,
      enumCodes parseValidationErrorCode,
      enumCodes resolveErrorCode,
      enumCodes renameErrorCode,
      enumCodes renameWarningCode,
      enumCodes exhaustivenessWarningCode,
      enumCodes desugarErrorCode,
      enumCodes compileErrorCode,
      enumCodes typeCheckErrorCode
    ]

-- | Codes not attached to an enumerable constructor (see "YCHR.Display").
standaloneCodes :: [(String, Int)]
standaloneCodes =
  [ ("parseErrorCode", n parseErrorCode),
    ("operatorConflictCode", n operatorConflictCode),
    ("lambdasInLiveQueryCode", n lambdasInLiveQueryCode),
    ("goalNotAConstraintCode", n goalNotAConstraintCode),
    ("runtimeErrorCode", n runtimeErrorCode)
  ]
  where
    n (ErrorCode k) = k

allCodes :: [(String, Int)]
allCodes = constructorCodes ++ standaloneCodes

-- | Codes deliberately shared by more than one error. Every entry needs a
-- comment justifying the share; the @allowlist is not stale@ test keeps this
-- honest by rejecting entries that no longer correspond to a real duplicate.
intentionalShared :: Set Int
intentionalShared =
  Set.fromList
    [ 60001 -- runtimeErrorCode shares with TypeCheckError's InconsistentTypes
    ]

-- | Map each code number to the labels (constructor / constant names) that
-- assign it.
codesByNumber :: Map.Map Int [String]
codesByNumber =
  Map.fromListWith (++) [(n, [label]) | (label, n) <- allCodes]

-- ---------------------------------------------------------------------------
-- Tests
-- ---------------------------------------------------------------------------

tests :: TestTree
tests =
  testGroup
    "ErrorCode"
    [ testCase "every error code is unique" $
        let offenders =
              [ (n, sort labels)
              | (n, labels) <- Map.toList codesByNumber,
                length labels > 1,
                not (n `Set.member` intentionalShared)
              ]
         in case offenders of
              [] -> pure ()
              _ ->
                assertFailure $
                  "Duplicate error codes:\n"
                    ++ unlines
                      [ "  YCHR-" ++ show n ++ " assigned by " ++ show labels
                      | (n, labels) <- offenders
                      ],
      testCase "intentional-share allowlist is not stale" $
        let stale =
              [ n
              | n <- Set.toList intentionalShared,
                length (Map.findWithDefault [] n codesByNumber) < 2
              ]
         in stale @?= []
    ]
