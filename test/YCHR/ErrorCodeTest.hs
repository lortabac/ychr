{-# OPTIONS_GHC -Wno-orphans #-}

-- | Guards the uniqueness of error codes (@YCHR-NNNNN@).
--
-- Error codes are assigned by hand in "YCHR.Internal.Display": one @*ErrorCode@
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
import YCHR.Internal.Collect (BareImportHint (..), CollectError (..))
import YCHR.Internal.Compile (CompileError (..))
import YCHR.Internal.ConstraintUse (ConstraintUseError (..), OccurrenceRole (..))
import YCHR.Internal.DeclMacro (DeclMacroError (..))
import YCHR.Internal.Desugar (DesugarError (..))
import YCHR.Internal.Display
  ( ErrorCode (..),
    collectErrorCode,
    compileErrorCode,
    constraintUseErrorCode,
    declMacroErrorCode,
    desugarErrorCode,
    exhaustivenessWarningCode,
    fileReadErrorCode,
    goalNotAConstraintCode,
    lambdasInLiveQueryCode,
    lambdasInSchemeDriverCode,
    operatorConflictCode,
    parseErrorCode,
    parseValidationErrorCode,
    renameErrorCode,
    renameWarningCode,
    resolveErrorCode,
    runtimeErrorCode,
    typeCheckErrorCode,
  )
import YCHR.Internal.Exhaustiveness (ExhaustivenessWarning (..))
import YCHR.Internal.Parsed (MacroKind (..))
import YCHR.Internal.Parser (ParseValidationError (..))
import YCHR.Internal.Rename
  ( BadConjunct (..),
    HeadPart (..),
    NonGoalKind (..),
    RenameError (..),
    RenameWarning (..),
  )
import YCHR.Internal.Rename.Macro (PrimitiveOperand (..))
import YCHR.Internal.Resolve
  ( BoundTargetKind (..),
    ExtensionDirective (..),
    RefiningViolation (..),
    ResolveError (..),
  )
import YCHR.Internal.Resolved qualified as R
import YCHR.Internal.TypeCheck (ConstructorDecl (..), TypeCheckError (..))
import YCHR.Internal.Types (ConstraintUse (..), Name, QualifiedName, Term)

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
  dataTypeOf _ = mkNoRepType "YCHR.Internal.Resolved.Expr"

instance Data QualifiedName where
  gunfold _ _ = error "Data QualifiedName: gunfold (unused)"
  toConstr _ = error "Data QualifiedName: toConstr (unused)"
  dataTypeOf _ = mkNoRepType "YCHR.Types.QualifiedName"

deriving instance Data CollectError

deriving instance Data BareImportHint

deriving instance Data ParseValidationError

deriving instance Data ResolveError

deriving instance Data RefiningViolation

deriving instance Data BoundTargetKind

deriving instance Data ExtensionDirective

deriving instance Data HeadPart

deriving instance Data BadConjunct

deriving instance Data NonGoalKind

deriving instance Data PrimitiveOperand

deriving instance Data MacroKind

deriving instance Data RenameError

deriving instance Data DeclMacroError

deriving instance Data RenameWarning

deriving instance Data ExhaustivenessWarning

deriving instance Data ConstraintUse

deriving instance Data OccurrenceRole

deriving instance Data ConstraintUseError

deriving instance Data DesugarError

deriving instance Data CompileError

deriving instance Data ConstructorDecl

deriving instance Data TypeCheckError

-- ---------------------------------------------------------------------------
-- Code collection
-- ---------------------------------------------------------------------------

-- | An error code number and the name of what assigns it (a constructor
-- or a constant).
data CodeEntry = CodeEntry
  { label :: String,
    code :: Int
  }

-- | Enumerate every constructor of an error type and pair its name with the
-- code number its @*ErrorCode@ function assigns. 'fromConstr' builds a value
-- with bottom payloads, which is safe because the @*ErrorCode@ functions
-- match only on the constructor.
enumCodes :: forall e. (Data e) => (e -> ErrorCode) -> [CodeEntry]
enumCodes f =
  [ CodeEntry {label = show c, code = n}
  | c <- dataTypeConstrs (dataTypeOf (undefined :: e)),
    let ErrorCode n = f (fromConstr c)
  ]

-- | 'enumCodes', skipping the named constructors.
enumCodesExcept :: forall e. (Data e) => [String] -> (e -> ErrorCode) -> [CodeEntry]
enumCodesExcept skip f = [e | e <- enumCodes f, e.label `notElem` skip]

-- | The codes of every enumerable error and warning constructor.
constructorCodes :: [CodeEntry]
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
      enumCodes constraintUseErrorCode,
      enumCodes typeCheckErrorCode,
      -- The two wrappers delegate to the renamer's and the parse
      -- validator's codes, already enumerated above.
      enumCodesExcept ["DeclMacroRenameError", "DeclMacroParseError"] declMacroErrorCode
    ]

-- | Codes not attached to an enumerable constructor (see "YCHR.Internal.Display").
standaloneCodes :: [CodeEntry]
standaloneCodes =
  [ entry "parseErrorCode" parseErrorCode,
    entry "operatorConflictCode" operatorConflictCode,
    entry "lambdasInLiveQueryCode" lambdasInLiveQueryCode,
    entry "lambdasInSchemeDriverCode" lambdasInSchemeDriverCode,
    entry "fileReadErrorCode" fileReadErrorCode,
    entry "goalNotAConstraintCode" goalNotAConstraintCode,
    entry "runtimeErrorCode" runtimeErrorCode
  ]
  where
    entry l (ErrorCode k) = CodeEntry {label = l, code = k}

-- | Every error code, by name.
allCodes :: [CodeEntry]
allCodes = constructorCodes ++ standaloneCodes

-- | Codes deliberately shared by more than one error. Every entry needs a
-- comment justifying the share; the @allowlist is not stale@ test keeps this
-- honest by rejecting entries that do not correspond to a real duplicate.
intentionalShared :: Set Int
intentionalShared =
  Set.fromList
    [ 60001 -- runtimeErrorCode shares with TypeCheckError's InconsistentTypes
    ]

-- | Map each code number to the labels (constructor / constant names) that
-- assign it.
codesByNumber :: Map.Map Int [String]
codesByNumber =
  Map.fromListWith (++) [(e.code, [e.label]) | e <- allCodes]

-- ---------------------------------------------------------------------------
-- Tests
-- ---------------------------------------------------------------------------

-- | Guards that every @YCHR-NNNNN@ error code is unique and the allowlist is not stale.
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
