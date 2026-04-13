{-# LANGUAGE OverloadedStrings #-}

-- | Human-readable error display.
module YCHR.Display
  ( Display (..),
    Severity (..),
    ErrorCode (..),
    displaySrcLoc,
    displayMsgWithSrcLoc,
    displayErrorCode,
    collectErrorCode,
    renameErrorCode,
    renameWarningCode,
    desugarErrorCode,
    compileErrorCode,
    parseErrorCode,
    operatorConflictCode,
  )
where

import Data.Foldable (toList)
import Data.List (intercalate)
import Data.Text (Text)
import Data.Text qualified as T
import Data.Void (Void)
import Text.Megaparsec
import YCHR.Collect (CollectError (..))
import YCHR.Compile (CompileError (..))
import YCHR.Desugar (DesugarError (..))
import YCHR.EndToEnd (Error (..), Warning (..))
import YCHR.Parsed (AnnP (..))
import YCHR.Parsed qualified as P
import YCHR.Pretty (prettyPExprSrc, prettyTermSrc)
import YCHR.Rename (RenameError (..), RenameWarning (..))
import YCHR.Types qualified as Types

class Display a where
  displayMsg :: a -> String

data Severity = SevError | SevWarning

newtype ErrorCode = ErrorCode Int
  deriving (Show, Eq, Ord)

-- | Format an error code as @YCHR-NNNNN@.
displayErrorCode :: ErrorCode -> String
displayErrorCode (ErrorCode n) = "YCHR-" ++ show n

-- | Display a source location as @file:line:col@.
displaySrcLoc :: P.SourceLoc -> String
displaySrcLoc loc = loc.file ++ ":" ++ show loc.line ++ ":" ++ show loc.col

displaySeverity :: Severity -> String
displaySeverity SevError = "error"
displaySeverity SevWarning = "warning"

-- | Format a diagnostic message with source location, severity, error code,
-- and optional AST context.
--
-- @
-- file:line:col: severity: YCHR-NNNNN
-- message
-- ast_node
-- @
displayMsgWithSrcLoc :: ErrorCode -> Severity -> String -> P.SourceLoc -> Maybe String -> String
displayMsgWithSrcLoc code sev msg loc maybeNode =
  displaySrcLoc loc ++ ": " ++ displaySeverity sev ++ ": " ++ displayErrorCode code ++ "\n" ++ msg ++ maybe "" ("\n" ++) maybeNode ++ "\n"

-- | Join multiple error messages. Each message is expected to end with
-- a newline, so a single @\"\\n\"@ separator produces a blank line between
-- messages.
displayErrors :: [String] -> String
displayErrors = intercalate "\n"

-- | Convert a megaparsec 'SourcePos' to a 'P.SourceLoc'.
sourceLocFromPos :: SourcePos -> P.SourceLoc
sourceLocFromPos sp =
  P.SourceLoc
    { P.file = sourceName sp,
      P.line = unPos (sourceLine sp),
      P.col = unPos (sourceColumn sp)
    }

-- ---------------------------------------------------------------------------
-- Error codes by phase
-- ---------------------------------------------------------------------------

-- | 1xxxx — collect phase
collectErrorCode :: CollectError -> ErrorCode
collectErrorCode (UnknownLibrary _) = ErrorCode 10001
collectErrorCode (CircularLibraryImport _) = ErrorCode 10002

-- | 2xxxx — rename phase (errors)
renameErrorCode :: AnnP RenameError -> ErrorCode
renameErrorCode (AnnP (AmbiguousName _ _ _) _ _) = ErrorCode 20001
renameErrorCode (AnnP (UnknownName _ _) _ _) = ErrorCode 20002
renameErrorCode (AnnP (UnknownExport _ _ _) _ _) = ErrorCode 20003

-- | 2x1xx — rename phase (warnings)
renameWarningCode :: RenameWarning -> ErrorCode
renameWarningCode (UndeclaredDataConstructor _ _) = ErrorCode 20101
renameWarningCode (DataConstructorArityMismatch _ _ _) = ErrorCode 20102

-- | 3xxxx — desugar phase
desugarErrorCode :: AnnP DesugarError -> ErrorCode
desugarErrorCode (AnnP (UnexpectedBodyTerm _) _ _) = ErrorCode 30001
desugarErrorCode (AnnP (InvalidLambdaParam _) _ _) = ErrorCode 30003

-- | 4xxxx — compile phase
compileErrorCode :: AnnP CompileError -> ErrorCode
compileErrorCode (AnnP (UnknownConstraintType _) _ _) = ErrorCode 40001
compileErrorCode (AnnP (UnboundVariable _) _ _) = ErrorCode 40002

-- | 5xxxx — top-level errors
parseErrorCode :: ErrorCode
parseErrorCode = ErrorCode 50001

operatorConflictCode :: ErrorCode
operatorConflictCode = ErrorCode 50002

-- ---------------------------------------------------------------------------
-- Display instances
-- ---------------------------------------------------------------------------

instance Display CollectError where
  displayMsg e@(UnknownLibrary name) =
    displayErrorCode (collectErrorCode e)
      ++ "\nUnknown library: "
      ++ T.unpack name
      ++ "\n"
  displayMsg e@(CircularLibraryImport names) =
    displayErrorCode (collectErrorCode e)
      ++ "\nCircular library import: "
      ++ intercalate " -> " (map T.unpack names)
      ++ "\n"

instance Display (AnnP RenameError) where
  displayMsg e@(AnnP (AmbiguousName name arity candidates) loc origin) =
    displayMsgWithSrcLoc
      (renameErrorCode e)
      SevError
      ( "Ambiguous name "
          ++ T.unpack name
          ++ "/"
          ++ show arity
          ++ ", could be: "
          ++ intercalate ", " (map T.unpack candidates)
      )
      loc
      (Just (prettyPExprSrc origin))
  displayMsg e@(AnnP (UnknownName name arity) loc origin) =
    displayMsgWithSrcLoc
      (renameErrorCode e)
      SevError
      ("Unknown constraint " ++ T.unpack name ++ "/" ++ show arity)
      loc
      (Just (prettyPExprSrc origin))
  displayMsg e@(AnnP (UnknownExport modName name arity) loc origin) =
    displayMsgWithSrcLoc
      (renameErrorCode e)
      SevError
      ( "Module "
          ++ T.unpack modName
          ++ " exports "
          ++ T.unpack name
          ++ "/"
          ++ show arity
          ++ " but does not declare it"
      )
      loc
      (Just (prettyPExprSrc origin))

instance Display RenameWarning where
  displayMsg e@(UndeclaredDataConstructor loc name) =
    displayMsgWithSrcLoc
      (renameWarningCode e)
      SevWarning
      ("Undeclared data constructor " ++ T.unpack name)
      loc
      Nothing
  displayMsg e@(DataConstructorArityMismatch loc name arity) =
    displayMsgWithSrcLoc
      (renameWarningCode e)
      SevWarning
      ("Data constructor " ++ T.unpack name ++ " used with arity " ++ show arity ++ " but declared with different arity")
      loc
      Nothing

instance Display (AnnP DesugarError) where
  displayMsg e@(AnnP (UnexpectedBodyTerm term) loc origin) =
    displayMsgWithSrcLoc
      (desugarErrorCode e)
      SevError
      ("Unexpected term in rule body: " ++ prettyTermSrc term)
      loc
      (Just (prettyPExprSrc origin))
  displayMsg e@(AnnP (InvalidLambdaParam term) loc origin) =
    displayMsgWithSrcLoc
      (desugarErrorCode e)
      SevError
      ("Invalid lambda parameter (expected variable or wildcard): " ++ prettyTermSrc term)
      loc
      (Just (prettyPExprSrc origin))

instance Display (AnnP CompileError) where
  displayMsg e@(AnnP (UnknownConstraintType name) loc origin) =
    displayMsgWithSrcLoc
      (compileErrorCode e)
      SevError
      ("Unknown constraint type '" ++ displayName name ++ "'")
      loc
      (Just (prettyPExprSrc origin))
  displayMsg e@(AnnP (UnboundVariable var) loc origin) =
    displayMsgWithSrcLoc
      (compileErrorCode e)
      SevError
      ("Unbound variable '" ++ T.unpack var ++ "'")
      loc
      (Just (prettyPExprSrc origin))

displayName :: Types.Name -> String
displayName (Types.Unqualified n) = T.unpack n
displayName (Types.Qualified m n) = T.unpack m ++ ":" ++ T.unpack n

-- | Display a single parse error using our 'displaySrcLoc' format.
displayParseError :: PosState Text -> ParseError Text Void -> String
displayParseError posState err =
  let (_, posState') = reachOffset (errorOffset err) posState
      loc = sourceLocFromPos (pstateSourcePos posState')
   in displaySrcLoc loc ++ ": " ++ displayErrorCode parseErrorCode ++ ": " ++ parseErrorTextPretty err

instance Display Warning where
  displayMsg (RenameWarnings ws) = displayErrors (map displayMsg ws)

instance Display Error where
  displayMsg (ParseError _ bundle) =
    let posState = bundlePosState bundle
        errs = bundleErrors bundle
     in displayErrors (map (displayParseError posState) (toList errs))
  displayMsg (CollectErrors errs) = displayErrors (map displayMsg errs)
  displayMsg (RenameErrors errs) = displayErrors (map displayMsg errs)
  displayMsg (DesugarErrors errs) = displayErrors (map displayMsg errs)
  displayMsg (CompileErrors errs) = displayErrors (map displayMsg errs)
  displayMsg (OperatorConflict sources name) =
    displayErrorCode operatorConflictCode
      ++ "\nOperator naming conflict: "
      ++ T.unpack name
      ++ case sources of
        [] -> ""
        _ -> " (declared in " ++ intercalate ", " sources ++ ")"
      ++ "\n"
