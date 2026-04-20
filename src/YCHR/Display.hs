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
    parseValidationErrorCode,
    resolveErrorCode,
    renameErrorCode,
    renameWarningCode,
    desugarErrorCode,
    compileErrorCode,
    parseErrorCode,
    operatorConflictCode,
  )
where

import Data.Foldable (toList)
import Data.List (dropWhileEnd, intercalate)
import Data.Text (Text)
import Data.Text qualified as T
import Data.Void (Void)
import System.Console.ANSI (Color (..), ColorIntensity (..), ConsoleIntensity (..), ConsoleLayer (..), SGR (..), setSGRCode)
import Text.Megaparsec
import YCHR.Collect (CollectError (..))
import YCHR.Compile (CompileError (..))
import YCHR.Desugar (DesugarError (..))
import YCHR.Diagnostic (Diagnostic (..))
import YCHR.Parsed (AnnP (..))
import YCHR.Parsed qualified as P
import YCHR.Parser (ParseValidationError (..))
import YCHR.Pretty (prettyPExprSrc, prettyTermSrc)
import YCHR.Rename (RenameError (..), RenameWarning (..))
import YCHR.Resolve (ResolveError (..))
import YCHR.Run (Error (..), Warning (..))
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

severityLabel :: Severity -> String
severityLabel SevError = "error"
severityLabel SevWarning = "warning"

severityColor :: Severity -> Color
severityColor SevError = Red
severityColor SevWarning = Yellow

-- | Format a diagnostic message with source location, severity, error code,
-- optional location label, and optional AST context.
--
-- @
-- file:line:col: severity: YCHR-NNNNN
-- location_label
-- message
-- ast_node
-- @
displayMsgWithSrcLoc :: ErrorCode -> Severity -> String -> P.SourceLoc -> Maybe String -> Maybe String -> String
displayMsgWithSrcLoc code sev msg loc maybeLabel maybeNode =
  let col = severityColor sev
      lbl = severityLabel sev
      c = setSGRCode [SetColor Foreground Vivid col]
      r = setSGRCode [Reset]
   in c
        ++ "=== "
        ++ lbl
        ++ " ==="
        ++ r
        ++ "\n"
        ++ setSGRCode [SetConsoleIntensity BoldIntensity]
        ++ displaySrcLoc loc
        ++ ": "
        ++ displayErrorCode code
        ++ "\n"
        ++ maybe "" (\l -> setSGRCode [SetConsoleIntensity BoldIntensity] ++ "<<" ++ l ++ ">>" ++ r ++ "\n") maybeLabel
        ++ msg
        ++ maybe "" (\n -> "\n" ++ setSGRCode [SetItalicized True] ++ n ++ setSGRCode [SetItalicized False]) maybeNode
        ++ "\n"
        ++ r

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

-- | 15xxx — parse validation phase
parseValidationErrorCode :: ParseValidationError -> ErrorCode
parseValidationErrorCode (DiscontiguousEquations _) = ErrorCode 15001

-- | 16xxx — resolve phase (post-rename, pre-desugar)
resolveErrorCode :: ResolveError -> ErrorCode
resolveErrorCode (ConstraintHasEquations _) = ErrorCode 16001
resolveErrorCode (FunctionInRuleHead _) = ErrorCode 16002

-- | 2xxxx — rename phase (errors).
-- Code 20004 was previously used for OperatorInImportList; now reserved
-- because operators are permitted in import lists (see UnknownOperatorImport).
renameErrorCode :: RenameError -> ErrorCode
renameErrorCode (AmbiguousName _ _ _) = ErrorCode 20001
renameErrorCode (UnknownName _ _) = ErrorCode 20002
renameErrorCode (UnknownExport _ _ _) = ErrorCode 20003
renameErrorCode (UnknownImport _ _ _) = ErrorCode 20005
renameErrorCode (UnknownOperatorImport _ _) = ErrorCode 20006
renameErrorCode (UseModuleOutOfOrder _) = ErrorCode 20007

-- | 2x1xx — rename phase (warnings)
renameWarningCode :: RenameWarning -> ErrorCode
renameWarningCode (UndeclaredDataConstructor _) = ErrorCode 20101
renameWarningCode (DataConstructorArityMismatch _ _) = ErrorCode 20102

-- | 3xxxx — desugar phase
desugarErrorCode :: DesugarError -> ErrorCode
desugarErrorCode (UnexpectedBodyTerm _) = ErrorCode 30001
desugarErrorCode (InvalidLambdaParam _) = ErrorCode 30003

-- | 4xxxx — compile phase
compileErrorCode :: CompileError -> ErrorCode
compileErrorCode (UnknownConstraintType _) = ErrorCode 40001
compileErrorCode (UnboundVariable _) = ErrorCode 40002

-- | 5xxxx — top-level errors
parseErrorCode :: ErrorCode
parseErrorCode = ErrorCode 50001

operatorConflictCode :: ErrorCode
operatorConflictCode = ErrorCode 50002

-- ---------------------------------------------------------------------------
-- Display instances
-- ---------------------------------------------------------------------------

instance Display (P.AnnP ParseValidationError) where
  displayMsg (AnnP err loc origin) =
    displayMsgWithSrcLoc
      (parseValidationErrorCode err)
      SevError
      (parseValidationErrorMsg err)
      loc
      Nothing
      (Just (prettyPExprSrc origin))

parseValidationErrorMsg :: ParseValidationError -> String
parseValidationErrorMsg (DiscontiguousEquations name) =
  "Equations for function "
    ++ T.unpack name
    ++ " must be contiguous (or declare it with :- open_function)"

instance Display (Diagnostic ResolveError) where
  displayMsg (Diagnostic lbl (AnnP err loc origin)) =
    displayMsgWithSrcLoc
      (resolveErrorCode err)
      SevError
      (resolveErrorMsg err)
      loc
      (fmap T.unpack lbl)
      (Just (prettyPExprSrc origin))

resolveErrorMsg :: ResolveError -> String
resolveErrorMsg (ConstraintHasEquations name) =
  displayName name
    ++ " is declared as a constraint but has function equations (->)"
resolveErrorMsg (FunctionInRuleHead name) =
  displayName name
    ++ " is declared as a function but appears in a rule head"

instance Display (Diagnostic CollectError) where
  displayMsg (Diagnostic lbl (AnnP err loc origin)) =
    displayMsgWithSrcLoc
      (collectErrorCode err)
      SevError
      (collectErrorMsg err)
      loc
      (fmap T.unpack lbl)
      (Just (prettyPExprSrc origin))

collectErrorMsg :: CollectError -> String
collectErrorMsg (UnknownLibrary name) = "Unknown library: " ++ T.unpack name
collectErrorMsg (CircularLibraryImport names) = "Circular library import: " ++ intercalate " -> " (map T.unpack names)

instance Display (Diagnostic RenameError) where
  displayMsg (Diagnostic lbl (AnnP err loc origin)) =
    displayMsgWithSrcLoc
      (renameErrorCode err)
      SevError
      (renameErrorMsg err)
      loc
      (fmap T.unpack lbl)
      (Just (prettyPExprSrc origin))

renameErrorMsg :: RenameError -> String
renameErrorMsg (AmbiguousName name arity candidates) =
  "Ambiguous name "
    ++ T.unpack name
    ++ "/"
    ++ show arity
    ++ ", could be: "
    ++ intercalate ", " (map T.unpack candidates)
renameErrorMsg (UnknownName name arity) =
  "Unknown constraint " ++ T.unpack name ++ "/" ++ show arity
renameErrorMsg (UnknownExport modName name arity) =
  "Module "
    ++ T.unpack modName
    ++ " exports "
    ++ T.unpack name
    ++ "/"
    ++ show arity
    ++ " but does not declare it"
renameErrorMsg (UnknownImport modName name arity) =
  "Module "
    ++ T.unpack modName
    ++ " does not export "
    ++ T.unpack name
    ++ "/"
    ++ show arity
renameErrorMsg (UnknownOperatorImport modName opName) =
  "Module "
    ++ T.unpack modName
    ++ " does not export operator "
    ++ T.unpack opName
renameErrorMsg (UseModuleOutOfOrder modName) =
  "use_module("
    ++ T.unpack modName
    ++ ") must appear immediately after the module directive, before any other directive or rule"

instance Display (Diagnostic RenameWarning) where
  displayMsg (Diagnostic lbl (AnnP err loc origin)) =
    displayMsgWithSrcLoc
      (renameWarningCode err)
      SevWarning
      (renameWarningMsg err)
      loc
      (fmap T.unpack lbl)
      (Just (prettyPExprSrc origin))

renameWarningMsg :: RenameWarning -> String
renameWarningMsg (UndeclaredDataConstructor name) =
  "Undeclared data constructor " ++ T.unpack name
renameWarningMsg (DataConstructorArityMismatch name arity) =
  "Data constructor " ++ T.unpack name ++ " used with arity " ++ show arity ++ " but declared with different arity"

instance Display (Diagnostic DesugarError) where
  displayMsg (Diagnostic lbl (AnnP err loc origin)) =
    displayMsgWithSrcLoc
      (desugarErrorCode err)
      SevError
      (desugarErrorMsg err)
      loc
      (fmap T.unpack lbl)
      (Just (prettyPExprSrc origin))

desugarErrorMsg :: DesugarError -> String
desugarErrorMsg (UnexpectedBodyTerm term) = "Unexpected term in rule body: " ++ prettyTermSrc term
desugarErrorMsg (InvalidLambdaParam term) = "Invalid lambda parameter (expected variable or wildcard): " ++ prettyTermSrc term

instance Display (Diagnostic CompileError) where
  displayMsg (Diagnostic lbl (AnnP err loc origin)) =
    displayMsgWithSrcLoc
      (compileErrorCode err)
      SevError
      (compileErrorMsg err)
      loc
      (fmap T.unpack lbl)
      (Just (prettyPExprSrc origin))

compileErrorMsg :: CompileError -> String
compileErrorMsg (UnknownConstraintType name) = "Unknown constraint type '" ++ displayName name ++ "'"
compileErrorMsg (UnboundVariable var) = "Unbound variable '" ++ T.unpack var ++ "'"

displayName :: Types.Name -> String
displayName (Types.Unqualified n) = T.unpack n
displayName (Types.Qualified m n) = T.unpack m ++ ":" ++ T.unpack n

-- | Display a single parse error using our 'displayMsgWithSrcLoc' format.
displayParseError :: PosState Text -> ParseError Text Void -> String
displayParseError posState err =
  let (_, posState') = reachOffset (errorOffset err) posState
      loc = sourceLocFromPos (pstateSourcePos posState')
      msg = dropWhileEnd (== '\n') (parseErrorTextPretty err)
   in displayMsgWithSrcLoc parseErrorCode SevError msg loc Nothing Nothing

instance Display Warning where
  displayMsg (RenameWarnings ws) = displayErrors (map displayMsg ws)

instance Display Error where
  displayMsg (ParseError _ bundle) =
    let posState = bundlePosState bundle
        errs = bundleErrors bundle
     in displayErrors (map (displayParseError posState) (toList errs))
  displayMsg (ParseValidationErrors errs) = displayErrors (map displayMsg errs)
  displayMsg (CollectErrors errs) = displayErrors (map displayMsg errs)
  displayMsg (RenameErrors errs) = displayErrors (map displayMsg errs)
  displayMsg (ResolveErrors errs) = displayErrors (map displayMsg errs)
  displayMsg (DesugarErrors errs) = displayErrors (map displayMsg errs)
  displayMsg (CompileErrors errs) = displayErrors (map displayMsg errs)
  displayMsg (OperatorConflict (AnnP name loc origin)) =
    displayMsgWithSrcLoc
      operatorConflictCode
      SevError
      ("Operator naming conflict: " ++ T.unpack name)
      loc
      Nothing
      (Just (prettyPExprSrc origin))
