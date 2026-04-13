{-# LANGUAGE OverloadedStrings #-}

-- | Human-readable error display.
module YCHR.Display
  ( Display (..),
    Severity (..),
    displaySrcLoc,
    displayMsgWithSrcLoc,
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
import YCHR.Parsed qualified as P
import YCHR.Pretty (prettyTermSrc)
import YCHR.Rename (RenameError (..), RenameWarning (..))
import YCHR.Types qualified as Types

class Display a where
  displayMsg :: a -> String

data Severity = SevError | SevWarning

-- | Display a source location as @file:line:col@.
displaySrcLoc :: P.SourceLoc -> String
displaySrcLoc loc = loc.file ++ ":" ++ show loc.line ++ ":" ++ show loc.col

displaySeverity :: Severity -> String
displaySeverity SevError = "error"
displaySeverity SevWarning = "warning"

-- | Format a diagnostic message with source location, severity, and optional AST context.
--
-- @
-- file:line:col: severity: message
-- ast_node
-- @
displayMsgWithSrcLoc :: Severity -> String -> P.SourceLoc -> Maybe String -> String
displayMsgWithSrcLoc sev msg loc maybeNode =
  displaySrcLoc loc ++ ": " ++ displaySeverity sev ++ ":\n" ++ msg ++ maybe "" ("\n" ++) maybeNode

-- | Join multiple error messages separated by two blank lines.
displayErrors :: [String] -> String
displayErrors = intercalate "\n\n"

-- | Convert a megaparsec 'SourcePos' to a 'P.SourceLoc'.
sourceLocFromPos :: SourcePos -> P.SourceLoc
sourceLocFromPos sp =
  P.SourceLoc
    { P.file = sourceName sp,
      P.line = unPos (sourceLine sp),
      P.col = unPos (sourceColumn sp)
    }

instance Display CollectError where
  displayMsg (UnknownLibrary name) =
    "Unknown library: " ++ T.unpack name
  displayMsg (CircularLibraryImport names) =
    "Circular library import: " ++ intercalate " -> " (map T.unpack names)

instance Display RenameError where
  displayMsg (AmbiguousName loc name arity candidates) =
    displayMsgWithSrcLoc
      SevError
      ( "Ambiguous name "
          ++ T.unpack name
          ++ "/"
          ++ show arity
          ++ ", could be: "
          ++ intercalate ", " (map T.unpack candidates)
      )
      loc
      Nothing
  displayMsg (UnknownName loc name arity) =
    displayMsgWithSrcLoc
      SevError
      ("Unknown constraint " ++ T.unpack name ++ "/" ++ show arity)
      loc
      Nothing
  displayMsg (UnknownExport modName name arity) =
    "Module "
      ++ T.unpack modName
      ++ " exports "
      ++ T.unpack name
      ++ "/"
      ++ show arity
      ++ " but does not declare it"

instance Display RenameWarning where
  displayMsg (UndeclaredDataConstructor loc name) =
    displayMsgWithSrcLoc
      SevWarning
      ("Undeclared data constructor " ++ T.unpack name)
      loc
      Nothing
  displayMsg (DataConstructorArityMismatch loc name arity) =
    displayMsgWithSrcLoc
      SevWarning
      ("Data constructor " ++ T.unpack name ++ " used with arity " ++ show arity ++ " but declared with different arity")
      loc
      Nothing

instance Display DesugarError where
  displayMsg (UnexpectedBodyTerm loc term) =
    displayMsgWithSrcLoc
      SevError
      "Unexpected term in rule body"
      loc
      (Just (prettyTermSrc term))
  displayMsg (UnexpectedGuardTerm loc term) =
    displayMsgWithSrcLoc
      SevError
      "Unexpected term in guard"
      loc
      (Just (prettyTermSrc term))
  displayMsg (InvalidLambdaParam loc term) =
    displayMsgWithSrcLoc
      SevError
      "Invalid lambda parameter (expected variable or wildcard)"
      loc
      (Just (prettyTermSrc term))

instance Display CompileError where
  displayMsg (UnknownConstraintType loc origin name) =
    displayMsgWithSrcLoc
      SevError
      ("Unknown constraint type '" ++ displayName name ++ "'")
      loc
      (Just (show origin))
  displayMsg (UnboundVariable loc origin var) =
    displayMsgWithSrcLoc
      SevError
      ("Unbound variable '" ++ T.unpack var ++ "'")
      loc
      (Just (show origin))

displayName :: Types.Name -> String
displayName (Types.Unqualified n) = T.unpack n
displayName (Types.Qualified m n) = T.unpack m ++ ":" ++ T.unpack n

-- | Display a single parse error using our 'displaySrcLoc' format.
displayParseError :: PosState Text -> ParseError Text Void -> String
displayParseError posState err =
  let (_, posState') = reachOffset (errorOffset err) posState
      loc = sourceLocFromPos (pstateSourcePos posState')
   in displaySrcLoc loc ++ ": " ++ parseErrorTextPretty err

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
    "Operator naming conflict: "
      ++ T.unpack name
      ++ case sources of
        [] -> ""
        _ -> " (declared in " ++ intercalate ", " sources ++ ")"
