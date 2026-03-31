{-# LANGUAGE OverloadedStrings #-}

-- | Human-readable error display.
module YCHR.Display
  ( Display (..),
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
import YCHR.EndToEnd (Error (..))
import YCHR.Parsed qualified as P
import YCHR.Pretty (prettyTermSrc)
import YCHR.Rename (RenameError (..))
import YCHR.Types qualified as Types

class Display a where
  displayMsg :: a -> String

-- | Display a source location as @file:line:col@.
displaySrcLoc :: P.SourceLoc -> String
displaySrcLoc loc = loc.file ++ ":" ++ show loc.line ++ ":" ++ show loc.col

-- | Format an error message with source location and optional AST context.
--
-- @
-- file:line:col
-- message
-- ast_node
-- @
displayMsgWithSrcLoc :: String -> P.SourceLoc -> Maybe String -> String
displayMsgWithSrcLoc msg loc maybeNode =
  displaySrcLoc loc ++ "\n" ++ msg ++ maybe "" ("\n" ++) maybeNode

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

instance Display DesugarError where
  displayMsg (UnexpectedBodyTerm loc term) =
    displayMsgWithSrcLoc
      "Unexpected term in rule body"
      loc
      (Just (prettyTermSrc term))
  displayMsg (UnexpectedGuardTerm loc term) =
    displayMsgWithSrcLoc
      "Unexpected term in guard"
      loc
      (Just (prettyTermSrc term))

instance Display CompileError where
  displayMsg (UnknownConstraintType loc origin name) =
    displayMsgWithSrcLoc
      ("Unknown constraint type '" ++ displayName name ++ "'")
      loc
      (Just (show origin))
  displayMsg (UnboundVariable loc origin var) =
    displayMsgWithSrcLoc
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
