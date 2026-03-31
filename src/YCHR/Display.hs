{-# LANGUAGE OverloadedStrings #-}

-- | Human-readable error display.
module YCHR.Display
  ( Display (..),
    displaySrcLoc,
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
    "unknown library: " ++ T.unpack name
  displayMsg (CircularLibraryImport names) =
    "circular library import: " ++ intercalate " -> " (map T.unpack names)

instance Display RenameError where
  displayMsg (AmbiguousName loc name arity candidates) =
    displaySrcLoc loc
      ++ ": ambiguous name "
      ++ T.unpack name
      ++ "/"
      ++ show arity
      ++ ", could be: "
      ++ intercalate ", " (map T.unpack candidates)
  displayMsg (UnknownName loc name arity) =
    displaySrcLoc loc
      ++ ": unknown constraint "
      ++ T.unpack name
      ++ "/"
      ++ show arity

instance Display DesugarError where
  displayMsg (UnexpectedBodyTerm loc term) =
    displaySrcLoc loc
      ++ ": unexpected term in rule body: "
      ++ prettyTermSrc term

instance Display CompileError where
  displayMsg (UnknownConstraintType loc origin name) =
    displaySrcLoc loc
      ++ ": unknown constraint type '"
      ++ displayName name
      ++ "' in: "
      ++ show origin
  displayMsg (UnboundVariable loc origin var) =
    displaySrcLoc loc
      ++ ": unbound variable '"
      ++ T.unpack var
      ++ "' in: "
      ++ show origin

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
     in unlines (map (displayParseError posState) (toList errs))
  displayMsg (CollectErrors errs) = unlines (map displayMsg errs)
  displayMsg (RenameErrors errs) = unlines (map displayMsg errs)
  displayMsg (DesugarErrors errs) = unlines (map displayMsg errs)
  displayMsg (CompileErrors errs) = unlines (map displayMsg errs)
  displayMsg (OperatorConflict sources name) =
    "operator naming conflict: "
      ++ T.unpack name
      ++ case sources of
        [] -> ""
        _ -> " (declared in " ++ intercalate ", " sources ++ ")"
      ++ "\n"
