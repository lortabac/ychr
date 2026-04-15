{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Runtime error formatting with annotation stack traces.
module YCHR.Runtime.Error
  ( displayRuntimeError,
    runtimeErrorCode,
  )
where

import Data.List (intercalate)
import Data.Text qualified as T
import System.Console.ANSI (Color (..), ColorIntensity (..), ConsoleIntensity (..), ConsoleLayer (..), SGR (..), setSGRCode)
import YCHR.Loc (SourceLoc (..), dummyLoc)
import YCHR.VM (SourceAnnotation (..))

-- | Runtime error code.
runtimeErrorCode :: String
runtimeErrorCode = "YCHR-60001"

-- | Format a runtime error with an annotation stack trace.
--
-- The top stack frame (most recent) is displayed as the error location.
-- Subsequent frames are displayed as notes showing the call context.
-- The stack is expected newest-first (head = most recent).
--
-- Each frame follows the same format as 'YCHR.Display.displayMsgWithSrcLoc':
-- every message ends with a newline followed by a reset escape.
-- Messages are joined with @\"\\n\"@ so a blank line appears between them
-- (same convention as 'YCHR.Display.displayErrors').
displayRuntimeError :: String -> [SourceAnnotation] -> String
displayRuntimeError msg [] =
  formatFrame "error" Red msg dummyLoc Nothing
displayRuntimeError msg (top : rest) =
  intercalate
    "\n"
    ( formatFrame "error" Red msg top.annSourceLoc (Just (T.unpack top.annSourceCode))
        : map (\ann -> formatFrame "note" Cyan "stack trace:" ann.annSourceLoc (Just (T.unpack ann.annSourceCode))) rest
    )

-- | Format a single diagnostic frame.  Mirrors the layout of
-- 'YCHR.Display.displayMsgWithSrcLoc'.
formatFrame :: String -> Color -> String -> SourceLoc -> Maybe String -> String
formatFrame sev color msg loc maybeNode =
  setSGRCode [SetConsoleIntensity BoldIntensity]
    ++ displaySrcLoc loc
    ++ ": "
    ++ setSGRCode [SetColor Foreground Vivid color]
    ++ sev
    ++ setSGRCode [SetColor Foreground Dull White]
    ++ ": "
    ++ runtimeErrorCode
    ++ "\n"
    ++ msg
    ++ maybe "" (\n -> "\n" ++ setSGRCode [SetItalicized True] ++ n ++ setSGRCode [SetItalicized False]) maybeNode
    ++ "\n"
    ++ setSGRCode [Reset]

-- | Display a source location as @file:line:col@.
displaySrcLoc :: SourceLoc -> String
displaySrcLoc loc = loc.file ++ ":" ++ show loc.line ++ ":" ++ show loc.col
