{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Runtime error formatting with call stack traces.
module YCHR.Runtime.Error
  ( displayRuntimeError,
    runtimeErrorCode,
  )
where

import Data.List (intercalate)
import Data.Text qualified as T
import System.Console.ANSI (Color (..), ColorIntensity (..), ConsoleIntensity (..), ConsoleLayer (..), SGR (..), setSGRCode)
import YCHR.Loc (SourceLoc (..), dummyLoc)
import YCHR.VM (StackFrame (..))

-- | Runtime error code.
runtimeErrorCode :: String
runtimeErrorCode = "YCHR-60001"

-- | Format a runtime error with a call stack trace.
--
-- The top stack frame (most recent) is displayed as the error location.
-- Subsequent frames are displayed as notes showing the call context.
-- The stack is expected newest-first (head = most recent).
--
-- Each frame follows the same format as 'YCHR.Display.displayMsgWithSrcLoc':
-- every message ends with a newline followed by a reset escape.
-- Messages are joined with @\"\\n\"@ so a blank line appears between them
-- (same convention as 'YCHR.Display.displayErrors').
displayRuntimeError :: String -> [StackFrame] -> String
displayRuntimeError msg [] =
  formatFrame "runtime error" Magenta msg dummyLoc Nothing Nothing
displayRuntimeError msg (top : rest) =
  intercalate
    "\n"
    ( formatFrame "runtime error" Magenta msg top.frameSourceLoc (Just (T.unpack top.frameLabel)) (Just (T.unpack top.frameSourceCode))
        : map (\frame -> formatFrame "stack trace" Cyan "" frame.frameSourceLoc (Just (T.unpack frame.frameLabel)) (Just (T.unpack frame.frameSourceCode))) rest
    )

-- | Format a single diagnostic frame.  Mirrors the layout of
-- 'YCHR.Display.displayMsgWithSrcLoc'.
formatFrame :: String -> Color -> String -> SourceLoc -> Maybe String -> Maybe String -> String
formatFrame sev color msg loc maybeLabel maybeNode =
  let c = setSGRCode [SetColor Foreground Vivid color]
      r = setSGRCode [Reset]
   in c
        ++ "=== "
        ++ sev
        ++ " ==="
        ++ r
        ++ "\n"
        ++ setSGRCode [SetConsoleIntensity BoldIntensity]
        ++ displaySrcLoc loc
        ++ ": "
        ++ runtimeErrorCode
        ++ "\n"
        ++ maybe "" (\l -> setSGRCode [SetConsoleIntensity BoldIntensity] ++ "<<" ++ l ++ ">>" ++ r ++ "\n") maybeLabel
        ++ (if null msg then "" else msg)
        ++ maybe "" (\n -> (if null msg then "" else "\n") ++ setSGRCode [SetItalicized True] ++ n ++ setSGRCode [SetItalicized False]) maybeNode
        ++ "\n"
        ++ r

-- | Display a source location as @file:line:col@.
displaySrcLoc :: SourceLoc -> String
displaySrcLoc loc = loc.file ++ ":" ++ show loc.line ++ ":" ++ show loc.col
