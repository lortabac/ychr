{-# LANGUAGE OverloadedStrings #-}

-- | Runtime error formatting with call stack traces.
--
-- Also owns the small set of helpers that raise runtime errors from any
-- runtime module ('runtimeError'', 'runtimeErrorS') and the shared
-- 'CallStack' type alias they thread through. Living here keeps
-- "YCHR.Runtime.Registry" and "YCHR.Runtime.Session" free of import
-- cycles with "YCHR.Runtime.Interpreter".
module YCHR.Runtime.Error
  ( -- * Display
    displayRuntimeError,
    runtimeErrorCode,

    -- * Call stack
    CallStack,

    -- * Raising runtime errors
    runtimeError',
    runtimeErrorS,
  )
where

import Data.List (intercalate)
import Data.Text qualified as T
import Effectful
import Effectful.State.Static.Local (State, get)
import System.Console.ANSI
  ( Color (..),
    ColorIntensity (..),
    ConsoleIntensity (..),
    ConsoleLayer (..),
    SGR (..),
    setSGRCode,
  )
import System.Exit (exitFailure)
import System.IO (hPutStr, stderr)
import YCHR.Loc (SourceLoc (..), dummyLoc)
import YCHR.VM (StackFrame (..))

-- | Runtime call stack for error reporting (newest first).
type CallStack = [StackFrame]

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
    ( formatFrame
        "runtime error"
        Magenta
        msg
        top.frameSourceLoc
        ( Just
            ( T.unpack
                top.frameLabel
            )
        )
        (Just (T.unpack top.frameSourceCode))
        : map
          ( \frame ->
              formatFrame
                "stack trace"
                Cyan
                ""
                frame.frameSourceLoc
                ( Just
                    ( T.unpack
                        frame.frameLabel
                    )
                )
                (Just (T.unpack frame.frameSourceCode))
          )
          rest
    )

-- | Format a single diagnostic frame.  Mirrors the layout of
-- 'YCHR.Display.displayMsgWithSrcLoc'.
formatFrame ::
  String ->
  Color ->
  String ->
  SourceLoc ->
  Maybe String ->
  Maybe String ->
  String
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
        ++ maybe
          ""
          ( \l ->
              setSGRCode [SetConsoleIntensity BoldIntensity]
                ++ "<<"
                ++ l
                ++ ">>"
                ++ r
                ++ "\n"
          )
          maybeLabel
        ++ (if null msg then "" else msg)
        ++ maybe
          ""
          ( \n ->
              (if null msg then "" else "\n")
                ++ setSGRCode [SetItalicized True]
                ++ n
                ++ setSGRCode [SetItalicized False]
          )
          maybeNode
        ++ "\n"
        ++ r

-- | Display a source location as @file:line:col@.
displaySrcLoc :: SourceLoc -> String
displaySrcLoc loc = loc.file ++ ":" ++ show loc.line ++ ":" ++ show loc.col

-- | Raise a runtime error with the current call stack.
-- Prints the formatted error to stderr and exits.
runtimeError' ::
  (IOE :> es, State CallStack :> es) =>
  String ->
  T.Text ->
  Eff es a
runtimeError' prefix detail = do
  stack <- get @CallStack
  liftIO $ do
    hPutStr stderr $ displayRuntimeError (prefix ++ T.unpack detail) stack
    exitFailure

-- | Raise a runtime error with the current call stack (String-only variant).
-- Prints the formatted error to stderr and exits.
runtimeErrorS ::
  (IOE :> es, State CallStack :> es) =>
  String ->
  Eff es a
runtimeErrorS msg = do
  stack <- get @CallStack
  liftIO $ do
    hPutStr stderr $ displayRuntimeError msg stack
    exitFailure
