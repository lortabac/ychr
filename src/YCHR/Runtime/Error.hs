{-# LANGUAGE OverloadedStrings #-}

-- | Helpers that raise runtime errors from any runtime module
-- ('runtimeError'', 'runtimeErrorS'), the 'CallStack' alias they thread
-- through, and the 'RuntimeErrorThrown' exception they throw. Living
-- here keeps "YCHR.Runtime.Registry" and "YCHR.Runtime.Session" free of
-- import cycles with "YCHR.Runtime.Interpreter".
--
-- Rendering lives in "YCHR.Display": the top-level driver catches
-- 'RuntimeErrorThrown', lifts it into 'YCHR.Run.RuntimeError', and
-- displays it via the same 'displayMsgWithSrcLoc' machinery used by
-- every other diagnostic.
module YCHR.Runtime.Error
  ( -- * Call stack
    CallStack,

    -- * Raising runtime errors
    RuntimeErrorThrown (..),
    runtimeError',
    runtimeErrorS,
  )
where

import Control.Exception (Exception, throwIO)
import Data.Text qualified as T
import Effectful
import Effectful.State.Static.Local (State, get)
import YCHR.VM (StackFrame)

-- | Runtime call stack for error reporting (newest first).
type CallStack = [StackFrame]

-- | Exception thrown by 'runtimeError'' and 'runtimeErrorS'. Carries
-- the message and the call stack captured at the throw site (newest
-- frame first). The top-level driver catches this and lifts it into
-- 'YCHR.Run.RuntimeError' for rendering.
data RuntimeErrorThrown = RuntimeErrorThrown String [StackFrame]
  deriving (Show)

instance Exception RuntimeErrorThrown

-- | Raise a runtime error with the current call stack.
-- Throws 'RuntimeErrorThrown' so the driver can catch and display it.
runtimeError' ::
  (IOE :> es, State CallStack :> es) =>
  String ->
  T.Text ->
  Eff es a
runtimeError' prefix detail = do
  stack <- get @CallStack
  liftIO $ throwIO (RuntimeErrorThrown (prefix ++ T.unpack detail) stack)

-- | Raise a runtime error with the current call stack (String-only variant).
-- Throws 'RuntimeErrorThrown' so the driver can catch and display it.
runtimeErrorS ::
  (IOE :> es, State CallStack :> es) =>
  String ->
  Eff es a
runtimeErrorS msg = do
  stack <- get @CallStack
  liftIO $ throwIO (RuntimeErrorThrown msg stack)
