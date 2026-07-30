{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Helpers that raise runtime errors from any 'Chr' action
-- ('runtimeError'', 'runtimeErrorS'), the 'CallStack' alias they read
-- through, and the 'RuntimeErrorThrown' exception they throw. Living
-- here keeps "YCHR.Internal.Runtime.Registry" and "YCHR.Internal.Runtime.Session" free of
-- import cycles with "YCHR.Internal.Runtime.Interpreter".
--
-- Rendering lives in "YCHR.Internal.Display": the top-level driver catches
-- 'RuntimeErrorThrown', lifts it into 'YCHR.Run.RuntimeError', and
-- displays it via the same 'displayMsgWithSrcLoc' machinery used by
-- every other diagnostic.
module YCHR.Internal.Runtime.Error
  ( -- * Call stack
    CallStack,

    -- * Raising runtime errors
    RuntimeErrorThrown (..),
    runtimeError',
    runtimeErrorS,
  )
where

import Control.Exception (Exception, throwIO)
import Control.Monad.IO.Class (liftIO)
import Control.Monad.Trans.Reader (ask)
import Data.IORef (readIORef)
import Data.Text qualified as T
import YCHR.Internal.Runtime.Monad (CallStack, Chr, SessionEnv (..))
import YCHR.Internal.VM (StackFrame)

-- | Exception thrown by 'runtimeError'' and 'runtimeErrorS'. Carries
-- the message and the call stack captured at the throw site (newest
-- frame first). The top-level driver catches this and lifts it into
-- 'YCHR.Run.RuntimeError' for rendering.
data RuntimeErrorThrown = RuntimeErrorThrown String [StackFrame]
  deriving (Show)

instance Exception RuntimeErrorThrown

-- | Raise a runtime error with the current call stack.
runtimeError' :: String -> T.Text -> Chr a
runtimeError' prefix detail = do
  SessionEnv {callStack} <- ask
  stack <- liftIO $ readIORef callStack
  liftIO $ throwIO (RuntimeErrorThrown (prefix ++ T.unpack detail) stack)

-- | Raise a runtime error with the current call stack (String-only variant).
runtimeErrorS :: String -> Chr a
runtimeErrorS msg = do
  SessionEnv {callStack} <- ask
  stack <- liftIO $ readIORef callStack
  liftIO $ throwIO (RuntimeErrorThrown msg stack)
