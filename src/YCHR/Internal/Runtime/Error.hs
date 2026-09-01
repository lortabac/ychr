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
    maxCallStackDepth,

    -- * Raising runtime errors
    RuntimeErrorKind (..),
    RuntimeErrorThrown (..),
    runtimeError',
    runtimeErrorS,
    instantiationErrorS,
  )
where

import Control.Exception (Exception, throwIO)
import Control.Monad.IO.Class (liftIO)
import Control.Monad.Trans.Reader (ask)
import Data.IORef (readIORef)
import Data.Text qualified as T
import YCHR.Internal.Runtime.Monad (CallStack, Chr, SessionEnv (..))
import YCHR.Internal.VM (StackFrame)

-- | Maximum number of call-stack frames carried on a runtime error.
--
-- Truncation happens here, at the single point where the stack is
-- /read/, rather than on every 'YCHR.Internal.Runtime.Interpreter.pushFrame':
-- pushing is on the hot path (once per rule fire and per function
-- entry) and re-truncating there allocated a fresh spine every time.
-- The reported frames are identical either way — the stack is
-- newest-first, so taking the first @n@ of the whole thing is what
-- truncating on the way in used to leave behind.
--
-- The un-truncated stack is bounded by the interpreter's call depth,
-- because every procedure call restores the frames it found on the
-- way out. That does make the stack O(call depth) rather than O(1):
-- a program that nests a million activations deep now retains a
-- million cons cells here. That is proportional to the interpreter's
-- own IO continuation chain at the same depth, so it adds no new
-- asymptotic class.
maxCallStackDepth :: Int
maxCallStackDepth = 10

-- | Why a runtime error was raised. The distinction is not cosmetic:
-- a rule guard catches 'InstantiationError' and evaluates to 'False'
-- (see @Note [Soft guard catch safety]@ in
-- "YCHR.Internal.Runtime.Interpreter"), while 'GeneralError'
-- propagates out of every position alike.
data RuntimeErrorKind
  = -- | An ordinary failure: a definite mismatch, a type error,
    -- division by zero, an arity mismatch. Always fatal to the query.
    GeneralError
  | -- | The computation demanded the value of a variable that is
    -- still unbound, so no verdict was possible. Raised only at a
    -- genuine demand point — never from the mere presence of an
    -- unbound variable in an argument list.
    InstantiationError
  deriving (Eq, Show)

-- | Exception thrown by 'runtimeError'' and 'runtimeErrorS'. Carries
-- the kind, the message, and the call stack captured at the throw
-- site (newest frame first). The top-level driver catches this and
-- lifts it into 'YCHR.Run.RuntimeError' for rendering; the kind is
-- not part of the user-facing error, only of the runtime's own
-- control flow.
data RuntimeErrorThrown = RuntimeErrorThrown RuntimeErrorKind String [StackFrame]
  deriving (Show)

instance Exception RuntimeErrorThrown

-- | Raise a general runtime error with the current call stack.
runtimeError' :: String -> T.Text -> Chr a
runtimeError' prefix detail = throwWithStack GeneralError (prefix ++ T.unpack detail)

-- | Raise a general runtime error with the current call stack
-- (String-only variant).
runtimeErrorS :: String -> Chr a
runtimeErrorS = throwWithStack GeneralError

-- | Raise an /instantiation/ runtime error with the current call
-- stack: the caller reached a point that demanded the value of an
-- unbound variable. Inside a rule guard this is caught and turned
-- into a silent @false@; everywhere else it behaves like
-- 'runtimeErrorS'.
instantiationErrorS :: String -> Chr a
instantiationErrorS = throwWithStack InstantiationError

throwWithStack :: RuntimeErrorKind -> String -> Chr a
throwWithStack kind msg = do
  SessionEnv {callStack} <- ask
  stack <- liftIO $ readIORef callStack
  liftIO $ throwIO (RuntimeErrorThrown kind msg (take maxCallStackDepth stack))
