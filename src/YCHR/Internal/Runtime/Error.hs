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
    chrRuntimeErrorPrefix,
    closureUnboundError,
    closureNoMatchError,

    -- * Control-flow exceptions
    SearchFailure (..),
    isControlException,
  )
where

import Control.Exception
  ( Exception,
    SomeAsyncException,
    SomeException,
    fromException,
    throwIO,
  )
import Control.Monad.IO.Class (liftIO)
import Control.Monad.Trans.Reader (ask)
import Data.IORef (readIORef)
import Data.Maybe (isJust)
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

-- | The banner every CHR runtime error carries before its detail. The
-- host-call reporters in "YCHR.Internal.Runtime.Registry" and the
-- runtime's own raises share it, so the two cannot drift apart.
chrRuntimeErrorPrefix :: String
chrRuntimeErrorPrefix = "CHR runtime error: "

-- | @'$call'@ dispatch, first failure mode: the closure operand is
-- still an unbound logical variable, so no dispatch is decidable. An
-- /instantiation/ error, not a general one — a rule guard catches it
-- and retries the occurrence once reactivation binds the variable.
--
-- The message is the one the generated @call_N@ dispatchers used to
-- raise, kept byte-for-byte so guards, golden tests and both backends
-- keep reporting it identically.
closureUnboundError :: Chr a
closureUnboundError =
  instantiationErrorS $
    chrRuntimeErrorPrefix
      <> "'$call': closure argument is not sufficiently instantiated"
      <> " (unbound variable)"

-- | @'$call'@ dispatch, second failure mode: the operand is an
-- instantiated value that is not a callable — or a callable applied at
-- an arity other than the one it was declared at. Both are definite
-- mismatches, so both are general errors.
closureNoMatchError :: Chr a
closureNoMatchError =
  runtimeErrorS (chrRuntimeErrorPrefix <> "call: no matching closure")

throwWithStack :: RuntimeErrorKind -> String -> Chr a
throwWithStack kind msg = do
  SessionEnv {callStack} <- ask
  stack <- liftIO $ readIORef callStack
  liftIO $ throwIO (RuntimeErrorThrown kind msg (take maxCallStackDepth stack))

-- | Thrown by @search:fail\/0@ to abandon the current search branch,
-- and caught only by the search driver
-- ("YCHR.Internal.Runtime.Search").
--
-- Deliberately /not/ a 'RuntimeErrorThrown'. A branch failure is
-- ordinary control flow and an error is a bug; conflating them is what
-- makes generate-and-test programs undebuggable, so they are separate
-- types caught in separate places. It lives here, next to the error it
-- is not, because the host-call boundary below has to know about both
-- and sits underneath the module that raises this one.
data SearchFailure = SearchFailure
  deriving (Show)

instance Exception SearchFailure

-- | Does this exception carry control flow that a host-call boundary
-- must let through untouched, rather than wrapping into a
-- @host call X: …@ runtime error?
--
-- Three kinds qualify: asynchronous exceptions (the computation is
-- being killed), runtime errors (already carrying their own message
-- and captured stack — rewrapping would bury both), and search branch
-- failures (whose whole point is to reach the enclosing driver).
-- Everything else is a genuine host-side exception that the boundary
-- should turn into a runtime error naming the host call.
isControlException :: SomeException -> Bool
isControlException e =
  isJust (fromException e :: Maybe SomeAsyncException)
    || isJust (fromException e :: Maybe RuntimeErrorThrown)
    || isJust (fromException e :: Maybe SearchFailure)
