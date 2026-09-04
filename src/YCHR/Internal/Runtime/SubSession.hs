{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE OverloadedStrings #-}

-- | The @run_chr_session@ host function: run a goal in a fresh,
-- isolated session of the current program.
--
-- The sub-session gets its own constraint store, propagation history,
-- reactivation queue, and call stack, but shares the outer session's
-- procedures, host-call registry, evaluables, and export maps — it is
-- "the same program, from scratch". This gives CHR code the same
-- throwaway-session isolation an embedder gets from calling 'withCHR'
-- again, without leaving CHR.
--
-- == Variable-sharing contract
--
-- Logical variables are 'Data.IORef.IORef' cells, so a variable
-- reachable from the goal is /the same variable/ inside the
-- sub-session: bindings made there persist after the call returns.
-- This is the result channel — pass fresh unbound out-variables in
-- the goal and read them afterwards.
--
-- Reactivation does NOT cross the boundary. A shared variable's
-- observer list may carry suspension ids from both sessions; ids are
-- globally unique (the id supply is shared, like the variable
-- counter), and each session drops foreign ids at enqueue
-- ("YCHR.Internal.Runtime.Reactivation"). So binding a shared
-- variable reactivates only the binding session's own observers. The
-- common benign case is the calling rule's already-killed head
-- constraint observing an out-variable — nothing to reactivate. The
-- case to avoid is a /live/ stored constraint of one session
-- observing a variable the other session binds: the observer is
-- simply not reactivated, which can leave the observing session
-- incomplete (a rule that should have fired on the new binding does
-- not). In practice: pass only ground terms and fresh variables in,
-- and have the sub-session bind its out-variables before quiescence.
--
-- The module lives outside "YCHR.Internal.Meta" because the
-- implementation needs 'YCHR.Internal.Runtime.Session.tellConstraint',
-- and "YCHR.Internal.Runtime.Session" transitively imports
-- "YCHR.Internal.Meta" (via the interpreter).
module YCHR.Internal.Runtime.SubSession
  ( subSessionHostCallRegistry,
    defaultHostCallRegistry,
  )
where

import Control.Exception (SomeException, fromException, throwIO, try)
import Control.Monad.IO.Class (liftIO)
import Control.Monad.Trans.Reader (ask)
import Data.Map.Strict qualified as Map
import YCHR.Internal.Meta (metaHostCallRegistry)
import YCHR.Internal.Runtime.Error
  ( RuntimeErrorThrown,
    SearchFailure,
    runtimeErrorS,
  )
import YCHR.Internal.Runtime.Goal (goalConstraints)
import YCHR.Internal.Runtime.Monad
  ( Chr,
    forkSessionEnv,
    runChr,
  )
import YCHR.Internal.Runtime.Registry
  ( HostCallFn (..),
    HostCallRegistry,
    baseHostCallRegistry,
  )
import YCHR.Internal.Runtime.Search (searchHostCallRegistry)
import YCHR.Internal.Runtime.Session (tellConstraint)
import YCHR.Internal.Runtime.Types (Value (..))
import YCHR.Internal.VM (Name (..))

-- | Registry providing @run_chr_session/1@. Part of
-- 'defaultHostCallRegistry'; union it in explicitly when assembling a
-- custom registry that should support the @meta@ library's
-- @run_chr_session@ wrapper.
subSessionHostCallRegistry :: HostCallRegistry
subSessionHostCallRegistry =
  Map.fromList [(Name "run_chr_session", HostCallFn runChrSession)]

-- | The default host-call registry — base builtins, the @meta@
-- library's host calls, @run_chr_session@, and @library(search)@. This
-- is what the @ychr@ CLI and the default 'YCHR.Convert' / 'YCHR.DSL'
-- entry points use. Defined here rather than in "YCHR.Internal.Meta"
-- because this is the topmost of the component modules.
defaultHostCallRegistry :: HostCallRegistry
defaultHostCallRegistry =
  baseHostCallRegistry
    <> metaHostCallRegistry
    <> subSessionHostCallRegistry
    <> searchHostCallRegistry

-- | @run_chr_session(Goal)@: @Goal@ is a single constraint term or a
-- list of them. Each is told into a fresh session of the current
-- program, in order. Returns @true@ if and only if the sub-session
-- runs to quiescence, and @false@ otherwise. Results flow back through
-- out-variables shared with the goal.
--
-- \"Otherwise\" is two things: a runtime error, and — when the call
-- happens inside a search branch — a branch failure raised by
-- @search:fail\/0@. Catching both is what makes the sub-session
-- boundary total, so that a @fail@ inside the goal is contained here
-- rather than escaping to fail the enclosing search branch. For a
-- program that never searches the behaviour is unchanged, since a
-- 'SearchFailure' cannot arise without a search.
--
-- The cost is that @false@ does not distinguish a bug in the goal from
-- a deliberate failure. That conflation was already this call's
-- contract for errors, and it is bounded by the caller getting a
-- boolean it has to test — unlike search itself, where the same
-- conflation would silently turn a bug into a dead end.
--
-- Bindings the sub-session made before failing are not rolled back:
-- there is no choice point here and no mark to unwind to. Running the
-- sub-session inside a search branch is what puts it under an
-- enclosing driver's marks.
--
-- Goal constraint names are resolved (and their tell procedures
-- looked up) in the calling session before the sub-session starts, so
-- a misspelled or unexported constraint is a loud caller error, never
-- a @false@ result.
runChrSession :: [Value] -> Chr Value
runChrSession [goalArg] = do
  goals <- goalConstraints "run_chr_session" goalArg
  env <- ask
  -- 'forkSessionEnv' is what makes this "the same program, from
  -- scratch": fresh store, history, queue and call stack, everything
  -- else — including the variable and suspension-id counters, the
  -- search trail, and the trace state — carried over. See its
  -- documentation for why the counters and the trail are shared.
  sub <- liftIO (forkSessionEnv env)
  result <- liftIO (try (runChr (mapM_ (uncurry tellConstraint) goals) sub))
  case result of
    Right () -> pure (VBool True)
    Left e
      | quiescenceNotReached e -> pure (VBool False)
      | otherwise -> liftIO (throwIO e)
runChrSession _ = runtimeErrorS "run_chr_session: expected 1 argument"

-- | Did this exception mean "the goal did not run to quiescence", as
-- opposed to something the sub-session boundary has no business
-- swallowing (an asynchronous exception, say)?
quiescenceNotReached :: SomeException -> Bool
quiescenceNotReached e =
  case fromException e :: Maybe RuntimeErrorThrown of
    Just _ -> True
    Nothing -> case fromException e :: Maybe SearchFailure of
      Just _ -> True
      Nothing -> False
