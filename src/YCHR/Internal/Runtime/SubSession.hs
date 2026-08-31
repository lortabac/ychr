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

import Control.Exception (try)
import Control.Monad (unless)
import Control.Monad.IO.Class (liftIO)
import Control.Monad.Trans.Reader (ask)
import Data.IORef (readIORef)
import Data.Map.Strict qualified as Map
import Data.Text qualified as T
import YCHR.Internal.Compile (tellProcName)
import YCHR.Internal.Meta (decodeName, metaHostCallRegistry)
import YCHR.Internal.Runtime.Error (RuntimeErrorThrown, runtimeErrorS)
import YCHR.Internal.Runtime.Monad
  ( Chr,
    SessionEnv (..),
    forkSessionEnv,
    runChr,
  )
import YCHR.Internal.Runtime.Registry
  ( HostCallFn (..),
    HostCallRegistry,
    baseHostCallRegistry,
  )
import YCHR.Internal.Runtime.Session (resolveByExport, tellConstraint)
import YCHR.Internal.Runtime.Types (Value (..))
import YCHR.Internal.Runtime.Var (deref)
import YCHR.Internal.Types (Term (..))
import YCHR.Internal.Types qualified as Types
import YCHR.Internal.VM (Name (..))

-- | Registry providing @run_chr_session/1@. Part of
-- 'defaultHostCallRegistry'; union it in explicitly when assembling a
-- custom registry that should support the @meta@ library's
-- @run_chr_session@ wrapper.
subSessionHostCallRegistry :: HostCallRegistry
subSessionHostCallRegistry =
  Map.fromList [(Name "run_chr_session", HostCallFn runChrSession)]

-- | The default host-call registry — base builtins, the @meta@
-- library's host calls, and @run_chr_session@. This is what the
-- @ychr@ CLI and the default 'YCHR.Convert' / 'YCHR.DSL' entry points
-- use. Defined here rather than in "YCHR.Internal.Meta" because this
-- is the topmost of the three component modules.
defaultHostCallRegistry :: HostCallRegistry
defaultHostCallRegistry =
  baseHostCallRegistry <> metaHostCallRegistry <> subSessionHostCallRegistry

-- | @run_chr_session(Goal)@: @Goal@ is a single constraint term or a
-- list of them. Each is told into a fresh session of the current
-- program, in order. Returns @true@ when the sub-session runs to
-- quiescence, @false@ when it raises a runtime error. Results flow
-- back through out-variables shared with the goal.
--
-- Goal constraint names are resolved (and their tell procedures
-- looked up) in the calling session before the sub-session starts, so
-- a misspelled or unexported constraint is a loud caller error, never
-- a @false@ result.
runChrSession :: [Value] -> Chr Value
runChrSession [goalArg] = do
  goals <- goalConstraints goalArg
  env <- ask
  -- 'forkSessionEnv' is what makes this "the same program, from
  -- scratch": fresh store, history, queue and call stack, everything
  -- else — including the variable and suspension-id counters, and the
  -- trace state — carried over. See its documentation for why the
  -- counters are shared.
  sub <- liftIO (forkSessionEnv env)
  result <- liftIO (try (runChr (mapM_ (uncurry tellConstraint) goals) sub))
  case result of
    Left (_ :: RuntimeErrorThrown) -> pure (VBool False)
    Right () -> pure (VBool True)
runChrSession _ = runtimeErrorS "run_chr_session: expected 1 argument"

-- | Decompose the goal argument into constraint tells, resolving each
-- name against the session's exports up front. A list value means
-- several goals in order; anything else is a single goal.
goalConstraints :: Value -> Chr [(Types.Name, [Value])]
goalConstraints v = do
  elems <- listElems v
  case elems of
    Just gs -> traverse goalConstraint gs
    Nothing -> (: []) <$> goalConstraint v

-- | One goal: a compound or atom whose (mangled) functor names an
-- exported constraint. Arguments are passed through untouched so
-- unbound out-variables reach the sub-session live.
goalConstraint :: Value -> Chr (Types.Name, [Value])
goalConstraint v = do
  v' <- deref v
  case v' of
    VAtom f | not (isListFunctor f) -> resolveGoal f []
    VTerm f args | not (isListFunctor f) -> resolveGoal f args
    _ ->
      runtimeErrorS
        "run_chr_session: goal must be a constraint term or a list of them"

-- | Resolve a goal functor to its qualified constraint name and check
-- that the tell procedure exists, in the calling session, mirroring
-- 'tellConstraint'. Failing here (rather than inside the sub-session)
-- keeps "unknown constraint" a caller error instead of a @false@.
resolveGoal :: T.Text -> [Value] -> Chr (Types.Name, [Value])
resolveGoal f args = do
  SessionEnv {procMap, exportMap, exportedSet} <- ask
  resolved <- case resolveByExport exportMap exportedSet (functorName f) arity of
    Left err -> runtimeErrorS ("run_chr_session: " ++ err)
    Right qname -> pure qname
  pm <- liftIO (readIORef procMap)
  unless (Map.member (tellProcName resolved arity) pm) $
    runtimeErrorS
      ("run_chr_session: constraint not found: " ++ T.unpack f)
  pure (resolved, args)
  where
    arity = length args
    functorName mangled = case decodeName mangled [] of
      CompoundTerm name _ -> name
      -- 'decodeName' always yields a compound for a functor text.
      _ -> Types.Unqualified mangled

-- | Is this mangled functor the list constructor or the empty list?
-- A goal must never be one: a cons cell here means an improper list
-- slipped past 'listElems', which should fail as a malformed goal,
-- not resolve as a constraint named @.@.
isListFunctor :: T.Text -> Bool
isListFunctor f =
  f == "prelude__." || f == "." || f == "prelude__[]" || f == "[]"

-- | Walk a (possibly nested-under-variables) runtime list. 'Nothing'
-- when the value is not a list at all. A deref-aware variant of
-- 'YCHR.Internal.Runtime.Registry.fromValueList'.
listElems :: Value -> Chr (Maybe [Value])
listElems v = do
  v' <- deref v
  case v' of
    VAtom a | a == "prelude__[]" || a == "[]" -> pure (Just [])
    VTerm f [h, t]
      | f == "prelude__." || f == "." ->
          fmap (h :) <$> listElems t
    _ -> pure Nothing
