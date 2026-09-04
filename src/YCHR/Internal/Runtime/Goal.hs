{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Decoding a host-call argument into constraint tells.
--
-- Several host calls take "a goal" — a constraint term, or a list of
-- them run in order, kept symbolic with @quote\/1@ —  and run it in a
-- forked session: @run_chr_session\/1@
-- ("YCHR.Internal.Runtime.SubSession") and @solve\/1@ \/
-- @find_all\/2@ ("YCHR.Internal.Runtime.Search"). This module is the
-- decoding they share.
--
-- Names are resolved, and their tell procedures looked up, in the
-- /calling/ session, before the fork exists. That is what keeps a
-- misspelled or unexported constraint a loud caller error rather than
-- a @false@ result or a failed search branch.
module YCHR.Internal.Runtime.Goal (goalConstraints, listElems) where

import Control.Monad (unless)
import Control.Monad.IO.Class (liftIO)
import Control.Monad.Trans.Reader (ask)
import Data.IORef (readIORef)
import Data.Map.Strict qualified as Map
import Data.Text qualified as T
import YCHR.Internal.Compile (tellProcName)
import YCHR.Internal.Meta (decodeName)
import YCHR.Internal.Runtime.Error (runtimeErrorS)
import YCHR.Internal.Runtime.Monad (Chr, SessionEnv (..))
import YCHR.Internal.Runtime.Session (resolveByExport)
import YCHR.Internal.Runtime.Types (Value (..))
import YCHR.Internal.Runtime.Var (deref)
import YCHR.Internal.Types (Term (..))
import YCHR.Internal.Types qualified as Types

-- | Decompose a goal argument into constraint tells, resolving each
-- name against the session's exports up front. A list value means
-- several goals in order; anything else is a single goal.
--
-- @who@ prefixes any error message with the host call's name, so the
-- diagnostic points at @solve@ or @run_chr_session@ rather than at
-- this shared helper.
goalConstraints :: String -> Value -> Chr [(Types.Name, [Value])]
goalConstraints who v = do
  elems <- listElems v
  case elems of
    Just gs -> traverse (goalConstraint who) gs
    Nothing -> (: []) <$> goalConstraint who v

-- | One goal: a compound or atom whose (mangled) functor names an
-- exported constraint. Arguments are passed through untouched so
-- unbound out-variables reach the forked session live.
goalConstraint :: String -> Value -> Chr (Types.Name, [Value])
goalConstraint who v = do
  v' <- deref v
  case v' of
    VAtom f | not (isListFunctor f) -> resolveGoal who f []
    VTerm f args | not (isListFunctor f) -> resolveGoal who f args
    _ ->
      runtimeErrorS
        (who ++ ": goal must be a constraint term or a list of them")

-- | Resolve a goal functor to its qualified constraint name and check
-- that the tell procedure exists, in the calling session, mirroring
-- 'YCHR.Internal.Runtime.Session.tellConstraint'. Failing here (rather
-- than inside the forked session) keeps "unknown constraint" a caller
-- error.
resolveGoal :: String -> T.Text -> [Value] -> Chr (Types.Name, [Value])
resolveGoal who f args = do
  SessionEnv {procMap, exportMap, exportedSet} <- ask
  resolved <- case resolveByExport exportMap exportedSet (functorName f) arity of
    Left err -> runtimeErrorS (who ++ ": " ++ err)
    Right qname -> pure qname
  pm <- liftIO (readIORef procMap)
  unless (Map.member (tellProcName resolved arity) pm) $
    runtimeErrorS (who ++ ": constraint not found: " ++ T.unpack f)
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
