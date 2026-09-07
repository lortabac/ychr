{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Decoding a host-call argument into constraint tells.
--
-- Several host calls take "a goal" — a constraint term, a list of them
-- run in order, or a @;@ disjunction of either — kept symbolic with
-- @quote\/1@, and run it in a forked session: @run_chr_session\/1@
-- ("YCHR.Internal.Runtime.SubSession") and the search entry points
-- ("YCHR.Internal.Runtime.Search"). The search driver
-- reads the alternatives of a choice point the same way. This module
-- is the decoding they share.
--
-- Names are resolved, and their tell procedures looked up, before the
-- tell happens. For a caller-supplied goal that is done in the
-- /calling/ session, before the fork exists, which is what keeps a
-- misspelled or unexported constraint a loud caller error rather than
-- a @false@ result or a failed search branch.
module YCHR.Internal.Runtime.Goal
  ( goalConstraints,
    altGoalConstraints,
    altName,
    listElems,
  )
where

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
import YCHR.Internal.Runtime.Registry (valueList)
import YCHR.Internal.Runtime.Session (resolveByExport)
import YCHR.Internal.Runtime.Types (Value (..))
import YCHR.Internal.Runtime.Var (deref)
import YCHR.Internal.Types (Term (..), flattenName)
import YCHR.Internal.Types qualified as Types

-- | The qualified name the runtime keys choice points on.
--
-- One wired-in name, in the spirit of @'$call'@. This is provisional:
-- when a library gains a way to nominate a constraint to the runtime
-- (the VM already carries an evaluables dispatch table shaped much
-- like it), this becomes a lookup and the name stops being special.
-- The arity is pinned by the one-element pattern in
-- 'YCHR.Internal.Runtime.Search.findChoice'.
altName :: Types.Name
altName = Types.Qualified "search" "alt"

-- | How a goal's constraint names are resolved.
data GoalScope
  = -- | Through the program's exports, the way a caller-supplied goal
    -- has to be: a name the caller could not have written by hand is
    -- a caller error.
    ExportedOnly
  | -- | By qualified name alone. A choice point's alternatives are
    -- often disjuncts lifted out of a @;@, which are module-internal
    -- and exported by nobody, so the export check would reject
    -- exactly the goals the compiler itself generated.
    AnyDeclared

-- | Decompose a goal argument into constraint tells, resolving each
-- name against the session's exports up front. A list value means
-- several goals in order; anything else is a single goal.
--
-- @who@ prefixes any error message with the host call's name, so the
-- diagnostic points at @solve@ or @run_chr_session@ rather than at
-- this shared helper.
goalConstraints :: String -> Value -> Chr [(Types.Name, [Value])]
goalConstraints = goalTells ExportedOnly

-- | 'goalConstraints' for one alternative of a choice point, which
-- reaches constraints no module exports. See 'AnyDeclared'.
altGoalConstraints :: String -> Value -> Chr [(Types.Name, [Value])]
altGoalConstraints = goalTells AnyDeclared

goalTells :: GoalScope -> String -> Value -> Chr [(Types.Name, [Value])]
goalTells scope who v = do
  elems <- listElems v
  case elems of
    Just gs -> concat <$> traverse (oneGoal scope who) gs
    Nothing -> oneGoal scope who v

-- | One goal. A @;@ compound becomes a tell of @search:alt@ over its
-- flattened alternatives, so a disjunction reaches the driver as an
-- ordinary choice point; anything else is a single constraint.
oneGoal :: GoalScope -> String -> Value -> Chr [(Types.Name, [Value])]
oneGoal scope who v = do
  v' <- deref v
  case v' of
    VTerm f [_, _] | isSemicolonFunctor f -> do
      alts <- semicolonAlts v'
      requireTellProc who altName 1
      pure [(altName, [valueList alts])]
    _ -> (: []) <$> goalConstraint scope who v'

-- | Flatten the right spine of a @;@ compound. @;@ is @xfy@, so
-- @(a ; b ; c)@ is @';'(a, ';'(b, c))@ and yields three alternatives.
-- A left-nested @((a ; b) ; c)@ keeps its left operand as a single
-- alternative, which is itself a disjunctive goal and becomes a
-- nested choice point — the same solution order either way.
semicolonAlts :: Value -> Chr [Value]
semicolonAlts v = do
  v' <- deref v
  case v' of
    VTerm f [l, r] | isSemicolonFunctor f -> (l :) <$> semicolonAlts r
    _ -> pure [v']

-- | @;@ is in 'YCHR.Internal.Rename.Types.reservedSymbolSet', so it is
-- never module-qualified and its mangled functor is the bare symbol.
isSemicolonFunctor :: T.Text -> Bool
isSemicolonFunctor f = f == ";"

-- | One goal: a compound or atom whose (mangled) functor names a
-- constraint. Arguments are passed through untouched so unbound
-- out-variables reach the forked session live.
goalConstraint :: GoalScope -> String -> Value -> Chr (Types.Name, [Value])
goalConstraint scope who v = do
  v' <- deref v
  case v' of
    VAtom f | not (isListFunctor f) -> resolveGoal scope who f []
    VTerm f args | not (isListFunctor f) -> resolveGoal scope who f args
    _ ->
      runtimeErrorS
        (who ++ ": goal must be a constraint term or a list of them")

-- | Resolve a goal functor to its qualified constraint name and check
-- that the tell procedure exists, mirroring
-- 'YCHR.Internal.Runtime.Session.tellConstraint'. Failing here (rather
-- than inside the forked session) keeps "unknown constraint" a caller
-- error.
resolveGoal :: GoalScope -> String -> T.Text -> [Value] -> Chr (Types.Name, [Value])
resolveGoal scope who f args = do
  SessionEnv {exportMap, exportedSet} <- ask
  resolved <- case (scope, functorName f) of
    -- A qualified name reaching a choice point was put there by the
    -- compiler or by a module that could already see it; the export
    -- list has nothing left to say about it.
    (AnyDeclared, qname@(Types.Qualified _ _)) -> pure qname
    (_, name) -> case resolveByExport exportMap exportedSet name arity of
      Left err -> runtimeErrorS (who ++ ": " ++ err)
      Right qname -> pure qname
  requireTellProc who resolved arity
  pure (resolved, args)
  where
    arity = length args
    functorName mangled = case decodeName mangled [] of
      CompoundTerm name _ -> name
      -- 'decodeName' always yields a compound for a functor text.
      _ -> Types.Unqualified mangled

-- | Check that a resolved constraint has a tell procedure in this
-- program, so a missing one is reported against the goal rather than
-- as a bare procedure-lookup failure later on.
requireTellProc :: String -> Types.Name -> Int -> Chr ()
requireTellProc who name arity = do
  SessionEnv {procMap} <- ask
  pm <- liftIO (readIORef procMap)
  unless (Map.member (tellProcName name arity) pm) $
    runtimeErrorS
      ( who
          ++ ": constraint not found: "
          ++ T.unpack (flattenName name)
          ++ "/"
          ++ show arity
      )

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
