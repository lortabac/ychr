{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Logical variables, compound terms, unification, and equality.
--
-- This module provides the foundational layer of the CHR Haskell runtime:
-- mutable logical variables with binding chains, Prolog-style unification
-- (tell semantics) and equality checking (ask semantics), and compound
-- term construction and inspection.
--
-- Unification collects observer IDs from bound variables, enabling
-- selective constraint reactivation (per the paper, Section 5.3).
-- Path compression is applied during dereferencing to amortize
-- future lookups.
module YCHR.Runtime.Var
  ( -- * Types (re-exported from YCHR.Runtime.Types)
    VarId (..),
    Var (..),
    VarState (..),
    Value (..),

    -- * Operations
    newVar,
    deref,
    unify,
    unifiable,
    equal,
    makeTerm,
    matchTerm,
    getArg,
    addObserver,
    getVarId,
  )
where

import Control.Monad.IO.Class (liftIO)
import Control.Monad.Trans.Reader (ask)
import Data.IORef
import Data.Text (Text)
import YCHR.Runtime.Monad (Chr, SessionEnv (..))
import YCHR.Runtime.Types
  ( SuspensionId,
    Value (..),
    Var (..),
    VarId (..),
    VarState (..),
  )

-- ---------------------------------------------------------------------------
-- Internal Unify primitives
-- ---------------------------------------------------------------------------

readVarState :: Var -> Chr VarState
readVarState (Var ref) = liftIO $ readIORef ref

writeVarState :: Var -> VarState -> Chr ()
writeVarState (Var ref) st = liftIO $ writeIORef ref st

newVarRef :: VarState -> Chr Var
newVarRef st = liftIO $ Var <$> newIORef st

freshVarId :: Chr VarId
freshVarId = do
  SessionEnv {varCounter} <- ask
  liftIO $ do
    vid@(VarId n) <- readIORef varCounter
    writeIORef varCounter (VarId (n + 1))
    pure vid

-- ---------------------------------------------------------------------------
-- Operations
-- ---------------------------------------------------------------------------

-- | Create a fresh unbound logical variable.
newVar :: Chr Value
newVar = do
  vid <- freshVarId
  v <- newVarRef (Unbound vid [])
  pure (VVar v)

-- | Follow binding chains to find the ultimate value, applying
-- path compression along the way. If the result is an unbound
-- variable, returns the 'VVar' wrapping it.
deref :: Value -> Chr Value
deref val@(VVar var@(Var ref)) = do
  st <- readVarState var
  case st of
    Unbound {} -> pure val
    Bound v -> do
      v' <- deref v
      case v' of
        VVar (Var ref')
          | ref == ref' -> pure ()
        _ -> writeVarState var (Bound v')
      pure v'
deref val = pure val

-- | Unify two values (tell semantics, Prolog @=@).
--
-- Returns @(success, observers)@: the boolean indicates whether
-- unification succeeded, and the list is the observer ids gathered
-- from every variable that was bound during the call. Callers
-- (typically the 'BUnify' interpretation in
-- "YCHR.Runtime.Interpreter") forward the observers to the
-- reactivation queue.
--
-- The observer list is meaningful even when @success@ is 'False':
-- 'unifyArgs' short-circuits on the first failing argument pair, but
-- variables bound by earlier pairs remain bound (we do not roll back),
-- and the observers from those bindings are still returned. Callers
-- must enqueue them so the half-committed bindings are followed up on.
unify :: Value -> Value -> Chr (Bool, [SuspensionId])
unify v1 v2 = do
  d1 <- deref v1
  d2 <- deref v2
  unify' d1 d2

unify' :: Value -> Value -> Chr (Bool, [SuspensionId])
unify' VWildcard _ = pure (True, [])
unify' _ VWildcard = pure (True, [])
unify' (VVar (Var ref1)) (VVar (Var ref2))
  | ref1 == ref2 = pure (True, [])
unify' (VVar var1) v2@(VVar var2) = do
  st1 <- readVarState var1
  case st1 of
    Bound {} -> error "unify': unexpected Bound after deref"
    Unbound _ obs1 -> do
      st2 <- readVarState var2
      case st2 of
        Unbound vid2 obs2 -> do
          writeVarState var1 (Bound v2)
          writeVarState var2 (Unbound vid2 (obs1 ++ obs2))
          pure (True, obs1)
        Bound {} -> error "unify': unexpected Bound after deref"
unify' (VVar var) v = do
  st <- readVarState var
  case st of
    Bound {} -> error "unify': unexpected Bound after deref"
    Unbound _ obs -> do
      writeVarState var (Bound v)
      pure (True, obs)
unify' v (VVar vr) = unify' (VVar vr) v
unify' (VInt a) (VInt b) = pure (a == b, [])
unify' (VFloat a) (VFloat b) = pure (a == b, [])
unify' (VAtom a) (VAtom b) = pure (a == b, [])
unify' (VText a) (VText b) = pure (a == b, [])
unify' (VBool a) (VBool b) = pure (a == b, [])
unify' (VTerm f1 args1) (VTerm f2 args2)
  | f1 == f2 && length args1 == length args2 = unifyArgs args1 args2
unify' _ _ = pure (False, [])

-- | Unify argument lists pairwise. Short-circuits on the first failure.
-- Observer lists from successful element unifications are concatenated.
unifyArgs :: [Value] -> [Value] -> Chr (Bool, [SuspensionId])
unifyArgs [] [] = pure (True, [])
unifyArgs (a : as) (b : bs) = do
  (ok, obs) <- unify a b
  if ok
    then do
      (ok', obs') <- unifyArgs as bs
      pure (ok', obs ++ obs')
    else pure (False, obs)
unifyArgs _ _ = pure (False, [])

-- | Check whether two values can be unified, without committing any
-- bindings. Returns 'True' iff 'unify' would succeed.
--
-- Mutations made to variable cells during the check are recorded on a
-- local trail and rolled back before returning, so the operation is
-- observably pure with respect to variable bindings. Path compression
-- performed by 'deref' is preserved (it is semantically invisible).
-- Observer lists are never modified.
unifiable :: Value -> Value -> Chr Bool
unifiable a b = do
  trailRef <- liftIO $ newIORef []
  result <- uni trailRef a b
  liftIO $ do
    entries <- readIORef trailRef
    -- Entries are prepended newest-first, so walking front-to-back
    -- restores each cell to its oldest captured state.
    mapM_ (\(Var ref, st) -> writeIORef ref st) entries
  pure result
  where
    trailWrite trailRef var@(Var ref) newSt = liftIO $ do
      cur <- readIORef ref
      modifyIORef' trailRef ((var, cur) :)
      writeIORef ref newSt

    uni trailRef v1 v2 = do
      d1 <- deref v1
      d2 <- deref v2
      uni' trailRef d1 d2

    uni' _ VWildcard _ = pure True
    uni' _ _ VWildcard = pure True
    uni' _ (VVar (Var ref1)) (VVar (Var ref2))
      | ref1 == ref2 = pure True
    uni' trailRef (VVar var1) v2@(VVar _) = do
      st1 <- readVarState var1
      case st1 of
        Bound {} -> error "unifiable: unexpected Bound after deref"
        Unbound _ _ -> do
          trailWrite trailRef var1 (Bound v2)
          pure True
    uni' trailRef (VVar var) v = do
      st <- readVarState var
      case st of
        Bound {} -> error "unifiable: unexpected Bound after deref"
        Unbound _ _ -> do
          trailWrite trailRef var (Bound v)
          pure True
    uni' trailRef v (VVar vr) = uni' trailRef (VVar vr) v
    uni' _ (VInt x) (VInt y) = pure (x == y)
    uni' _ (VFloat x) (VFloat y) = pure (x == y)
    uni' _ (VAtom x) (VAtom y) = pure (x == y)
    uni' _ (VText x) (VText y) = pure (x == y)
    uni' _ (VBool x) (VBool y) = pure (x == y)
    uni' trailRef (VTerm f1 args1) (VTerm f2 args2)
      | f1 == f2 && length args1 == length args2 = uniArgs trailRef args1 args2
    uni' _ _ _ = pure False

    uniArgs _ [] [] = pure True
    uniArgs trailRef (x : xs) (y : ys) = do
      ok <- uni trailRef x y
      if ok then uniArgs trailRef xs ys else pure False
    uniArgs _ _ _ = pure False

-- | Check equality of two values (ask semantics, Prolog @==@).
--
-- No mutation beyond path compression during dereferencing.
-- Two distinct unbound variables are /not/ equal.
equal :: Value -> Value -> Chr Bool
equal v1 v2 = do
  d1 <- deref v1
  d2 <- deref v2
  equal' d1 d2

equal' :: Value -> Value -> Chr Bool
equal' (VVar (Var ref1)) (VVar (Var ref2)) = pure (ref1 == ref2)
equal' (VVar _) _ = pure False
equal' _ (VVar _) = pure False
equal' (VInt a) (VInt b) = pure (a == b)
equal' (VFloat a) (VFloat b) = pure (a == b)
equal' (VAtom a) (VAtom b) = pure (a == b)
equal' (VText a) (VText b) = pure (a == b)
equal' (VBool a) (VBool b) = pure (a == b)
equal' (VTerm f1 args1) (VTerm f2 args2)
  | f1 == f2 && length args1 == length args2 = allEqual args1 args2
equal' _ _ = pure False

allEqual :: [Value] -> [Value] -> Chr Bool
allEqual [] [] = pure True
allEqual (a : as) (b : bs) = do
  ok <- equal a b
  if ok then allEqual as bs else pure False
allEqual _ _ = pure False

-- | Construct a compound term. Pure.
makeTerm :: Text -> [Value] -> Value
makeTerm = VTerm

-- | Check whether a value is a compound term with the given functor and arity.
-- Dereferences first.
matchTerm :: Value -> Text -> Int -> Chr Bool
matchTerm v functor arity = do
  d <- deref v
  case d of
    VTerm f args -> pure (f == functor && length args == arity)
    _ -> pure False

-- | Extract an argument from a compound term by 0-based index.
-- Dereferences first. Raises an error if the value is not a term
-- or the index is out of bounds.
getArg :: Value -> Int -> Chr Value
getArg v idx = do
  d <- deref v
  case d of
    VTerm _ args
      | idx >= 0 && idx < length args -> pure (args !! idx)
      | otherwise -> error $ "getArg: index " ++ show idx ++ " out of bounds"
    _ -> error "getArg: not a compound term"

-- | Register an observer on a logical variable. If the value is not
-- an unbound variable (after dereferencing), this is a no-op.
addObserver :: SuspensionId -> Value -> Chr ()
addObserver oid v = do
  d <- deref v
  case d of
    VVar var -> do
      st <- readVarState var
      case st of
        Unbound vid obs -> writeVarState var (Unbound vid (oid : obs))
        Bound {} -> pure ()
    _ -> pure ()

-- | Extract the 'VarId' of an unbound variable after dereferencing.
-- Returns 'Nothing' if the value is not an unbound variable.
getVarId :: Value -> Chr (Maybe VarId)
getVarId v = do
  d <- deref v
  case d of
    VVar var -> do
      st <- readVarState var
      case st of
        Unbound vid _ -> pure (Just vid)
        Bound {} -> pure Nothing
    _ -> pure Nothing
