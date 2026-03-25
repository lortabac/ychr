{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}

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

    -- * Unify effect
    Unify,
    runUnify,

    -- * Operations
    newVar,
    deref,
    unify,
    equal,
    makeTerm,
    matchTerm,
    getArg,
    addObserver,
    getVarId,
  )
where

import Data.IORef
import Data.Text (Text)
import Effectful
import Effectful.Dispatch.Static
import Effectful.Writer.Static.Local (Writer, tell)
import YCHR.Runtime.Types (SuspensionId (..), Value (..), Var (..), VarId (..), VarState (..))

-- ---------------------------------------------------------------------------
-- Unify effect
-- ---------------------------------------------------------------------------

data Unify :: Effect

type instance DispatchOf Unify = Static WithSideEffects

newtype instance StaticRep Unify = UnifyRep (IORef VarId)

-- | Run a computation that uses 'Unify'. Requires 'IOE' only at the
-- runner level; individual operations do not need it.
runUnify :: (IOE :> es) => Eff (Unify : es) a -> Eff es a
runUnify m = do
  counter <- liftIO $ newIORef (VarId 0)
  evalStaticRep (UnifyRep counter) m

-- ---------------------------------------------------------------------------
-- Internal Unify primitives
-- ---------------------------------------------------------------------------

readVarState :: (Unify :> es) => Var -> Eff es VarState
readVarState (Var ref) = unsafeEff_ $ readIORef ref

writeVarState :: (Unify :> es) => Var -> VarState -> Eff es ()
writeVarState (Var ref) st = unsafeEff_ $ writeIORef ref st

newVarRef :: (Unify :> es) => VarState -> Eff es Var
newVarRef st = unsafeEff_ $ Var <$> newIORef st

freshVarId :: (Unify :> es) => Eff es VarId
freshVarId = do
  UnifyRep counter <- getStaticRep
  unsafeEff_ $ do
    vid@(VarId n) <- readIORef counter
    writeIORef counter (VarId (n + 1))
    pure vid

-- ---------------------------------------------------------------------------
-- Operations
-- ---------------------------------------------------------------------------

-- | Create a fresh unbound logical variable.
newVar :: (Unify :> es) => Eff es Value
newVar = do
  vid <- freshVarId
  v <- newVarRef (Unbound vid [])
  pure (VVar v)

-- | Follow binding chains to find the ultimate value, applying
-- path compression along the way. If the result is an unbound
-- variable, returns the 'VVar' wrapping it.
deref :: (Unify :> es) => Value -> Eff es Value
deref val@(VVar var@(Var ref)) = do
  st <- readVarState var
  case st of
    Unbound {} -> pure val
    Bound v -> do
      v' <- deref v
      -- Path compression: point directly to the end of the chain.
      case v' of
        VVar (Var ref')
          | ref == ref' -> pure () -- already pointing to itself
        _ -> writeVarState var (Bound v')
      pure v'
deref val = pure val

-- | Unify two values (tell semantics, Prolog @=@).
--
-- Returns whether unification succeeded. Observer IDs from bound
-- variables are emitted via the 'Writer' effect. The caller is
-- responsible for reactivating the constraints identified by those
-- observer IDs.
unify :: (Writer [SuspensionId] :> es, Unify :> es) => Value -> Value -> Eff es Bool
unify v1 v2 = do
  d1 <- deref v1
  d2 <- deref v2
  unify' d1 d2

unify' :: (Writer [SuspensionId] :> es, Unify :> es) => Value -> Value -> Eff es Bool
-- Wildcard: unifies with anything without binding
unify' VWildcard _ = pure True
unify' _ VWildcard = pure True
-- Var-Var, same variable
unify' (VVar (Var ref1)) (VVar (Var ref2))
  | ref1 == ref2 = pure True
-- Var-Var, different variables: bind first to second, merge observers
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
          tell obs1
          pure True
        Bound {} -> error "unify': unexpected Bound after deref"
-- Var-NonVar: bind var to value
unify' (VVar var) v = do
  st <- readVarState var
  case st of
    Bound {} -> error "unify': unexpected Bound after deref"
    Unbound _ obs -> do
      writeVarState var (Bound v)
      tell obs
      pure True
-- NonVar-Var: symmetric
unify' v (VVar vr) = unify' (VVar vr) v
-- Int-Int
unify' (VInt a) (VInt b) = pure (a == b)
-- Atom-Atom
unify' (VAtom a) (VAtom b) = pure (a == b)
-- Bool-Bool
unify' (VBool a) (VBool b) = pure (a == b)
-- Term-Term: same functor and arity, unify args pairwise
unify' (VTerm f1 args1) (VTerm f2 args2)
  | f1 == f2 && length args1 == length args2 = unifyArgs args1 args2
-- Everything else fails
unify' _ _ = pure False

-- | Unify argument lists pairwise.
-- Short-circuits on the first failure.
unifyArgs :: (Writer [SuspensionId] :> es, Unify :> es) => [Value] -> [Value] -> Eff es Bool
unifyArgs [] [] = pure True
unifyArgs (a : as) (b : bs) = do
  ok <- unify a b
  if ok
    then unifyArgs as bs
    else pure False
unifyArgs _ _ = pure False -- arity mismatch (shouldn't happen)

-- | Check equality of two values (ask semantics, Prolog @==@).
--
-- No mutation beyond path compression during dereferencing.
-- Two distinct unbound variables are /not/ equal.
equal :: (Unify :> es) => Value -> Value -> Eff es Bool
equal v1 v2 = do
  d1 <- deref v1
  d2 <- deref v2
  equal' d1 d2

equal' :: (Unify :> es) => Value -> Value -> Eff es Bool
-- Var-Var: equal iff same underlying ref (same VarId)
equal' (VVar (Var ref1)) (VVar (Var ref2)) = pure (ref1 == ref2)
-- Var-NonVar or NonVar-Var: not equal
equal' (VVar _) _ = pure False
equal' _ (VVar _) = pure False
-- Ground-Ground
equal' (VInt a) (VInt b) = pure (a == b)
equal' (VAtom a) (VAtom b) = pure (a == b)
equal' (VBool a) (VBool b) = pure (a == b)
-- Term-Term: same functor, same arity, all args recursively equal
equal' (VTerm f1 args1) (VTerm f2 args2)
  | f1 == f2 && length args1 == length args2 = allEqual args1 args2
equal' _ _ = pure False

-- | Check pairwise equality of argument lists. Short-circuits on first mismatch.
allEqual :: (Unify :> es) => [Value] -> [Value] -> Eff es Bool
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
matchTerm :: (Unify :> es) => Value -> Text -> Int -> Eff es Bool
matchTerm v functor arity = do
  d <- deref v
  case d of
    VTerm f args -> pure (f == functor && length args == arity)
    _ -> pure False

-- | Extract an argument from a compound term by 0-based index.
-- Dereferences first. Raises an error if the value is not a term
-- or the index is out of bounds.
getArg :: (Unify :> es) => Value -> Int -> Eff es Value
getArg v idx = do
  d <- deref v
  case d of
    VTerm _ args
      | idx >= 0 && idx < length args -> pure (args !! idx)
      | otherwise -> error $ "getArg: index " ++ show idx ++ " out of bounds"
    _ -> error "getArg: not a compound term"

-- | Register an observer on a logical variable. If the value is not
-- an unbound variable (after dereferencing), this is a no-op.
addObserver :: (Unify :> es) => SuspensionId -> Value -> Eff es ()
addObserver oid v = do
  d <- deref v
  case d of
    VVar var -> do
      st <- readVarState var
      case st of
        Unbound vid obs -> writeVarState var (Unbound vid (oid : obs))
        Bound {} -> pure () -- already bound, no-op
    _ -> pure ()

-- | Extract the 'VarId' of an unbound variable after dereferencing.
-- Returns 'Nothing' if the value is not an unbound variable.
getVarId :: (Unify :> es) => Value -> Eff es (Maybe VarId)
getVarId v = do
  d <- deref v
  case d of
    VVar var -> do
      st <- readVarState var
      case st of
        Unbound vid _ -> pure (Just vid)
        Bound {} -> pure Nothing -- shouldn't happen after deref
    _ -> pure Nothing
