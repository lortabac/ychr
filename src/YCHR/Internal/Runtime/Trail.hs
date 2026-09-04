{-# LANGUAGE OverloadedRecordDot #-}

-- | The search undo trail: recording writes, marking a position, and
-- unwinding back to one.
--
-- Search backtracking is snapshot plus trail. The snapshot half lives
-- in "YCHR.Internal.Runtime.Search" and covers the session references
-- that hold persistent structures (store, history, reactivation
-- queue), for which undo is a pointer write. This module is the other
-- half: the individual mutable cells a snapshot cannot reach —
-- logical-variable cells and the @alive@ \/ @stored@ flags on
-- suspensions — which are recorded write-by-write and replayed in
-- reverse.
--
-- The recording hooks sit at the two choke points that own those
-- cells, 'YCHR.Internal.Runtime.Var.writeVarState' and the flag
-- writes in "YCHR.Internal.Runtime.Store", so no caller has to
-- remember to trail anything. When no search is active
-- ('SessionEnv.trail' is 'Nothing') every hook is a field read and a
-- 'case'.
--
-- Note that 'YCHR.Internal.Runtime.Var.deref' writes through
-- 'writeVarState' too, so path compression is trailed. That is not
-- merely harmless, it is necessary: a cell compressed to point /past/
-- a variable the branch bound has to be restored alongside that
-- variable, or unwinding leaves it pointing at a value the branch was
-- supposed to have taken back.
--
-- 'YCHR.Internal.Runtime.Var.unifiable' is the one deliberate
-- exception. It reverts its own hypothetical writes from a private
-- micro-trail before returning, so they must not reach the shared one;
-- its walk uses a non-compressing deref precisely so that the private
-- trail is its only writer.
module YCHR.Internal.Runtime.Trail
  ( -- * Recording
    recordVarWrite,
    recordFlagWrite,

    -- * Marking and unwinding
    trailMark,
    unwindTo,
  )
where

import Control.Monad.IO.Class (liftIO)
import Control.Monad.Trans.Reader (ask)
import Data.IORef
import YCHR.Internal.Runtime.Monad (Chr, SessionEnv (..))
import YCHR.Internal.Runtime.Types
  ( Trail (..),
    TrailEntry (..),
    TrailMark (..),
    TrailState (..),
    Var (..),
  )

-- | Record the current contents of a variable cell, immediately
-- before it is overwritten. A no-op when no search is active.
--
-- Reading the old state is deferred into the 'Just' branch: an
-- untrailed session pays a field read and a branch, not an extra
-- 'readIORef' on every variable write.
recordVarWrite :: Var -> Chr ()
recordVarWrite var@(Var ref) = do
  env <- ask
  case env.trail of
    Nothing -> pure ()
    Just t -> liftIO $ do
      old <- readIORef ref
      push t (TrailVar var old)
{-# INLINE recordVarWrite #-}

-- | Record the current value of a suspension flag, immediately before
-- it is overwritten. A no-op when no search is active.
recordFlagWrite :: IORef Bool -> Chr ()
recordFlagWrite ref = do
  env <- ask
  case env.trail of
    Nothing -> pure ()
    Just t -> liftIO $ do
      old <- readIORef ref
      push t (TrailFlag ref old)
{-# INLINE recordFlagWrite #-}

push :: Trail -> TrailEntry -> IO ()
push (Trail ref) e =
  modifyIORef' ref $ \st ->
    TrailState
      { entries = e : st.entries,
        length = st.length + 1
      }

-- | The current trail position. 'TrailMark' @0@ when no search is
-- active, which makes 'unwindTo' a no-op — the honest answer, since
-- there is then nothing recorded to undo.
trailMark :: Chr TrailMark
trailMark = do
  env <- ask
  case env.trail of
    Nothing -> pure (TrailMark 0)
    Just (Trail ref) -> liftIO (TrailMark . (.length) <$> readIORef ref)

-- | Undo every write recorded since @mark@, newest first, and drop
-- those entries.
--
-- Restoring is idempotent in the sense that matters: replaying an
-- entry writes back a value the cell provably held at that point in
-- the run, and entries are replayed in the exact reverse of the order
-- they were made, so a cell written several times inside the branch
-- ends up holding the value it had at the mark.
--
-- Unwinding past @mark@ is impossible by construction — marks are
-- taken by nested drivers in increasing order and unwound to in
-- decreasing order — but a mark beyond the current length is treated
-- as "nothing to do" rather than an error.
unwindTo :: TrailMark -> Chr ()
unwindTo (TrailMark mark) = do
  env <- ask
  case env.trail of
    Nothing -> pure ()
    Just (Trail ref) -> liftIO $ do
      st <- readIORef ref
      let n = st.length - mark
      if n <= 0
        then pure ()
        else do
          let (undo, kept) = splitAt n st.entries
          mapM_ replay undo
          writeIORef ref (TrailState {entries = kept, length = mark})

replay :: TrailEntry -> IO ()
replay (TrailVar (Var ref) st) = writeIORef ref st
replay (TrailFlag ref b) = writeIORef ref b
