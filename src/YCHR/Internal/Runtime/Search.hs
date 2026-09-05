{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | The search driver: @solve\/1@, @find_all\/2@ and @fail\/0@, the
-- host calls behind @library(search)@.
--
-- See @docs\/reference\/search.md@ for the user-facing contract. This
-- module implements it.
--
-- == Choice at quiescence
--
-- Search here is /labeling/, not continuation capture. @alt\/1@ is an
-- ordinary CHR constraint with no rules, so telling it just leaves it
-- in the store. The driver forks a session, tells the goal, and runs
-- it to quiescence under the ordinary refined semantics; at quiescence
-- it looks for an alive @search:alt@ suspension. None means the state
-- is a solution. Otherwise it takes the oldest one and, for each
-- alternative in turn, kills the choice, tells that alternative's
-- goal, and recurses.
--
-- Each alternative is a /goal/, not a value: the choice is between
-- computations. Binding a variable is one computation among others,
-- which is why @choose\/2@ is library CHR over @alt@ and @try_unify@
-- rather than a second thing the runtime knows about.
--
-- Nothing needs to be captured because the continuation after a choice
-- is always "tell this goal and propagate to quiescence", which the
-- driver invokes itself. That is what keeps the 'Chr' monad, the
-- interpreter and the VM untouched by this feature.
--
-- == Undo
--
-- Two mechanisms, split by what a session reference actually holds:
--
--   * The store, the suspension map, the propagation history and the
--     reactivation queue are single references over /persistent/
--     structures, so a 'StoreSnapshot' is four pointer reads and
--     restoring it is four pointer writes, whatever the store
--     contains.
--   * Variable cells and suspension flags are individual references,
--     reachable only by walking and shared across forks besides.
--     Those go on the trail ("YCHR.Internal.Runtime.Trail"), recorded
--     at the write itself.
--
-- The variable and suspension-id counters are deliberately /not/ part
-- of either: they stay monotonic across backtracking, so an id burned
-- in an abandoned branch is never handed out again. That preserves the
-- property 'YCHR.Internal.Runtime.Monad.forkSessionEnv' documents,
-- that a stale observer id can only ever miss, never collide.
module YCHR.Internal.Runtime.Search (searchHostCallRegistry) where

import Control.Exception (throwIO, try)
import Control.Monad.IO.Class (liftIO)
import Control.Monad.Trans.Reader (ask)
import Data.Foldable (toList)
import Data.IORef
import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IntMap
import Data.Map.Strict qualified as Map
import Data.Sequence (Seq)
import Data.Set (Set)
import Data.Text qualified as T
import YCHR.Internal.Runtime.Error
  ( RuntimeErrorThrown,
    SearchFailure (..),
    runtimeErrorS,
  )
import YCHR.Internal.Runtime.Goal
  ( altGoalConstraints,
    altName,
    goalConstraints,
    listElems,
  )
import YCHR.Internal.Runtime.Interpreter
  ( emitTrace,
    snapshotValue,
    snapshotValues,
  )
import YCHR.Internal.Runtime.Monad
  ( CallStack,
    Chr,
    SessionEnv (..),
    forkSearchSessionEnv,
    runChr,
  )
import YCHR.Internal.Runtime.Registry
  ( HostCallFn (..),
    HostCallRegistry,
    copyTerm,
    valueList,
  )
import YCHR.Internal.Runtime.Session (tellResolvedConstraint)
import YCHR.Internal.Runtime.Store
  ( Suspension (..),
    getStoreSnapshot,
    isSuspAlive,
    killConstraint,
  )
import YCHR.Internal.Runtime.Trace (BacktrackReason (..), TraceEvent (..))
import YCHR.Internal.Runtime.Trail (trailMark, unwindTo)
import YCHR.Internal.Runtime.Types
  ( SuspensionId,
    TrailMark,
    Value (..),
  )
import YCHR.Internal.Types (ConstraintType (..))
import YCHR.Internal.VM (Name (..), RuleId)

-- | Registry providing @solve\/1@, @find_all\/2@ and @fail\/0@. Part
-- of 'YCHR.Internal.Runtime.SubSession.defaultHostCallRegistry'; union
-- it in explicitly when assembling a custom registry that should
-- support @library(search)@.
searchHostCallRegistry :: HostCallRegistry
searchHostCallRegistry =
  Map.fromList
    [ (Name "solve", HostCallFn hostSolve),
      (Name "find_all", HostCallFn hostFindAll),
      (Name "fail", HostCallFn hostFail)
    ]

-- ---------------------------------------------------------------------------
-- Failure
-- ---------------------------------------------------------------------------

-- | @fail()@: abandon the current branch.
--
-- The trail doubles as the "is a search running?" flag, since
-- 'forkSearchSessionEnv' installs it and nothing else does. Outside a
-- search there is no branch to fail, so this is a loud runtime error
-- rather than a silent success or a stuck query.
hostFail :: [Value] -> Chr Value
hostFail [] = do
  env <- ask
  case env.trail of
    Nothing ->
      runtimeErrorS
        "fail/0 outside a search: no enclosing solve/1 or find_all/2"
    Just _ -> liftIO (throwIO SearchFailure)
hostFail _ = runtimeErrorS "fail: expected 0 arguments"

-- ---------------------------------------------------------------------------
-- Snapshots
-- ---------------------------------------------------------------------------

-- | The four session references a branch may change and whose undo is
-- a pointer write, captured at a choice point.
data StoreSnapshot = StoreSnapshot
  { byType :: !(IntMap (Seq Suspension)),
    byId :: !(IntMap Suspension),
    history :: !(Set (RuleId, [SuspensionId])),
    queue :: !(Seq SuspensionId)
  }

takeStoreSnapshot :: Chr StoreSnapshot
takeStoreSnapshot = do
  env <- ask
  liftIO $
    StoreSnapshot
      <$> readIORef env.storeByType
      <*> readIORef env.storeById
      <*> readIORef env.history
      <*> readIORef env.reactQueue

restoreStoreSnapshot :: StoreSnapshot -> Chr ()
restoreStoreSnapshot snap = do
  env <- ask
  liftIO $ do
    writeIORef env.storeByType snap.byType
    writeIORef env.storeById snap.byId
    writeIORef env.history snap.history
    writeIORef env.reactQueue snap.queue

-- | Everything a failed branch has to put back. The call stack is in
-- here for the same reason
-- 'YCHR.Internal.Runtime.Interpreter.catchInstantiation' restores it:
-- a throw leaves the frames it pushed behind, and this is a catch that
-- resumes in the same session.
data BranchState = BranchState
  { mark :: !TrailMark,
    store :: !StoreSnapshot,
    stack :: !CallStack
  }

saveBranchState :: Chr BranchState
saveBranchState = do
  env <- ask
  BranchState
    <$> trailMark
    <*> takeStoreSnapshot
    <*> liftIO (readIORef env.callStack)

restoreBranchState :: BranchState -> Chr ()
restoreBranchState st = do
  env <- ask
  liftIO (writeIORef env.callStack st.stack)
  restoreStoreSnapshot st.store
  unwindTo st.mark

-- ---------------------------------------------------------------------------
-- The driver
-- ---------------------------------------------------------------------------

-- | What the driver needs at every level of the recursion.
data SearchCtx = SearchCtx
  { -- | Store indices holding @search:alt@ constraints. Resolved
    -- once per search rather than per quiescence. Empty when the
    -- program never declares @alt\/1@, in which case the goal simply
    -- has no choice points and quiescence is a solution.
    altTypes :: ![ConstraintType],
    -- | Called at each solution. 'True' stops the search and commits
    -- the current bindings; 'False' asks for the next solution, which
    -- backtracks out of this one.
    onSolution :: Chr Bool
  }

-- | A choice point read out of the store: the @alt\/1@ suspension and
-- the alternative goals it offers, in the order they will be tried.
data Choice = Choice
  { sid :: !SuspensionId,
    goals :: ![Value]
  }

-- | Explore from the current, quiescent state.
--
-- 'AltStopped' means 'onSolution' stopped the search: committed,
-- nothing unwound. 'AltFailed' means this subtree yielded no stop, and
-- carries why — which the caller reports and a nesting caller
-- propagates, so the reason a trace shows is the one that actually
-- happened at the bottom rather than a summary invented on the way up.
searchFrom :: SearchCtx -> Chr AltOutcome
searchFrom ctx =
  findChoice ctx >>= \case
    Nothing -> do
      emitTrace (pure TESolution)
      stop <- ctx.onSolution
      pure (if stop then AltStopped else AltFailed BRMoreWanted)
    Just choice -> do
      emitTrace $ do
        gs <- snapshotValues choice.goals
        pure (TEChoice choice.sid gs)
      tryAlternatives ctx choice (zip [1 ..] choice.goals)

-- | How one alternative turned out.
data AltOutcome
  = -- | 'onSolution' stopped the search inside this alternative.
    -- Nothing is undone.
    AltStopped
  | -- | The alternative did not lead to a stop, for this reason. Its
    -- writes are still in place when this is returned; the caller
    -- undoes them.
    AltFailed !BacktrackReason

-- | Try each alternative of one choice point in list order, undoing
-- the branch between attempts. Exhausting them fails the choice point,
-- which fails whatever branch contains it.
tryAlternatives :: SearchCtx -> Choice -> [(Int, Value)] -> Chr AltOutcome
tryAlternatives _ _ [] = pure (AltFailed BRExhausted)
tryAlternatives ctx choice ((altNum, goal) : rest) = do
  saved <- saveBranchState
  emitTrace $ do
    g <- snapshotValue goal
    pure (TETryAlt altNum (length choice.goals) g)
  outcome <- withoutFailure $ do
    -- Taking the choice consumes it: an alternative must not
    -- rediscover its own choice point and recurse forever. The kill is
    -- trailed like any other flag write, so the constraint is alive
    -- again if this alternative is abandoned.
    killConstraint choice.sid
    -- Resolved here, inside the branch, and without the export check:
    -- a lifted disjunct is a module-internal constraint, so the check
    -- that guards a caller-supplied goal would reject exactly the
    -- goals the compiler generated. A name that resolves to nothing is
    -- still a runtime error and escapes the search — 'withoutFailure'
    -- catches 'SearchFailure' and nothing else.
    tells <- altGoalConstraints "alt" goal
    mapM_ (uncurry tellResolvedConstraint) tells
    searchFrom ctx
  case outcome of
    AltStopped -> pure AltStopped
    AltFailed reason -> do
      restoreBranchState saved
      -- Emitted after the undo, so the event means what it says: by
      -- the time a reader sees it, the bindings, store, history and
      -- queue are back to what they were at the choice point.
      emitTrace (pure (TEBacktrack reason))
      tryAlternatives ctx choice rest

-- | Run a branch, mapping a branch failure to an outcome. Runtime
-- errors are left alone: they are not failures and must escape the
-- search.
withoutFailure :: Chr AltOutcome -> Chr AltOutcome
withoutFailure act = do
  env <- ask
  liftIO (try (runChr act env)) >>= \case
    Right o -> pure o
    Left SearchFailure -> pure (AltFailed BRFail)

-- | The oldest alive choice point in the store, or 'Nothing' when the
-- current state is a solution. Store sequences are append-ordered, so
-- \"oldest\" is just the first match.
findChoice :: SearchCtx -> Chr (Maybe Choice)
findChoice ctx = go ctx.altTypes
  where
    go [] = pure Nothing
    go (ct : cts) =
      getStoreSnapshot ct >>= firstAlive . toList >>= \case
        Just c -> pure (Just c)
        Nothing -> go cts

    firstAlive [] = pure Nothing
    firstAlive (s : ss) = do
      alive <- isSuspAlive s
      case (alive, s.args) of
        (True, [goalsVal]) -> Just <$> readChoice s.suspId goalsVal
        _ -> firstAlive ss

-- | Read @alt(Goals)@. An argument that is not a proper list is a
-- runtime error, not a failure: it is a malformed choice point rather
-- than a dead end.
readChoice :: SuspensionId -> Value -> Chr Choice
readChoice sid goalsVal =
  listElems goalsVal >>= \case
    Just goals ->
      pure (Choice {sid = sid, goals = goals})
    Nothing ->
      runtimeErrorS
        "alt/1: argument must be a proper list of alternative goals"

-- | Resolve the store indices that hold choice points, by inverting
-- the session's constraint-type names.
altTypesOf :: SessionEnv -> [ConstraintType]
altTypesOf env =
  [ ConstraintType i
  | (i, n) <- IntMap.toAscList env.storeTypeNames,
    n == altName
  ]

-- ---------------------------------------------------------------------------
-- Entry points
-- ---------------------------------------------------------------------------

-- | Fork a search session, tell the goal, and drive it.
--
-- Returns whether 'onSolution' stopped the search. On every other
-- exit — exhaustion or an escaping runtime error — the search is
-- unwound to the mark taken here before returning or rethrowing. A
-- caller that catches the error (an enclosing @run_chr_session@, which
-- turns it into @false@) therefore resumes with the bindings it had,
-- the way ISO @catch\/3@ does.
runSearch :: String -> Value -> Chr Bool -> Chr Bool
runSearch who goalArg onSolution = do
  -- Resolved in the *calling* session, before the fork exists, so an
  -- unknown goal constraint is a caller error and never a failed
  -- branch.
  goals <- goalConstraints who goalArg
  env <- ask
  sub <- liftIO (forkSearchSessionEnv env)
  let ctx =
        SearchCtx
          { altTypes = altTypesOf sub,
            onSolution = onSolution
          }
      label = T.pack who
      body = do
        emitTrace (pure (TESearchEnter label))
        outcome <- withoutFailure $ do
          mapM_ (uncurry tellResolvedConstraint) goals
          searchFrom ctx
        let committed = case outcome of
              AltStopped -> True
              AltFailed _ -> False
        emitTrace (pure (TESearchExit label committed))
        pure committed
  liftIO $ do
    base <- runChr trailMark sub
    try (runChr body sub) >>= \case
      Left (e :: RuntimeErrorThrown) -> do
        runChr (unwindTo base) sub
        throwIO e
      Right True -> pure True
      Right False -> do
        runChr (unwindTo base) sub
        pure False

-- | @solve(Goal)@: run @Goal@ and stop at its first solution.
--
-- Commits: nothing is unwound, so bindings made to variables shared
-- with the goal are visible to the caller. @false@ when the space is
-- exhausted, with everything undone.
hostSolve :: [Value] -> Chr Value
hostSolve [goalArg] = VBool <$> runSearch "solve" goalArg (pure True)
hostSolve _ = runtimeErrorS "solve: expected 1 argument"

-- | @find_all(Template, Goal)@: every solution of @Goal@, as a list of
-- copies of @Template@ in search order.
--
-- The copies are what survive: the search is fully unwound afterwards,
-- so no binding it made is visible to the caller. Accumulating into an
-- 'IORef' is safe across backtracking precisely because the trail
-- covers variable cells and suspension flags and nothing else — an
-- ordinary reference the driver owns is not rolled back.
hostFindAll :: [Value] -> Chr Value
hostFindAll [template, goalArg] = do
  acc <- liftIO (newIORef [])
  let onSolution = do
        copied <- copyTerm template
        liftIO (modifyIORef' acc (copied :))
        -- Never stop: asking for the next solution backtracks out of
        -- this one.
        pure False
  _ <- runSearch "find_all" goalArg onSolution
  valueList . reverse <$> liftIO (readIORef acc)
hostFindAll _ = runtimeErrorS "find_all: expected 2 arguments"
