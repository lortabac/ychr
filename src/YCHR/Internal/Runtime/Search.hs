{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | The search driver: @solve\/1@, @find_all\/2@, @fold_solutions\/4@
-- and @fail\/0@, the host calls behind @library(search)@ — and
-- @run_chr_session\/1@, which is 'hostSolve' made total.
--
-- See @docs\/reference\/search.md@ for the user-facing contract. This
-- module implements it.
--
-- == Variable sharing across a fork
--
-- Logical variables are 'Data.IORef.IORef' cells, so a variable
-- reachable from the goal is /the same variable/ inside the forked
-- session: bindings made there are visible to the caller once the
-- search commits. This is the result channel — pass fresh unbound
-- out-variables in the goal and read them afterwards.
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
-- and have the forked session bind its out-variables before
-- quiescence.
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
-- in an abandoned branch is never handed out again. That preserves
-- the property 'YCHR.Internal.Runtime.Monad.forkSearchSessionEnv'
-- documents, that a stale observer id can only ever miss, never
-- collide.
module YCHR.Internal.Runtime.Search
  ( searchHostCallRegistry,
    defaultHostCallRegistry,
  )
where

import Control.Exception (throwIO, try)
import Control.Monad.IO.Class (liftIO)
import Control.Monad.Trans.Reader (ask)
import Data.Foldable (toList)
import Data.IORef
import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IntMap
import Data.Map.Strict qualified as Map
import Data.Maybe (listToMaybe)
import Data.Sequence (Seq)
import Data.Sequence qualified as Seq
import Data.Set (Set)
import Data.Text qualified as T
import YCHR.Internal.Compile.Names (callFunProcName, runtimeName)
import YCHR.Internal.Meta (metaHostCallRegistry)
import YCHR.Internal.Pretty (prettyTerm)
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
  ( callProc,
    emitTrace,
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
    baseHostCallRegistry,
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
import YCHR.Internal.Runtime.Trace
  ( BacktrackReason (..),
    SearchOutcome (..),
    TraceEvent (..),
  )
import YCHR.Internal.Runtime.Trail (trailMark, unwindTo)
import YCHR.Internal.Runtime.Types
  ( CallVal (..),
    SuspensionId,
    TrailMark,
    Value (..),
  )
import YCHR.Internal.Runtime.Var (deref)
import YCHR.Internal.Types (ConstraintType (..))
import YCHR.Internal.Types qualified as Types
import YCHR.Internal.VM (Name (..), RuleId)

-- | Registry providing @solve\/1@, @find_all\/2@, @fold_solutions\/4@
-- and @fail\/0@, plus the @meta@ library's @run_chr_session\/1@,
-- which is the same driver. Part of 'defaultHostCallRegistry'; union
-- it in explicitly when assembling a custom registry that should
-- support @library(search)@ or @run_chr_session@.
searchHostCallRegistry :: HostCallRegistry
searchHostCallRegistry =
  Map.fromList
    [ (Name "solve", HostCallFn hostSolve),
      (Name "find_all", HostCallFn hostFindAll),
      (Name "fold_solutions", HostCallFn hostFoldSolutions),
      (Name "fail", HostCallFn hostFail),
      (Name "run_chr_session", HostCallFn hostRunChrSession)
    ]

-- | The default host-call registry — base builtins, the @meta@
-- library's host calls, and the search driver (which also provides
-- @run_chr_session@). This is what the @ychr@ CLI and the default
-- 'YCHR.Convert' / 'YCHR.DSL' entry points use. Defined here rather
-- than in "YCHR.Internal.Meta" because this is the topmost of the
-- component modules.
defaultHostCallRegistry :: HostCallRegistry
defaultHostCallRegistry =
  baseHostCallRegistry
    <> metaHostCallRegistry
    <> searchHostCallRegistry

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
        "fail/0 outside a search: no enclosing search entry point"
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
--
-- The scan cursor is deliberately /not/ in here: it is per branch, not
-- per search, so it is a parameter of 'searchFrom' instead.
data SearchCtx = SearchCtx
  { -- | The store index holding @search:alt@ constraints. Resolved
    -- once per search rather than per quiescence. 'Nothing' when the
    -- program never declares @alt\/1@, in which case the goal simply
    -- has no choice points and quiescence is a solution.
    altType :: !(Maybe ConstraintType),
    -- | Called at each solution, with the solution's bindings still
    -- live and nothing yet undone. Its answer decides whether the
    -- search goes on, and if not, what happens to those bindings.
    onSolution :: Chr SolutionStep
  }

-- | What a caller wants done at a solution. The three cases are the
-- three @step@ constructors of @library(search)@, and @solve\/1@ and
-- @find_all\/2@ are the constant functions @commit@ and @continue@.
data SolutionStep
  = -- | Ask for the next solution, backtracking out of this one.
    StepContinue
  | -- | End the search and unwind everything to the base mark.
    StepStop
  | -- | End the search and keep this solution's bindings.
    StepCommit

-- | 0-based position in a constraint type's store sequence. Those
-- sequences are append-only, and 'restoreStoreSnapshot' only ever puts
-- back a prefix of the current one, so an index names the same
-- suspension for as long as the driver holds it.
newtype StoreIndex = StoreIndex Int
  deriving (Show, Eq, Ord)

-- | The index one past a given one, where a subtree's scan begins.
afterIndex :: StoreIndex -> StoreIndex
afterIndex (StoreIndex i) = StoreIndex (i + 1)

-- | A choice point read out of the store: the @alt\/1@ suspension, its
-- position in that type's store sequence, and the alternative goals it
-- offers, in the order they will be tried.
data Choice = Choice
  { sid :: !SuspensionId,
    -- | Where 'findChoice' found it. Everything at a lower index is
    -- dead, which is what lets the subtree below this choice skip
    -- them; see 'findChoice'.
    index :: !StoreIndex,
    goals :: ![Value]
  }

-- | Explore from the current, quiescent state, looking for choice
-- points from @cursor@ onwards in the @alt@ type's store sequence.
--
-- 'AltDone' means 'onSolution' ended the search, one way or the
-- other. 'AltFailed' means
-- this subtree yielded no such end, and carries why — which the caller
-- reports and a nesting caller propagates, so the reason a trace shows
-- is the one that actually happened at the bottom rather than a
-- summary invented on the way up.
searchFrom :: SearchCtx -> StoreIndex -> Chr AltOutcome
searchFrom ctx cursor =
  findChoice ctx cursor >>= \case
    Nothing -> do
      emitTrace (pure TESolution)
      ctx.onSolution >>= \case
        StepContinue -> pure (AltFailed BRMoreWanted)
        StepStop -> pure (AltDone StopUndoing)
        StepCommit -> pure (AltDone StopKeeping)
    Just choice -> do
      emitTrace $ do
        gs <- snapshotValues choice.goals
        pure (TEChoice choice.sid gs)
      tryAlternatives ctx choice (zip [1 ..] choice.goals)

-- | How one alternative turned out.
data AltOutcome
  = -- | 'onSolution' ended the search inside this alternative, keeping
    -- the solution's bindings or discarding them. Nothing is undone
    -- here either way: undoing is the entry point's job, since a
    -- 'StepStop' unwinds past every choice point at once, to the base
    -- mark.
    --
    -- Running out of alternatives is 'AltFailed', not an outcome, so
    -- the payload is the two /stopping/ steps rather than a
    -- 'SearchOutcome' with an unreachable exhausted case.
    AltDone !StopKind
  | -- | The alternative did not end the search, for this reason. Its
    -- writes are still in place when this is returned; the caller
    -- undoes them.
    AltFailed !BacktrackReason

-- | The two ways 'onSolution' can end a search, and what each does to
-- the solution it ended on.
data StopKind
  = -- | @stop@: unwind to the base mark.
    StopUndoing
  | -- | @commit@: keep the bindings.
    StopKeeping

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
    -- Past this choice, not from the front: this one is killed just
    -- above, and everything before it is already dead — see
    -- 'findChoice' for why. Each alternative gets the same starting
    -- point, because 'restoreBranchState' puts the sequence back
    -- exactly as it was.
    searchFrom ctx (afterIndex choice.index)
  case outcome of
    AltDone o -> pure (AltDone o)
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

-- | The oldest alive choice point at or after @cursor@, or 'Nothing'
-- when the current state is a solution. Store sequences are
-- append-ordered, so \"oldest\" is just the first match.
--
-- Skipping the prefix is not an optimization the caller may get wrong.
-- The invariant is that at every quiescence in the subtree entered on
-- the choice at index @i@, every entry below @i + 1@ is dead: the ones
-- in @[cursor, i)@ because this scan read them dead, the ones below
-- @cursor@ by the same property one level up, and @i@ itself because
-- taking the choice kills it. Nothing in that subtree can revive one.
-- A suspension\'s @alive@ flag only goes back to 'True' by trail undo,
-- and every undo reachable from inside the subtree is to a mark taken
-- at or after it was entered. So the subtree may start at @i + 1@ —
-- which is what keeps a path of depth @k@ from rescanning @k@ dead
-- choice points at every quiescence.
--
-- A nested search forks a fresh store, so its sequence is its own and
-- so is its driver's cursor.
findChoice :: SearchCtx -> StoreIndex -> Chr (Maybe Choice)
findChoice ctx cursor@(StoreIndex from) = case ctx.altType of
  Nothing -> pure Nothing
  Just ct -> do
    susps <- getStoreSnapshot ct
    firstAlive cursor (toList (Seq.drop from susps))
  where
    firstAlive _ [] = pure Nothing
    firstAlive i (s : ss) = do
      alive <- isSuspAlive s
      case (alive, s.args) of
        (True, [goalsVal]) -> Just <$> readChoice s.suspId i goalsVal
        _ -> firstAlive (afterIndex i) ss

-- | Read @alt(Goals)@. An argument that is not a proper list is a
-- runtime error, not a failure: it is a malformed choice point rather
-- than a dead end.
readChoice :: SuspensionId -> StoreIndex -> Value -> Chr Choice
readChoice sid idx goalsVal =
  listElems goalsVal >>= \case
    Just goals ->
      pure (Choice {sid = sid, index = idx, goals = goals})
    Nothing ->
      runtimeErrorS
        "alt/1: argument must be a proper list of alternative goals"

-- | Resolve the store index that holds choice points, by inverting the
-- session's constraint-type names. 'Nothing' when the program never
-- declares @alt\/1@.
altTypeOf :: SessionEnv -> Maybe ConstraintType
altTypeOf env =
  listToMaybe
    [ ConstraintType i
    | (i, n) <- IntMap.toAscList env.storeTypeNames,
      n == altName
    ]

-- ---------------------------------------------------------------------------
-- Entry points
-- ---------------------------------------------------------------------------

-- | Resolve the goal, then drive it: 'runSearch' is 'driveSearch'
-- with the goal decoded in the /calling/ session, before the fork
-- exists, so an unknown goal constraint is a caller error and never a
-- failed branch.
runSearch :: String -> Value -> Chr SolutionStep -> Chr SearchOutcome
runSearch who goalArg onSolution = do
  goals <- goalConstraints who goalArg
  driveSearch who goals onSolution

-- | Fork a search session, tell the already-resolved goal, and drive
-- it.
--
-- Returns how the search ended. 'SearchCommitted' is the one outcome
-- that leaves the search's writes in place; on every other exit —
-- a @stop@ step, exhaustion, or an escaping runtime error — the search
-- is unwound to the mark taken here before returning or rethrowing. A
-- caller that catches the error ('hostRunChrSession', which turns it
-- into @false@) therefore resumes with the bindings it had, the way
-- ISO @catch\/3@ does.
--
-- Split from 'runSearch' so 'hostRunChrSession' can resolve the goal
-- outside the @try@ that swallows runtime errors.
driveSearch ::
  String ->
  [(Types.Name, [Value])] ->
  Chr SolutionStep ->
  Chr SearchOutcome
driveSearch who goals onSolution = do
  env <- ask
  sub <- liftIO (forkSearchSessionEnv env)
  let ctx =
        SearchCtx
          { altType = altTypeOf sub,
            onSolution = onSolution
          }
      label = T.pack who
      body = do
        emitTrace (pure (TESearchEnter label))
        outcome <- withoutFailure $ do
          mapM_ (uncurry tellResolvedConstraint) goals
          searchFrom ctx (StoreIndex 0)
        let exit = case outcome of
              AltDone StopKeeping -> SearchCommitted
              AltDone StopUndoing -> SearchStopped
              AltFailed _ -> SearchExhausted
        emitTrace (pure (TESearchExit label exit))
        pure exit
  liftIO $ do
    base <- runChr trailMark sub
    try (runChr body sub) >>= \case
      Left (e :: RuntimeErrorThrown) -> do
        runChr (unwindTo base) sub
        throwIO e
      Right SearchCommitted -> pure SearchCommitted
      Right exit -> do
        runChr (unwindTo base) sub
        pure exit

-- | @solve(Goal)@: run @Goal@ and stop at its first solution.
--
-- Commits: nothing is unwound, so bindings made to variables shared
-- with the goal are visible to the caller. @false@ when the space is
-- exhausted, with everything undone.
hostSolve :: [Value] -> Chr Value
hostSolve [goalArg] =
  VBool . (== SearchCommitted) <$> runSearch "solve" goalArg (pure StepCommit)
hostSolve _ = runtimeErrorS "solve: expected 1 argument"

-- | @run_chr_session(Goal)@: 'hostSolve' made total.
--
-- Same fork, same base mark, same commit-on-first-solution — the one
-- difference is that a runtime error escaping @Goal@ becomes @false@
-- instead of propagating. That makes this the language's only error
-- catcher, which is the whole reason it is a host call rather than
-- @run_chr_session(G) -> solve(G)@ in CHR.
--
-- Every @false@ is fully rolled back: 'driveSearch' unwinds to its
-- base mark before rethrowing an error and before reporting
-- exhaustion, so a failed sub-session leaves no half-made bindings
-- behind.
--
-- The cost of the one distinct behaviour is that @false@ does not
-- distinguish a bug in the goal from a deliberate failure. That was
-- already this call's contract, and it is bounded by the caller
-- getting a boolean it has to test — unlike search itself, where the
-- same conflation would silently turn a bug into a dead end.
--
-- Only 'RuntimeErrorThrown' is caught. A 'SearchFailure' — from
-- @search:fail\/0@ in the goal, or from an exhausted choice point —
-- never reaches here: 'withoutFailure' inside 'driveSearch' absorbs
-- it into 'SearchExhausted', which is @false@ by the same rule.
hostRunChrSession :: [Value] -> Chr Value
hostRunChrSession [goalArg] = do
  -- Resolved here rather than inside 'driveSearch', so that it happens
  -- outside the 'try' below: a misspelled or unexported goal
  -- constraint stays a loud caller error instead of being swallowed
  -- into a @false@ result.
  goals <- goalConstraints "run_chr_session" goalArg
  env <- ask
  let search = driveSearch "run_chr_session" goals (pure StepCommit)
  outcome <- liftIO (try (runChr search env))
  pure . VBool $ case outcome of
    Right SearchCommitted -> True
    Right _ -> False
    Left (_ :: RuntimeErrorThrown) -> False
hostRunChrSession _ = runtimeErrorS "run_chr_session: expected 1 argument"

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
        pure StepContinue
  _ <- runSearch "find_all" goalArg onSolution
  valueList . reverse <$> liftIO (readIORef acc)
hostFindAll _ = runtimeErrorS "find_all: expected 2 arguments"

-- | @fold_solutions(Template, Goal, F, Acc0)@: fold @F@ over the
-- solutions of @Goal@, in search order, with the fold in control of
-- when to stop.
--
-- At each solution @F@ is applied to a copy of @Template@ and the
-- accumulator, and answers with a @step@: @continue@ asks for the next
-- solution, @stop@ ends the search and undoes everything, @commit@
-- ends it and keeps the solution's bindings.
--
-- The accumulator lives in an 'IORef' the driver owns, so backtracking
-- does not roll it back: the trail covers variable cells and
-- suspension flags and nothing else.
--
-- That makes the /reference/ safe, not everything reachable through
-- it. @F@ can return a value that /points at/ a variable the branch
-- bound, and the accumulator is stored as it comes back. When the
-- branch is undone the cell reverts and the accumulator's contents
-- change underneath it. Copying here would fix that at @O(|acc|)@ per
-- solution, which is quadratic for the fold that accumulates a list
-- and would make this strictly slower than @find_all\/2@ at
-- @find_all@'s own job. So the witness is copied and the accumulator
-- is not, and the contract — carry the witness, or widen the template
-- or @copy_term@ anything else you take from the branch — is stated in
-- @docs\/reference\/search.md@ and in @libraries\/search.chr@.
hostFoldSolutions :: [Value] -> Chr Value
hostFoldSolutions [template, goalArg, f, acc0] = do
  accRef <- liftIO (newIORef acc0)
  let onSolution = do
        copied <- copyTerm template
        acc <- liftIO (readIORef accRef)
        -- A branch failure inside @F@ (@fail\/0@) escapes here as a
        -- 'SearchFailure' and is caught by the enclosing
        -- 'withoutFailure', which backtracks with the accumulator
        -- untouched — exactly a 'StepContinue'.
        result <- callProc (callFunProcName 2) [CVal f, CVal copied, CVal acc]
        (step, acc') <- readStep result
        liftIO (writeIORef accRef acc')
        pure step
  _ <- runSearch "fold_solutions" goalArg onSolution
  liftIO (readIORef accRef)
hostFoldSolutions _ = runtimeErrorS "fold_solutions: expected 4 arguments"

-- | Read the @step(A)@ a fold's step function returned, as the
-- driver's own decision plus the new accumulator. Anything else is a
-- runtime error: a fold whose step function answers with a bare value
-- has no way to say what to do next.
readStep :: Value -> Chr (SolutionStep, Value)
readStep v =
  deref v >>= \case
    VTerm functor [acc]
      | functor == stepContinue -> pure (StepContinue, acc)
      | functor == stepStop -> pure (StepStop, acc)
      | functor == stepCommit -> pure (StepCommit, acc)
    other -> do
      t <- snapshotValue other
      runtimeErrorS
        ( "fold_solutions: the step function must return continue/1,"
            ++ " stop/1 or commit/1, got "
            ++ prettyTerm t
        )

-- | The functors of @library(search)@'s @step(A)@ constructors, in the
-- mangled form a 'MakeTerm' produces for a module-qualified name.
-- Built through 'runtimeName' rather than spelled out, so they follow
-- the encoding rather than restating it.
stepContinue, stepStop, stepCommit :: T.Text
stepContinue = stepCtor "continue"
stepStop = stepCtor "stop"
stepCommit = stepCtor "commit"

stepCtor :: T.Text -> T.Text
stepCtor = runtimeName . Types.Qualified searchModule

-- | The module @step(A)@ is declared in. Wired in, like
-- 'YCHR.Internal.Runtime.Goal.altName' and for the same provisional
-- reason: the runtime has no way yet for a library to nominate a name
-- to it.
searchModule :: T.Text
searchModule = "search"
