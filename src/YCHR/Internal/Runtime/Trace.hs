{-# LANGUAGE OverloadedStrings #-}

-- | Tracing events for the Haskell interpreter.
--
-- The interpreter emits a 'TraceEvent' at each canonical point of the
-- refined operational semantics (ωr): activation of a constraint,
-- entry into an occurrence procedure, partner match, history hit,
-- rule fire, store, kill, reactivation, unification. It also emits
-- events for function calls, lambda calls, and host calls so the
-- whole picture — not just the CHR scheduling — is visible.
--
-- The search driver ("YCHR.Internal.Runtime.Search") emits its own
-- six: entering and leaving a search, selecting a choice point,
-- trying an alternative, reaching a solution, and backtracking. Without them a trace of a
-- search reads as a @kill@ followed by an unexplained @reactivate@ of
-- the same constraint, with nothing to say the branch in between was
-- abandoned and its state rolled back.
--
-- 'SessionEnv' carries a @Maybe (TraceEvent -> IO ())@ handler; when
-- @Nothing@, the cost of tracing is a single pointer test inside the
-- interpreter's emission helper. The REPL's @:trace@ command installs
-- 'defaultTraceHandler' for the duration of one query.
module YCHR.Internal.Runtime.Trace
  ( -- * Events
    TraceEvent (..),
    BacktrackReason (..),
    SearchOutcome (..),

    -- * Handlers
    TraceHandler,
    defaultTraceHandler,

    -- * Rendering
    formatEvent,
  )
where

import Data.List (intercalate)
import Data.Text (Text)
import Data.Text qualified as T
import System.IO (Handle, hPutStrLn)
import YCHR.Internal.Pretty (prettyTerm)
import YCHR.Internal.Runtime.Types (SuspensionId (..))
import YCHR.Internal.Types (Term)

-- | Signature of a trace handler. Takes the current indentation depth
-- (managed by the interpreter) plus the event, and runs whatever
-- side-effect the consumer wants (typically formatting and writing to
-- a handle, but tests can capture events instead).
type TraceHandler = Int -> TraceEvent -> IO ()

-- | A single observable event during interpretation. The interpreter
-- constructs these only when tracing is on; pretty-printing lives in
-- the handler so different consumers can render differently.
data TraceEvent
  = -- | Entering @tell_c@. Carries the constraint type name and the
    -- (already-dereferenced) argument terms.
    TETell {ctype :: !Text, args :: ![Term]}
  | -- | Entering @activate_c@.
    TEActivate {ctype :: !Text, sid :: !SuspensionId, args :: ![Term]}
  | -- | Entering @occurrence_c_j@.
    TETryOccurrence {ctype :: !Text, occNum :: !Int, ruleName :: !Text}
  | -- | Partner constraint matched in a 'Foreach'.
    TEPartner {ctype :: !Text, sid :: !SuspensionId, args :: ![Term]}
  | -- | Propagation history rejected the candidate combination.
    TEHistoryHit {ruleName :: !Text, sids :: ![SuspensionId]}
  | -- | Rule fires. Emitted at 'AddHistory' for propagation rules;
    -- simplification rules without history also reach a unique
    -- @kill@/@store@ sequence so the absence is visible via depth.
    TEFire {ruleName :: !Text, sids :: ![SuspensionId]}
  | -- | A constraint is added to the store.
    TEStore {sid :: !SuspensionId, ctype :: !Text, args :: ![Term]}
  | -- | A constraint is removed from the store.
    TEKill {sid :: !SuspensionId}
  | -- | A constraint is being reactivated from the queue.
    TEReactivate {sid :: !SuspensionId, ctype :: !Text, args :: ![Term]}
  | -- | A successful 'BUnify'. Carries the two operand terms (as they
    -- looked before the unify) and the number of constraints that
    -- the runtime enqueued for reactivation as a result.
    TEUnify {lhs :: !Term, rhs :: !Term, reactivated :: !Int}
  | -- | Call into a user-defined function (or lifted lambda). For
    -- lambdas, @fname@ contains the synthesised @module:__lambda_N@
    -- name; the formatter renders these as @lambda#N@.
    TECallFunction {fname :: !Text, args :: ![Term]}
  | -- | Function or lambda returned the given value.
    TEReturn {value :: !Term}
  | -- | A host-language call (arithmetic, comparisons, prelude
    -- primitives, etc.). Emitted once per call with both inputs and
    -- result.
    TECallHost {hname :: !Text, args :: ![Term], result :: !Term}
  | -- | Entering a search ('YCHR.Internal.Runtime.Search'). @sname@ is
    -- the driving host call: @solve@, @find_all@ or @fold_solutions@.
    TESearchEnter {sname :: !Text}
  | -- | A choice point was selected at quiescence: the @alt\/1@
    -- suspension the driver took, and the alternative goals in the
    -- order they will be tried.
    TEChoice {sid :: !SuspensionId, alts :: ![Term]}
  | -- | Trying one alternative of the current choice point. @altNum@
    -- is 1-based, @altCount@ the total, and @goal@ the goal about to
    -- be told.
    TETryAlt {altNum :: !Int, altCount :: !Int, goal :: !Term}
  | -- | The current branch was abandoned. Everything it did — bindings,
    -- store, history, reactivation queue — has been undone by the time
    -- this is emitted, which is what the surrounding @kill@ and
    -- @reactivate@ events would otherwise leave unsaid.
    TEBacktrack {reason :: !BacktrackReason}
  | -- | Quiescence with no choice point left: the current state is a
    -- solution.
    TESolution
  | -- | A search finished, with the outcome that ended it.
    TESearchExit {sname :: !Text, outcome :: !SearchOutcome}
  deriving (Show)

-- | How a search ended. Reported by 'TESearchExit', and the result the
-- driver hands back to the host call that started the search.
--
-- 'SearchCommitted' and 'SearchStopped' both stop at a solution and
-- differ only in what happens to its bindings; that difference is the
-- whole distinction between @commit@ and @stop@ in a
-- @fold_solutions\/4@ step, and between @solve\/1@ and the rest.
data SearchOutcome
  = -- | Stopped at a solution and kept its bindings: nothing is
    -- undone. What @solve\/1@ and a @commit@ step produce.
    SearchCommitted
  | -- | Stopped at a solution and unwound everything to the base
    -- mark. What a @stop@ step produces.
    SearchStopped
  | -- | The search space ran out. Everything is undone.
    SearchExhausted
  deriving (Show, Eq)

-- | Why a search branch was abandoned. Reported by 'TEBacktrack'.
--
-- The first three are exactly the three ways the specification says a
-- branch can fail. The fourth is not a failure at all — it is
-- @find_all@ recording a solution and asking for the next one — and it
-- is distinguished precisely so that a trace never shows a successful
-- branch being reported as exhausted.
data BacktrackReason
  = -- | @search:fail\/0@ was called. This covers @try_unify\/2@, and
    -- therefore @choose\/2@, both of which fail through it.
    BRFail
  | -- | Every alternative of the choice point has been tried.
    BRExhausted
  | -- | A solution was reached and the caller asked to keep searching.
    BRMoreWanted
  deriving (Show, Eq)

-- | The default trace handler: formats the event with two-space
-- indentation per level and writes a line to the given handle.
defaultTraceHandler :: Handle -> TraceHandler
defaultTraceHandler h depth ev = hPutStrLn h (formatEvent depth ev)

-- | Render a single event at the given depth. Pure, so callers can
-- format to any sink (tests use this directly).
formatEvent :: Int -> TraceEvent -> String
formatEvent depth ev = indent ++ body
  where
    indent = replicate (2 * depth) ' '
    body = case ev of
      TETell ct as ->
        "tell " ++ T.unpack ct ++ argList as
      TEActivate ct s as ->
        "activate " ++ showSid s ++ ": " ++ T.unpack ct ++ argList as
      TETryOccurrence ct n r ->
        "try occurrence " ++ T.unpack ct ++ " #" ++ show n ++ " (rule " ++ T.unpack r ++ ")"
      TEPartner ct s as ->
        "partner " ++ showSid s ++ ": " ++ T.unpack ct ++ argList as
      TEHistoryHit r ss ->
        "history hit " ++ T.unpack r ++ " " ++ sidList ss
      TEFire r ss ->
        "fire " ++ T.unpack r ++ " " ++ sidList ss
      TEStore s ct as ->
        "store " ++ showSid s ++ ": " ++ T.unpack ct ++ argList as
      TEKill s ->
        "kill " ++ showSid s
      TEReactivate s ct as ->
        "reactivate " ++ showSid s ++ ": " ++ T.unpack ct ++ argList as
      TEUnify l r n ->
        let suffix
              | n == 0 = ""
              | n == 1 = " (1 constraint reactivated)"
              | otherwise = " (" ++ show n ++ " constraints reactivated)"
         in "unify " ++ prettyTerm l ++ " = " ++ prettyTerm r ++ suffix
      TECallFunction f as ->
        "call " ++ T.unpack (renderFnName f) ++ argList as
      TEReturn v ->
        "return " ++ prettyTerm v
      TECallHost f as r ->
        "host call " ++ T.unpack f ++ argList as ++ " = " ++ prettyTerm r
      TESearchEnter s ->
        "search " ++ T.unpack s
      TEChoice s as ->
        "choice " ++ showSid s ++ ": " ++ termList as
      TETryAlt n total g ->
        "try alt " ++ show n ++ "/" ++ show total ++ ": " ++ prettyTerm g
      TEBacktrack r ->
        "backtrack (" ++ backtrackReason r ++ ")"
      TESolution -> "solution"
      TESearchExit s o ->
        "end search " ++ T.unpack s ++ " (" ++ searchOutcome o ++ ")"

argList :: [Term] -> String
argList [] = ""
argList ts = "(" ++ intercalate ", " (map prettyTerm ts) ++ ")"

termList :: [Term] -> String
termList ts = "[" ++ intercalate ", " (map prettyTerm ts) ++ "]"

searchOutcome :: SearchOutcome -> String
searchOutcome SearchCommitted = "committed"
searchOutcome SearchStopped = "stopped"
searchOutcome SearchExhausted = "exhausted"

backtrackReason :: BacktrackReason -> String
backtrackReason BRFail = "fail"
backtrackReason BRExhausted = "alternatives exhausted"
backtrackReason BRMoreWanted = "more solutions wanted"

sidList :: [SuspensionId] -> String
sidList ss = "[" ++ intercalate ", " (map showSid ss) ++ "]"

showSid :: SuspensionId -> String
showSid (SuspensionId i) = "c#" ++ show i

-- | Render a function name. Lifted lambdas are surfaced as
-- @lambda#N@ to match the user-facing language ("lambdas" rather than
-- "the synthesised @__lambda_N@ function").
renderFnName :: Text -> Text
renderFnName fname =
  case T.breakOn lambdaPrefix fname of
    (_, rest)
      | not (T.null rest) ->
          "lambda#" <> T.drop (T.length lambdaPrefix) rest
    _ -> fname
  where
    lambdaPrefix :: Text
    lambdaPrefix = "__lambda_"
