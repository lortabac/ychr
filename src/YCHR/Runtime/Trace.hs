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
-- 'SessionEnv' carries a @Maybe (TraceEvent -> IO ())@ handler; when
-- @Nothing@, the cost of tracing is a single pointer test inside the
-- interpreter's emission helper. The REPL's @:trace@ command installs
-- 'defaultTraceHandler' for the duration of one query.
module YCHR.Runtime.Trace
  ( TraceEvent (..),
    TraceHandler,
    defaultTraceHandler,
    formatEvent,
  )
where

import Data.List (intercalate)
import Data.Text (Text)
import Data.Text qualified as T
import System.IO (Handle, hPutStrLn)
import YCHR.Pretty (prettyTerm)
import YCHR.Runtime.Types (SuspensionId (..))
import YCHR.Types (Term)

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
  deriving (Show)

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

argList :: [Term] -> String
argList [] = ""
argList ts = "(" ++ intercalate ", " (map prettyTerm ts) ++ ")"

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
