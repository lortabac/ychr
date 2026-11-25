{-# LANGUAGE OverloadedStrings #-}

-- | Trace filters: pick which 'TraceEvent's reach a handler.
--
-- A filter sits in front of a 'TraceHandler'. The runtime knows nothing
-- about it. Some events don't say which constraint, rule or module they
-- belong to (a @kill@ has only an id, a @partner@ no rule), so the
-- filter keeps a little state: the last event seen at each depth, and
-- the type of every constraint id it has seen.
--
-- An event is shown when:
--
-- * its kind is in 'kinds';
-- * its depth is below 'maxDepth';
-- * it matches 'constraints' and 'rules', when either is given;
--   otherwise its module is not a library module (unless 'showLibrary').
--   Search events count as the query's, so they show by default.
--
-- A shown event is printed at the number of shown events above it, so a
-- @fire@-only trace is a flat list.
module YCHR.Internal.Runtime.TraceFilter
  ( -- * Filters
    TraceFilter (..),
    EventKind (..),
    ConstraintSpec (..),
    defaultTraceFilter,
    defaultKinds,
    eventKind,
    eventKindName,
    parseEventKind,
    parseConstraintSpec,
    matchesSpec,
    splitQualified,

    -- * Running a filter
    FilterState,
    initialFilterState,
    stepFilter,
    filteredTraceHandler,
  )
where

import Data.Char (isDigit)
import Data.IORef (atomicModifyIORef', newIORef)
import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IntMap
import Data.Maybe (mapMaybe)
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as T
import YCHR.Internal.Runtime.Trace (TraceEvent (..), TraceHandler)
import YCHR.Internal.Runtime.Types (SuspensionId (..))

-- | The kinds of event, as named by @-e@.
data EventKind
  = EKTell
  | EKActivate
  | EKTry
  | EKPartner
  | EKHistory
  | EKFire
  | EKStore
  | EKKill
  | EKReactivate
  | EKUnify
  | -- | A function or lambda call, and its return.
    EKCall
  | EKHost
  | -- | All six search events.
    EKSearch
  deriving (Show, Eq, Ord, Enum, Bounded)

eventKindName :: EventKind -> Text
eventKindName k = case k of
  EKTell -> "tell"
  EKActivate -> "activate"
  EKTry -> "try"
  EKPartner -> "partner"
  EKHistory -> "history"
  EKFire -> "fire"
  EKStore -> "store"
  EKKill -> "kill"
  EKReactivate -> "reactivate"
  EKUnify -> "unify"
  EKCall -> "call"
  EKHost -> "host"
  EKSearch -> "search"

parseEventKind :: Text -> Maybe EventKind
parseEventKind t = lookup t [(eventKindName k, k) | k <- [minBound .. maxBound]]

eventKind :: TraceEvent -> EventKind
eventKind ev = case ev of
  TETell {} -> EKTell
  TEActivate {} -> EKActivate
  TETryOccurrence {} -> EKTry
  TEPartner {} -> EKPartner
  TEHistoryHit {} -> EKHistory
  TEFire {} -> EKFire
  TEStore {} -> EKStore
  TEKill {} -> EKKill
  TEReactivate {} -> EKReactivate
  TEUnify {} -> EKUnify
  TECallFunction {} -> EKCall
  TEReturn {} -> EKCall
  TECallHost {} -> EKHost
  TESearchEnter {} -> EKSearch
  TEChoice {} -> EKSearch
  TETryAlt {} -> EKSearch
  TEBacktrack {} -> EKSearch
  TESolution -> EKSearch
  TESearchExit {} -> EKSearch

-- | A constraint as named by @-c@: @name@, @name/N@, @mod:name@ or
-- @mod:name/N@.
data ConstraintSpec = ConstraintSpec
  { specModule :: Maybe Text,
    specName :: Text,
    specArity :: Maybe Int
  }
  deriving (Show, Eq)

-- | Parse a @-c@ value. A trailing @/N@ with digits only is the arity.
parseConstraintSpec :: Text -> Maybe ConstraintSpec
parseConstraintSpec t
  | T.null t = Nothing
  | otherwise =
      let (namepart, ar) = case T.breakOnEnd "/" t of
            (pre, digits)
              | T.length pre > 1,
                not (T.null digits),
                T.all isDigit digits ->
                  (T.dropEnd 1 pre, Just (read (T.unpack digits)))
            _ -> (t, Nothing)
          (m, n) = splitQualified namepart
       in if T.null n then Nothing else Just (ConstraintSpec m n ar)

-- | Split @mod:name@ at the first @:@. Module names hold no @:@, so a
-- name that is itself an operator with a colon stays whole.
splitQualified :: Text -> (Maybe Text, Text)
splitQualified t = case T.breakOn ":" t of
  (m, rest)
    | not (T.null m), not (T.null rest) -> (Just m, T.drop 1 rest)
  _ -> (Nothing, t)

-- | Does a constraint (qualified name, arity if known) match a spec?
matchesSpec :: ConstraintSpec -> (Text, Maybe Int) -> Bool
matchesSpec spec (qn, ar) =
  let (m, n) = splitQualified qn
   in n == spec.specName
        && maybe True (\sm -> m == Just sm) spec.specModule
        && case (spec.specArity, ar) of
          (Just a, Just b) -> a == b
          _ -> True

data TraceFilter = TraceFilter
  { -- | @-c@. Empty: no constraint filter.
    constraints :: [ConstraintSpec],
    -- | @-r@. Empty: no rule filter.
    rules :: Set Text,
    kinds :: Set EventKind,
    -- | @--depth N@: hide events at depth N or more. This is the
    -- interpreter's depth, so hidden events count too.
    maxDepth :: Maybe Int,
    -- | Modules hidden unless named or 'showLibrary'.
    libraryModules :: Set Text,
    -- | @--all@.
    showLibrary :: Bool
  }
  deriving (Show)

-- | Every kind but host calls.
defaultKinds :: Set EventKind
defaultKinds = Set.delete EKHost (Set.fromList [minBound .. maxBound])

-- | What @:trace@ shows with no options, given the library modules.
defaultTraceFilter :: Set Text -> TraceFilter
defaultTraceFilter libs =
  TraceFilter
    { constraints = [],
      rules = Set.empty,
      kinds = defaultKinds,
      maxDepth = Nothing,
      libraryModules = libs,
      showLibrary = False
    }

-- | What the filter remembers about an earlier event.
data Frame = Frame
  { depth :: !Int,
    shown :: !Bool,
    -- | Module the event belongs to. 'Nothing' is the query.
    frameModule :: !(Maybe Text),
    -- | Innermost enclosing occurrence.
    frameRule :: !(Maybe RuleCtx),
    -- | Arity of the constraint, for an activate or reactivate.
    frameArity :: !(Maybe Int)
  }

-- | The rule an event belongs to.
data RuleCtx = RuleCtx
  { ruleName :: !Text,
    -- | Module of the occurrence's constraint. The rule itself may live
    -- elsewhere, but the events don't say.
    ruleModule :: !(Maybe Text)
  }

-- | A constraint id's type, as seen on an earlier event.
data SuspType = SuspType
  { typeName :: !Text,
    typeArity :: !Int
  }

-- | Strict fields: a lazy map would keep every event alive until the
-- next lookup.
data FilterState = FilterState
  { -- | Innermost first, depths strictly decreasing.
    frames :: ![Frame],
    suspTypes :: !(IntMap SuspType)
  }

initialFilterState :: FilterState
initialFilterState = FilterState [] IntMap.empty

-- | Feed one event. Returns the new state and, if the event is shown,
-- the depth to print it at.
stepFilter :: TraceFilter -> FilterState -> Int -> TraceEvent -> (FilterState, Maybe Int)
stepFilter flt st d ev = (st', if isShown then Just printed else Nothing)
  where
    sameDepth = case dropWhile (\f -> f.depth > d) st.frames of
      (f : _) | f.depth == d -> Just f
      _ -> Nothing
    above = dropWhile (\f -> f.depth >= d) st.frames
    parent = case above of
      (f : _) -> Just f
      [] -> Nothing
    types = recordTypes ev st.suspTypes
    lookupSid (SuspensionId i) =
      (\t -> (t.typeName, Just t.typeArity)) <$> IntMap.lookup i types
    parentModule = parent >>= (.frameModule)
    parentRule = parent >>= (.frameRule)

    -- The constraints this event is about.
    evConstraints :: [(Text, Maybe Int)]
    evConstraints = case ev of
      TETell ct as -> [(ct, Just (length as))]
      TEActivate ct _ as -> [(ct, Just (length as))]
      TETryOccurrence ct _ _ -> [(ct, parent >>= (.frameArity))]
      TEPartner ct _ as -> [(ct, Just (length as))]
      TEStore _ ct as -> [(ct, Just (length as))]
      TEReactivate _ ct as -> [(ct, Just (length as))]
      TEKill s -> maybe [] pure (lookupSid s)
      TEFire _ ss -> mapMaybe lookupSid ss
      TEHistoryHit _ ss -> mapMaybe lookupSid ss
      _ -> []

    occModule = parentRule >>= (.ruleModule)
    evRule = case ev of
      TETryOccurrence ct _ r -> Just (RuleCtx r (ctModule ct))
      TEFire r _ -> Just (RuleCtx r occModule)
      TEHistoryHit r _ -> Just (RuleCtx r occModule)
      _ -> parentRule

    ctModule ct = fst (splitQualified ct)
    evModule = case ev of
      TETell ct _ -> ctModule ct
      TEActivate ct _ _ -> ctModule ct
      TETryOccurrence ct _ _ -> ctModule ct
      TEPartner ct _ _ -> ctModule ct
      TEStore _ ct _ -> ctModule ct
      TEReactivate _ ct _ -> ctModule ct
      TEKill _ -> case evConstraints of
        ((ct, _) : _) -> ctModule ct
        [] -> parentModule
      TEFire {} -> occModule
      TEHistoryHit {} -> occModule
      TECallFunction f _ -> fst (splitQualified f)
      TEReturn {} -> maybe parentModule (.frameModule) sameDepth
      -- A search is started from a library call (@solve@, @findall@)
      -- but it is the user's search, so its events always show.
      _ | eventKind ev == EKSearch -> Nothing
      _ -> parentModule

    evArity = case ev of
      TEActivate _ _ as -> Just (length as)
      TEReactivate _ _ as -> Just (length as)
      _ -> Nothing

    kindOk = eventKind ev `Set.member` flt.kinds
    depthOk = maybe True (d <) flt.maxDepth
    named = not (null flt.constraints) || not (Set.null flt.rules)
    constraintOk =
      null flt.constraints
        || any (\c -> any (`matchesSpec` c) flt.constraints) evConstraints
    ruleOk =
      Set.null flt.rules
        || maybe False (\r -> r.ruleName `Set.member` flt.rules) evRule
    moduleOk =
      flt.showLibrary
        || maybe True (`Set.notMember` flt.libraryModules) evModule
    -- A depth cut hides the whole subtree; the other tests don't, so a
    -- user lambda called from a hidden library function still shows.
    isShown =
      kindOk && depthOk && if named then constraintOk && ruleOk else moduleOk
    printed = length (filter (.shown) above)

    frame =
      Frame
        { depth = d,
          shown = isShown,
          frameModule = evModule,
          frameRule = evRule,
          frameArity = evArity
        }
    st' = FilterState {frames = frame : above, suspTypes = types}

-- | Remember the type of every constraint id an event names with it.
recordTypes :: TraceEvent -> IntMap SuspType -> IntMap SuspType
recordTypes ev m = case ev of
  TEActivate ct s as -> ins s ct as
  TEPartner ct s as -> ins s ct as
  TEStore s ct as -> ins s ct as
  TEReactivate s ct as -> ins s ct as
  _ -> m
  where
    ins (SuspensionId i) ct as = IntMap.insert i (SuspType ct (length as)) m

-- | Wrap a handler with a filter. Each call makes fresh state, so make
-- one per traced query.
filteredTraceHandler :: TraceFilter -> TraceHandler -> IO TraceHandler
filteredTraceHandler flt inner = do
  ref <- newIORef initialFilterState
  pure $ \d ev -> do
    out <- atomicModifyIORef' ref (\st -> stepFilter flt st d ev)
    maybe (pure ()) (\pd -> inner pd ev) out
