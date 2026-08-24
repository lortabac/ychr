{-# LANGUAGE OverloadedStrings #-}

-- | The runtime half of the oracle: a host function the generated
-- program calls, which snapshots the values it is handed and records
-- what it finds.
--
-- Why a host function rather than an in-language @assert_τ\/1@
-- predicate, which is what v1 used:
--
--   * A host call's arguments carry no typing obligation at all
--     (@HostExpr@ types them and returns @any@), so an observation is
--     legal at a variable typed by a /rigid/ head occurrence — where
--     there is no static type an in-language assertion could be
--     declared at. That is where the whole polymorphic surface lives.
--   * It sees the raw 'Value', so it can tell \"unbound\" from
--     \"bound to something of the wrong shape\", and can recover
--     variable /identity/ with 'getVarId' — which is what makes
--     sharing between two store slots observable.
--   * It /records/ instead of raising, so one run yields every witness
--     rather than dying at the first, a violation is a datum in the
--     log rather than the absence of one, and no failure classification
--     has to hinge on a message substring.
--   * It makes runtime facts — did this rule fire? — directly
--     assertable with @cover@, which no in-language mechanism could do
--     (see @Note [Firing rates]@ in "YCHR.TypeSoundness.Gen").
--
-- The one cost is that instrumentation introduces @any@-typed
-- expressions into a fragment defined by not having any. It is
-- confined to the inserted call itself: the observer's result is
-- discarded in body position and consumed by the guard's
-- boolean check in guard position, and never binds a program variable.
module YCHR.TypeSoundness.Observe
  ( -- * Snapshots
    Snap (..),
    snapshot,

    -- * Verdicts
    Verdict (..),
    conformsSnap,

    -- * The log
    ObsLog (..),
    emptyLog,
    Bad (..),
    observerRegistry,
    obsLimit,
  )
where

import Control.Monad.IO.Class (liftIO)
import Data.IORef
import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IntMap
import Data.Text (Text)
import Data.Text qualified as T
import YCHR.Convert (hostFnValues, withDefaultHostFunctions)
import YCHR.Internal.Runtime.Monad (Chr, HostCallRegistry)
import YCHR.Internal.Runtime.Types (Value (..), VarId (..))
import YCHR.Internal.Runtime.Var (deref, getVarId)
import YCHR.TypeSoundness.Types

-- ---------------------------------------------------------------------------
-- Snapshots
-- ---------------------------------------------------------------------------

-- | A runtime value, frozen at the moment it was observed.
--
-- 'SnUnbound' carries the variable's identity rather than collapsing
-- to a placeholder: two positions holding the same 'VarId' hold the
-- same variable, which is the fact the store-interleaving shapes turn
-- on. @valueToTerm@ cannot give this — it renders every unbound
-- variable as a wildcard.
data Snap
  = SnInt Integer
  | SnFloat Double
  | SnBool Bool
  | SnAtom Text
  | SnText Text
  | SnTerm Text [Snap]
  | SnUnbound Int
  | SnWild
  deriving (Eq, Show)

snapshot :: Value -> Chr Snap
snapshot v = do
  d <- deref v
  case d of
    VInt n -> pure (SnInt n)
    VFloat f -> pure (SnFloat f)
    VBool b -> pure (SnBool b)
    VAtom a -> pure (SnAtom a)
    VText t -> pure (SnText t)
    VTerm f as -> SnTerm f <$> traverse snapshot as
    VWildcard -> pure SnWild
    VVar _ -> do
      mvid <- getVarId d
      pure (SnUnbound (maybe (-1) (\(VarId i) -> i) mvid))

-- ---------------------------------------------------------------------------
-- Verdicts
-- ---------------------------------------------------------------------------

-- | Three-valued, because \"not a value of this type\" splits into two
-- cases that mean opposite things.
--
-- 'NotYetBound' says the term holds no value yet. That is a statement
-- about /mode/, which the type system deliberately does not track
-- (@docs\/reference\/type-system.md@ §No mode checking), so it is not a
-- violation of the typing claim — the claim is about values that are
-- bound. 'Outside' says a value is present and inhabits some other
-- type, which is the violation.
data Verdict
  = Inhabits
  | -- | The term, or something inside it, is still an unbound
    -- variable. The payload is a path description for the
    -- counterexample.
    NotYetBound Text
  | Outside Text
  deriving (Eq, Show)

-- | Does a snapshot inhabit a type?
--
-- Atoms are compared on their final name component: values come back
-- with functors that may be qualified (@gen:k0@) or mangled
-- (@gen__k0@) depending on how they were built, and neither says
-- anything about typing.
conformsSnap :: Ty -> Snap -> Verdict
conformsSnap ty s = case s of
  SnUnbound _ -> NotYetBound (render ty)
  SnWild -> NotYetBound (render ty)
  _ -> case ty of
    TInt -> case s of
      SnInt _ -> Inhabits
      _ -> mismatch
    TBool -> case s of
      SnBool _ -> Inhabits
      SnAtom a | baseName a `elem` ["true", "false"] -> Inhabits
      SnTerm f [] | baseName f `elem` ["true", "false"] -> Inhabits
      _ -> mismatch
    TListInt -> listOf TInt s
    TAdt def -> case s of
      SnAtom a -> ctor def (baseName a) []
      SnTerm f as -> ctor def (baseName f) as
      _ -> mismatch
  where
    render = renderTy
    mismatch = Outside (render ty <> " vs " <> describe s)
    listOf el x = case x of
      SnAtom a | baseName a == "[]" -> Inhabits
      SnTerm f [] | baseName f == "[]" -> Inhabits
      SnTerm f [h, t]
        | baseName f == "." -> case conformsSnap el h of
            Inhabits -> listOf el t
            other -> other
      SnUnbound _ -> NotYetBound (render ty)
      SnWild -> NotYetBound (render ty)
      _ -> Outside (render ty <> " vs " <> describe x)
    ctor def n as = case findCtor def n of
      Nothing -> Outside (def.adtName <> " has no constructor " <> n)
      Just c
        | length c.fields /= length as ->
            Outside (n <> " applied to " <> tshow (length as) <> " arguments")
        | otherwise -> firstNonInhabits (zipWith conformsSnap c.fields as)
    firstNonInhabits vs = case filter (/= Inhabits) vs of
      [] -> Inhabits
      (v : _) -> v

-- | The final component of a possibly-qualified, possibly-mangled
-- functor name.
baseName :: Text -> Text
baseName n
  | (_, rest) <- T.breakOnEnd ":" n, not (T.null rest) = unmangle rest
  | otherwise = unmangle n
  where
    unmangle t = case T.breakOnEnd "__" t of
      (pre, post) | not (T.null pre), not (T.null post) -> post
      _ -> t

describe :: Snap -> Text
describe s = case s of
  SnInt n -> "int " <> tshow n
  SnFloat f -> "float " <> tshow f
  SnBool b -> "bool " <> tshow b
  SnAtom a -> "atom " <> a
  SnText t -> "string " <> tshow t
  SnTerm f as -> "compound " <> f <> "/" <> tshow (length as)
  SnUnbound i -> "unbound _" <> tshow i
  SnWild -> "wildcard"

-- ---------------------------------------------------------------------------
-- The log
-- ---------------------------------------------------------------------------

-- | A recorded violation, with everything the counterexample needs.
data Bad = Bad
  { badCode :: Int,
    badWhere :: Text,
    badWhy :: Text,
    badSnaps :: [Snap]
  }
  deriving (Eq, Show)

data ObsLog = ObsLog
  { -- | Hits per site code. This is what makes runtime facts —
    -- \"this rule fired\" — assertable with @cover@.
    logHits :: IntMap Int,
    logBad :: [Bad],
    -- | Sites that saw a term holding no value yet. Expected in the
    -- open regime, so recorded separately from 'logBad'.
    logUnbound :: IntMap Int,
    logCount :: Int,
    -- | Set once 'obsLimit' is reached. A run that overflowed observed
    -- less than it looks like it did, so the property covers against
    -- it rather than letting it pass quietly.
    logOverflow :: Bool
  }
  deriving (Eq, Show)

emptyLog :: ObsLog
emptyLog =
  ObsLog
    { logHits = IntMap.empty,
      logBad = [],
      logUnbound = IntMap.empty,
      logCount = 0,
      logOverflow = False
    }

-- | Cap on recorded observations. A guard-position observation runs
-- once per /candidate match/, not once per firing, so a two-head rule
-- over an n-instance store is quadratic; the cap keeps a pathological
-- program from exhausting memory before the timeout catches it.
obsLimit :: Int
obsLimit = 50_000

-- | The registry a generated program runs under: the defaults plus
-- @ts_obs@.
--
-- 'hostFnValues' rather than one of the typed adapters because the
-- observer must see unbound variables as such; the typed path goes
-- through @valueToTerm@, which renders them as wildcards and loses
-- identity.
--
-- Always returns @true@, so an observation in guard position leaves
-- the guard's meaning unchanged.
observerRegistry :: IntMap ObsSite -> IORef ObsLog -> HostCallRegistry
observerRegistry table ref =
  withDefaultHostFunctions [("ts_obs", hostFnValues go)]
  where
    go args = do
      case args of
        [] -> pure ()
        (codeV : vs) -> do
          code <- intOf <$> deref codeV
          snaps <- traverse snapshot vs
          liftIO (modifyIORef' ref (record table code snaps))
      pure (VBool True)
    intOf v = case v of
      VInt n -> fromInteger n
      _ -> -1

-- | Fold one observation into the log.
--
-- Policy-free by design: it separates \"present but of another type\"
-- from \"holds no value yet\" and records both, leaving which of them
-- counts as a violation to the property. In the ground fragment an
-- unbound observation is itself a violation; once the generator stores
-- unbound values on purpose it is expected at the positions whose
-- declared boundness allows it.
record :: IntMap ObsSite -> Int -> [Snap] -> ObsLog -> ObsLog
record table code snaps lg
  | lg.logCount >= obsLimit = lg {logOverflow = True}
  | otherwise = case IntMap.lookup code table of
      Nothing -> hit {logBad = unknownSite : hit.logBad}
      Just site -> foldl (apply site) hit (verdicts site.osCheck)
  where
    hit =
      lg
        { logHits = IntMap.insertWith (+) code 1 lg.logHits,
          logCount = lg.logCount + 1
        }
    unknownSite =
      Bad code "<unknown site>" "no site registered for this code" snaps
    verdicts (ExpectTys tys) = zipWith conformsSnap tys snaps
    apply site acc v = case v of
      Inhabits -> acc
      NotYetBound why ->
        acc
          { logUnbound = IntMap.insertWith (+) code 1 acc.logUnbound,
            logBad = Bad code site.osWhere ("holds no value yet: " <> why) snaps : acc.logBad
          }
      Outside why ->
        acc {logBad = Bad code site.osWhere why snaps : acc.logBad}
