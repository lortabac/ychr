{-# LANGUAGE OverloadedRecordDot #-}

-- | Per-argument indexes for the constraint store.
--
-- The /Indexing/ optimization of Van Weert, Wuille, Schrijvers and
-- Demoen, "CHR for Imperative Host Languages" (paper §5.3). The
-- compiler already annotates every partner lookup with the equality
-- conditions its guard implies — the 'YCHR.Internal.VM.Foreach' index
-- conditions. This module is the runtime half of that contract: an
-- index per (constraint type, argument position) that answers such a
-- condition with a bucket instead of a scan of the whole type.
--
-- == The index may only narrow the iterator
--
-- The iterator's conditions are re-checked per candidate by
-- @checkConditions@, which stays the decision procedure. So a candidate
-- set is allowed to be a /superset/ of the matching suspensions, never
-- a subset. A suspension is therefore filed under a key only when its
-- indexed argument was fully ground when it was stored
-- ('GroundKey'), and every other suspension — an unbound variable, or
-- a compound term containing one — goes into that position's non-ground
-- fallback set ('posRest'). A lookup for a ground key yields the
-- bucket's slots plus the whole fallback set.
--
-- Two properties make that superset exact enough to be worth having:
--
--   * Ground values are immutable in this runtime (only logical
--     variables and the @alive@ \/ @stored@ flags are mutable), so a
--     suspension's key never changes under it. This is also why the
--     interpreter refuses a driver condition whose value is not ground:
--     a key that could change mid-loop is a key no index can hold.
--
--   * Key equality is never /finer/ than ask-equality
--     ('YCHR.Internal.Runtime.Var.equal'), or a matching candidate
--     would be dropped. 'floatKey' is where that direction has to be
--     defended, and it coarsens deliberately.
--
-- == Slots, not suspensions
--
-- The index stores /store slots/: positions in the type's append-only
-- 'Data.Sequence.Seq'. That is what makes an ascending-slot candidate
-- list reproduce the store's iteration order exactly, which keeps the
-- change invisible to programs whose result depends on rule-firing
-- order. Slots stay valid because the store is only ever appended to,
-- and the index is restored by the same search snapshot as the store it
-- describes — see @StoreSnapshot@ in "YCHR.Internal.Runtime.Search".
--
-- == When the index is built
--
-- 'indexablePositions' — defined in "YCHR.Internal.VM.Index", over the
-- IR, and re-exported here — reads the position set off the program:
-- exactly the (constraint type, argument position) pairs some 'Foreach'
-- index condition refers to. A store only records entries for those, so
-- a program with no index conditions — @fib@, the search benchmarks —
-- pays nothing at all. A lookup whose position is not in the set falls
-- back to the plain store scan — as does a type whose bucket has not
-- reached 'indexThreshold' ('typeIndexed'). A query-time procedure
-- merged in after session initialisation is not part of the set either
-- ('YCHR.Internal.Runtime.Session.withCHRExtra'), so a position only it
-- looks up scans; a position the compiled program already looks up is
-- indexed, and using it is sound for the newcomer too.
module YCHR.Internal.Runtime.Index
  ( -- * Keys
    GroundKey (..),
    floatKey,

    -- * Index state
    PosIndex (..),
    emptyPosIndex,
    StoreIndex,
    emptyStoreIndex,
    indexThreshold,
    typeIndexed,
    insertConstraints,
    candidateSlots,

    -- * Derivation from the program
    indexablePositions,
  )
where

import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IntMap
import Data.IntSet (IntSet)
import Data.IntSet qualified as IntSet
import Data.List qualified as List
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe (fromMaybe)
import Data.Text (Text)
import YCHR.Internal.Types (ConstraintType (..))
import YCHR.Internal.VM.Index (indexablePositions)

-- ---------------------------------------------------------------------------
-- Keys
-- ---------------------------------------------------------------------------

-- | The lookup key of a constraint argument.
--
-- The constructors mirror the ground cases of
-- 'YCHR.Internal.Runtime.Var.equal'': asking two of these for 'Eq' is
-- the same question as asking @equal@ for the corresponding values,
-- except that the key may be coarser (which only ever yields extra
-- candidates for the per-candidate check to reject). @VInt@ and
-- @VFloat@ are distinct constructors because @equal@ never equates an
-- integer with a float.
data GroundKey
  = KInt !Integer
  | -- | A 'Double' that is neither NaN nor negative zero; see 'floatKey'.
    KFloat !Double
  | -- | Every NaN. @equal@ calls NaN unequal to everything including
    -- itself, so collapsing them can only cost a rejected candidate.
    KNaN
  | KAtom !Text
  | KText !Text
  | KBool !Bool
  | KTerm !Text ![GroundKey]
  deriving (Show, Eq, Ord)

-- | The key of a floating-point value.
--
-- @equal@ compares floats with @==@, which says @-0.0 == 0.0@ but not
-- @NaN == NaN@. The derived 'Ord' on 'GroundKey' says the opposite in
-- both cases, so a raw @Double@ would make the key finer than
-- ask-equality for negative zero (dropping a candidate) and finer for
-- NaN in the harmless direction. Normalising both away keeps key
-- equality at or below ask-equality, and keeps an unlawful 'Ord'
-- instance out of the 'Map' the buckets are keyed by.
floatKey :: Double -> GroundKey
floatKey x
  | isNaN x = KNaN
  | x == 0 = KFloat 0
  | otherwise = KFloat x

-- ---------------------------------------------------------------------------
-- Index state
-- ---------------------------------------------------------------------------

-- | What the store knows about one argument position of one constraint
-- type: a bucket of store slots per ground key, plus the slots whose
-- value at this position was not fully ground when they were stored.
data PosIndex = PosIndex
  { posBuckets :: !(Map GroundKey IntSet),
    posRest :: !IntSet
  }
  deriving (Show, Eq)

-- | An index position that has seen no store yet.
emptyPosIndex :: PosIndex
emptyPosIndex = PosIndex Map.empty IntSet.empty

-- | The whole index: constraint type index, then argument position.
--
-- A type's key is present exactly when that type's bucket is /indexed/:
-- the store files nothing for it until it holds 'indexThreshold'
-- constraints, and files the whole bucket in one pass at that point.
-- See 'typeIndexed'.
type StoreIndex = IntMap (IntMap PosIndex)

-- | An index over a store with no constraints in it.
emptyStoreIndex :: StoreIndex
emptyStoreIndex = IntMap.empty

-- | How many constraints of one type the store must hold before an index
-- for it is worth maintaining.
--
-- The trade is per store, not per lookup: filing an entry allocates a
-- path through the index whether or not anything ever looks it up, while
-- a bucket of a handful of constraints is cheaper to scan than to query.
-- So a type is indexed on demand — nothing is filed until its bucket
-- reaches this size, at which point the whole bucket is filed in one
-- pass — which keeps the index a win-or-neutral change rather than a
-- small tax on programs whose stores stay small.
--
-- The value comes from the benchmark suite: @test/golden/graph_test@,
-- a store-heavy shape whose constraint types stay below it, runs ~13%
-- slower with indexing from the first store and exactly as before with
-- this threshold; @leq_closure@, whose @leq@ bucket reaches the
-- thousands, crosses it immediately and keeps its ~50% gain.
indexThreshold :: Int
indexThreshold = 16

-- | Whether the store is maintaining an index for a type. A lookup for
-- an unindexed type must scan.
typeIndexed :: ConstraintType -> StoreIndex -> Bool
typeIndexed cType si = case cType of ConstraintType tidx -> IntMap.member tidx si

-- | Record stored suspensions in the index. Each element pairs a store
-- slot — the suspension's position in the type's store sequence — with
-- its /indexed/ argument positions and their keys, 'Nothing' when the
-- argument was not fully ground.
--
-- A single store passes one element; the pass that crosses
-- 'indexThreshold' passes the whole bucket.
insertConstraints ::
  ConstraintType ->
  [(Int, [(Int, Maybe GroundKey)])] ->
  StoreIndex ->
  StoreIndex
insertConstraints cType stores si0 = List.foldl' insertStore si0 stores
  where
    ConstraintType tidx = cType
    insertStore si (slot, entries) = List.foldl' (insertEntry slot) si entries
    insertEntry slot si (pos, mkey) =
      IntMap.alter (Just . insertAt slot pos mkey . fromMaybe IntMap.empty) tidx si
    insertAt slot pos mkey =
      IntMap.alter (Just . updateAt slot mkey . fromMaybe emptyPosIndex) pos
    updateAt slot mkey p = case mkey of
      Just key ->
        p
          { posBuckets =
              Map.insertWith IntSet.union key (IntSet.singleton slot) p.posBuckets
          }
      Nothing -> p {posRest = IntSet.insert slot p.posRest}

-- | The store slots that may hold a suspension whose argument at
-- @pos@ is 'equal' to a value with key @key@, in ascending (store)
-- order. Consult this only for a position of a type the store is
-- actually indexing — one 'indexablePositions' reports /and/
-- 'typeIndexed' accepts. An unindexed type has no entries, and an empty
-- answer for it would lose every candidate it holds.
candidateSlots :: ConstraintType -> Int -> GroundKey -> StoreIndex -> IntSet
candidateSlots cType pos key si = case IntMap.lookup tidx si >>= IntMap.lookup pos of
  Nothing -> IntSet.empty
  Just p -> IntSet.union (Map.findWithDefault IntSet.empty key p.posBuckets) p.posRest
  where
    ConstraintType tidx = cType
