{-# LANGUAGE DuplicateRecordFields #-}

-- | Internal types for the CHR-to-VM compiler.
module YCHR.Compile.Types
  ( -- * Semantic newtypes
    OccurrenceNumber (..),
    HeadPosition (..),
    PartnerIndex (..),

    -- * Data types
    Occurrence (..),
    Partner (..),

    -- * Occurrence map
    OccurrenceMap,
    occMapEmpty,
    occMapAppend,
    occMapMap,
    lookupOccurrences,

    -- * Variable map
    VarMap,
    varMapFromList,
    lookupVar,
    insertVar,
    notMemberVar,
  )
where

import Data.Map.Strict qualified as Map
import Data.Text (Text)
import YCHR.Desugared qualified as D
import YCHR.Types (Constraint, Identifier, Name, Term)
import YCHR.VM (ConstraintType, Expr)

-- | 1-based occurrence number within a constraint type's occurrence list.
newtype OccurrenceNumber = OccurrenceNumber {unOccurrenceNumber :: Int}
  deriving (Show, Eq, Ord, Num, Enum)

-- | 0-based position in the combined (removed ++ kept) head list.
newtype HeadPosition = HeadPosition {unHeadPosition :: Int}
  deriving (Show, Eq, Ord, Num, Enum)

-- | 0-based index into the partners list of an occurrence.
newtype PartnerIndex = PartnerIndex {unPartnerIndex :: Int}
  deriving (Show, Eq, Ord, Num, Enum)

data Occurrence = Occurrence
  { conName :: Name,
    conArity :: Int,
    number :: OccurrenceNumber,
    rule :: D.Rule,
    activeIdx :: HeadPosition,
    isKept :: Bool,
    activeArgs :: [Term],
    partners :: [Partner]
  }

data Partner = Partner
  { idx :: HeadPosition,
    constraint :: Constraint,
    isKept :: Bool,
    cType :: ConstraintType
  }

newtype OccurrenceMap = OccurrenceMap (Map.Map Identifier [Occurrence])

occMapEmpty :: OccurrenceMap
occMapEmpty = OccurrenceMap Map.empty

occMapAppend :: Identifier -> Occurrence -> OccurrenceMap -> OccurrenceMap
occMapAppend k occ (OccurrenceMap m) = OccurrenceMap (Map.insertWith (++) k [occ] m)

occMapMap :: ([Occurrence] -> [Occurrence]) -> OccurrenceMap -> OccurrenceMap
occMapMap f (OccurrenceMap m) = OccurrenceMap (Map.map f m)

lookupOccurrences :: Identifier -> OccurrenceMap -> [Occurrence]
lookupOccurrences k (OccurrenceMap m) = Map.findWithDefault [] k m

newtype VarMap = VarMap (Map.Map Text Expr)

varMapFromList :: [(Text, Expr)] -> VarMap
varMapFromList = VarMap . Map.fromList

lookupVar :: Text -> VarMap -> Maybe Expr
lookupVar k (VarMap m) = Map.lookup k m

insertVar :: Text -> Expr -> VarMap -> VarMap
insertVar k v (VarMap m) = VarMap (Map.insert k v m)

notMemberVar :: Text -> VarMap -> Bool
notMemberVar k (VarMap m) = Map.notMember k m
