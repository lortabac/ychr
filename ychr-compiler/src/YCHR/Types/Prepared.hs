{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module YCHR.Types.Prepared where

import Data.Map (Map)
import YCHR.Types.Common

data PrRule = PrRule
  { remove :: [Occurrence],
    head :: [Occurrence],
    guard :: PrGuard,
    body :: PrBody
  }

type PrGuard = Guard VariableId ConstraintId

type PrBody = Body VariableId ConstraintId

type PrTerm = Term VariableId

type OccurrenceMap = Map ConstraintId PrRule

newtype VariableId = VariableId {getVariableId :: Int}
  deriving stock (Eq, Show, Ord)
  deriving newtype (Enum)

newtype ConstraintId = ConstraintId {getConstraintId :: Int}
  deriving stock (Eq, Show, Ord)
  deriving newtype (Enum)

newtype OccurrenceNumber = OccurrenceNumber {getOccurrenceNumber :: Int}
  deriving stock (Eq, Show)
  deriving newtype (Enum)

data Occurrence = Occurrence
  { occurrenceNumber :: OccurrenceNumber,
    constraintId :: ConstraintId,
    args :: [VariableId]
  }
  deriving (Eq, Show)
