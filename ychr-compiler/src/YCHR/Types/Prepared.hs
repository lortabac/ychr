{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module YCHR.Types.Prepared where

import Data.Map (Map)
import YCHR.Types.Common

data PrRule = PrRule
  { head :: [PrConstraint],
    remove :: [PrConstraint],
    guard :: PrGuard,
    body :: PrBody
  }
  deriving (Eq, Show)

data PrConstraint = PrConstraint
  { constraint :: ChrConstraint VariableId ConstraintId,
    position :: Int
  }
  deriving (Eq, Show)

type PrGuard = Guard VariableId ConstraintId

type PrBody = Body VariableId ConstraintId

type PrTerm = Term VariableId

type OccurrenceMap = Map ConstraintId [Occurrence]

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
    position :: Int,
    constraintId :: ConstraintId,
    arguments :: [VariableId]
  }
  deriving (Eq, Show)
