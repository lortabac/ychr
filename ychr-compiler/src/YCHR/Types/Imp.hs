{-# LANGUAGE GADTs #-}

module YCHR.Types.Imp where

import Data.Map (Map)
import Data.Set (Set)
import Data.Text (Text)
import YCHR.Types.Prepared

data ImpEnv var = ImpEnv
  { constraintProcs :: ConstraintProcs var,
    occurrenceProcs :: OccurrenceProcs var,
    activateProcs :: ActivateProcs var
  }

type ConstraintProcs var = Map ConstraintId (Procedure var)

type OccurrenceProcs var = Map (ConstraintId, OccurrenceNumber) (Procedure var)

type ActivateProcs var = Map ConstraintId (Procedure var)

data Procedure var = Procedure
  { params :: [var],
    body :: Imp () var
  }

data Imp t var where
  SuspCreate :: ConstraintId -> [PrTerm] -> Imp Suspension var
  SuspStore :: Suspension -> Imp () var
  SuspKill :: Suspension -> Imp () var
  SuspAlive :: Suspension -> Imp Bool var
  SuspLookup :: ConstraintId -> Imp var [Suspension]
  AddToHistory :: RuleId -> [Suspension] -> Imp () var
  NotInHistory :: RuleId -> [Suspension] -> Imp Bool var
  Activate :: Suspension -> Imp () var
  Foreach :: var -> [Suspension] -> Imp () var
  Assign :: Imp a var -> Imp a var -> Imp var ()
  CallConstraintProc :: ConstraintId -> [PrTerm] -> Imp () var
  CallOccurrenceProc ::
    ConstraintId ->
    OccurrenceNumber ->
    SuspensionId ->
    [PrTerm] ->
    Imp () var
  CallActivateProc :: Suspension -> Imp () var
  If :: Imp Bool var -> Imp () var -> Imp () var
  SuspVar :: var -> Imp Suspension var
  TermVar :: var -> Imp PrTerm var

data Suspension = Suspension
  { constraintId :: ConstraintId,
    args :: [PrTerm],
    suspensionId :: SuspensionId,
    stored :: Bool,
    alive :: Bool,
    history :: Set HistoryItem
  }
  deriving (Eq, Show, Ord)

newtype SuspensionId = SuspensionId {getSuspensionId :: Int}
  deriving (Eq, Show, Ord)

data RuleId = RuleId {getRuleId :: Text}
  deriving (Eq, Show, Ord)

data HistoryItem = HistoryItem
  { rule :: RuleId,
    suspensions :: [Suspension]
  }
  deriving (Eq, Show, Ord)
