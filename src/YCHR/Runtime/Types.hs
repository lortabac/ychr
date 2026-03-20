-- | Shared types for the CHR Haskell runtime.

module YCHR.Runtime.Types
  ( SuspensionId (..)
  , VarId (..)
  , Var (..)
  , VarState (..)
  , Value (..)
  , RuntimeVal (..)
  ) where

import Data.IORef

-- | Unique identifier for a constraint suspension. Also serves as the
-- observer key on variables for selective reactivation.
newtype SuspensionId = SuspensionId Int
  deriving (Eq, Ord, Show)

-- | Unique identifier for a logical variable.
newtype VarId = VarId Int
  deriving (Eq, Ord, Show)

-- | A logical variable, backed by a mutable cell.
newtype Var = Var (IORef VarState)

-- | The state of a logical variable.
data VarState
  = Unbound !VarId ![SuspensionId]
    -- ^ Not yet bound. Carries a unique ID and a list of observer IDs
    -- (constraints watching this variable for reactivation).
  | Bound !Value
    -- ^ Bound to a value (possibly another variable, forming a chain).

-- | Runtime values that flow through the VM.
data Value
  = VVar !Var
    -- ^ A logical variable (possibly unbound, possibly bound).
  | VInt !Int
  | VAtom !String
  | VBool !Bool
  | VTerm !String ![Value]
    -- ^ Compound term: functor and arguments.

-- | Runtime values for the interpreter. Constraint IDs never flow into
-- unification or term construction.
data RuntimeVal
  = RVal !Value
  | RConstraint !SuspensionId
