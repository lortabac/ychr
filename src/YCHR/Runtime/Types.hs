-- | Shared types for the CHR Haskell runtime.
module YCHR.Runtime.Types
  ( SuspensionId (..),
    VarId (..),
    Var (..),
    VarState (..),
    Value (..),
    RuntimeVal (..),
  )
where

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
  = -- | Not yet bound. Carries a unique ID and a list of observer IDs
    -- (constraints watching this variable for reactivation).
    Unbound !VarId ![SuspensionId]
  | -- | Bound to a value (possibly another variable, forming a chain).
    Bound !Value

-- | Runtime values that flow through the VM.
data Value
  = -- | A logical variable (possibly unbound, possibly bound).
    VVar !Var
  | VInt !Int
  | VAtom !String
  | VBool !Bool
  | -- | Compound term: functor and arguments.
    VTerm !String ![Value]

-- | Runtime values for the interpreter. Constraint IDs never flow into
-- unification or term construction.
data RuntimeVal
  = RVal !Value
  | RConstraint !SuspensionId
