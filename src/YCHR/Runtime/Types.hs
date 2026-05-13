-- | Shared types for the CHR Haskell runtime.
module YCHR.Runtime.Types
  ( SuspensionId (..),
    VarId (..),
    Var (..),
    VarState (..),
    Value (..),
    CallVal (..),
    Suspension (..),
  )
where

import Data.IORef
import Data.Text (Text)
import YCHR.Types (ConstraintType)

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

-- | Runtime values that flow through the VM. Constraint identifiers
-- are a separate runtime kind ('SuspensionId'); they never inhabit
-- this type.
data Value
  = -- | A logical variable (possibly unbound, possibly bound).
    VVar !Var
  | VInt !Int
  | VFloat !Double
  | VAtom !Text
  | VText !Text
  | VBool !Bool
  | -- | Compound term: functor and arguments.
    VTerm !Text ![Value]
  | -- | Wildcard: unifies with anything without binding.
    VWildcard

-- | Procedure-call argument at runtime. Procedures take a heterogeneous
-- mix of value and id parameters; this wrapper carries the kind across
-- the call boundary so the callee can bind each parameter into the right
-- environment slot. Mirrors 'YCHR.VM.Types.CallArg' on the IR side.
data CallVal
  = CVal !Value
  | CId !SuspensionId

-- | A constraint suspension in the store. The 'alive' flag is mutable so
-- that 'killConstraint' is O(1) and copies of the suspension obtained
-- before the kill see the updated state without an explicit lookup.
data Suspension = Suspension
  { suspId :: !SuspensionId,
    suspType :: !ConstraintType,
    args :: ![Value],
    alive :: !(IORef Bool)
  }
