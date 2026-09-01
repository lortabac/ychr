-- | Shared types for the CHR Haskell runtime.
module YCHR.Internal.Runtime.Types
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
import YCHR.Internal.Types (ConstraintType)

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
    -- 'YCHR.Run.deref' follows the chain to what it stands for.
    VVar !Var
  | -- | Arbitrary-precision integer.
    VInt !Integer
  | -- | Floating-point number.
    VFloat !Double
  | -- | Atom: a symbolic constant. Zero-arity compounds collapse to
    -- this form at run time, unlike in the AST.
    VAtom !Text
  | -- | String.
    VText !Text
  | -- | Boolean. Guards and the prelude's comparisons produce these.
    VBool !Bool
  | -- | Compound term: functor and arguments.
    VTerm !Text ![Value]
  | -- | Wildcard: unifies with anything without binding.
    VWildcard

-- | Procedure-call argument at runtime. Procedures take a heterogeneous
-- mix of value and id parameters; this wrapper carries the kind across
-- the call boundary so the callee can bind each parameter into the right
-- environment slot. Mirrors 'YCHR.Internal.VM.Types.CallArg' on the IR side.
data CallVal
  = CVal !Value
  | CId !SuspensionId

-- | A constraint suspension in the store. The 'alive' flag is mutable so
-- that 'killConstraint' is O(1) and copies of the suspension obtained
-- before the kill see the updated state without an explicit lookup.
-- The 'stored' flag makes 'YCHR.Internal.Runtime.Store.storeConstraint'
-- idempotent: under Late Storage the compiler may emit more than one
-- reachable 'Store' for the same suspension (per fired kept occurrence,
-- and at the end of every activation, including re-activations), and
-- only the first may append to the store and register observers.
data Suspension = Suspension
  { suspId :: !SuspensionId,
    suspType :: !ConstraintType,
    args :: ![Value],
    alive :: !(IORef Bool),
    stored :: !(IORef Bool)
  }
