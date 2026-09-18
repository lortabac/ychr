-- | Shared types for the CHR Haskell runtime.
module YCHR.Internal.Runtime.Types
  ( SuspensionId (..),
    VarId (..),
    Var (..),
    VarState (..),
    Value (..),
    CallVal (..),
    Suspension (..),

    -- * Search trail
    TrailEntry (..),
    TrailState (..),
    Trail (..),
    TrailMark (..),
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
--
-- The constructors are exported only because 'Value', 'Var' and
-- 'VarState' are mutually recursive and so cannot be split across
-- modules. "YCHR.Internal.Runtime.Var" is the only module that may
-- read or write them; everything else goes through that module's
-- operations, and in particular sees a dereferenced cell as its
-- @Deref@ view rather than as a raw 'VarState'.
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

-- ---------------------------------------------------------------------------
-- Search trail
-- ---------------------------------------------------------------------------

-- | One undoable write, paired with the value the cell held /before/
-- it. Replaying an entry restores that value.
--
-- The trail covers exactly the mutable cells that a snapshot of the
-- session's 'Data.IORef.IORef's cannot reach. The store, the
-- propagation history and the reactivation queue all hold persistent
-- structures behind a single reference, so "undo" for them is a
-- pointer write ("YCHR.Internal.Runtime.Search"). Variable cells and
-- suspension flags are individual references reachable only by
-- walking, and are shared across session forks besides, so they need
-- a log.
data TrailEntry
  = -- | A logical-variable cell and its previous 'VarState'. Covers
    -- bindings, observer-list updates, and the writes 'deref' makes
    -- for path compression — which have to be here: a cell compressed
    -- to point past a variable the branch bound must be restored
    -- alongside it.
    TrailVar !Var !VarState
  | -- | A suspension's @alive@ or @stored@ flag and its previous
    -- value. The two flags are the only mutable part of a
    -- 'Suspension'.
    TrailFlag !(IORef Bool) !Bool

-- | Trail contents plus its length. Bundled in one cell so a trailed
-- write costs a single 'Data.IORef.modifyIORef''; the length is what
-- makes a 'TrailMark' an @Int@ rather than something that has to be
-- compared against the list.
data TrailState = TrailState
  { entries :: ![TrailEntry],
    length :: !Int
  }

-- | The undo log of the outermost search: one trail is
-- installed by the outermost 'YCHR.Internal.Runtime.Search' entry and
-- shared by every session forked underneath it, so that a nested
-- search which commits still leaves its writes undoable by the
-- enclosing one. Entries are newest-first.
newtype Trail = Trail (IORef TrailState)

-- | A position on a 'Trail', taken before a branch and unwound to
-- when it is abandoned. Just the trail length at the time it was
-- taken.
newtype TrailMark = TrailMark Int
  deriving (Eq, Ord, Show)
