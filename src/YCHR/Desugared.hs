-- | CHR Abstract Syntax Tree
--
-- This module defines the internal AST for CHR programs. This is not
-- the direct output of the parser, but a desugared and semantically
-- precise representation that guides compilation to the VM.
--
-- Desugaring already performed at this stage:
--
--   * Simplification and propagation rules are represented uniformly
--     as simpagation rules. A simplification rule has an empty 'headKept'
--     list; a propagation rule has an empty 'headRemoved' list. The
--     compiler checks whether 'headRemoved' is empty to decide whether
--     propagation history maintenance is needed.
--
--   * Guards and body goals are represented with distinct types
--     ('Guard' and 'BodyGoal') to enforce that only semantically
--     appropriate goals appear in each position.
module YCHR.Desugared
  ( -- * Program structure
    Program (..),
    Rule (..),
    Head (..),

    -- * Goals
    CommonGoal (..),
    Guard (..),
    BodyGoal (..),

    -- * Re-exports from CHR.Types
    Constraint (..),
    Term (..),
  )
where

import YCHR.Types (Constraint (..), Term (..))

-- | A CHR program is a list of rules.
data Program = Program [Rule]
  deriving (Show, Eq)

-- | A CHR rule in simpagation form.
--
-- All three kinds of CHR rules are represented uniformly:
--
--   * Simplification: @headKept@ is empty, all head constraints are removed.
--   * Propagation: @headRemoved@ is empty, all head constraints are kept.
--   * Simpagation: both @headKept@ and @headRemoved@ are non-empty.
data Rule = Rule
  { -- | Optional rule name (for diagnostics and history)
    ruleName :: Maybe String,
    -- | Head constraints
    ruleHead :: Head,
    -- | Guard conditions (ask semantics, no mutation)
    ruleGuard :: [Guard],
    -- | Body goals (tell semantics, may mutate)
    ruleBody :: [BodyGoal]
  }
  deriving (Show, Eq)

-- | The head of a CHR rule, in desugared simpagation form.
--
-- Kept constraints appear before the backslash, removed constraints
-- after. The compiler uses @null headRemoved@ to determine whether
-- propagation history maintenance is required (it is only needed
-- when no constraints are removed, i.e., for propagation rules).
data Head = Head
  { -- | Kept constraints (before the backslash)
    headKept :: [Constraint],
    -- | Removed constraints (after the backslash)
    headRemoved :: [Constraint]
  }
  deriving (Show, Eq)

-- | Goals that may appear in both guards and bodies.
data CommonGoal
  = -- | Trivially satisfied (no-op).
    GoalTrue
  | -- | Signal failure.
    GoalFail
  deriving (Show, Eq)

-- | Guard goals (ask semantics, no mutation).
--
-- Guards are evaluated to determine whether a rule is applicable.
-- They must not have side effects or bind variables.
data Guard
  = -- | A common goal ('GoalTrue' or 'GoalFail').
    GuardCommon CommonGoal
  | -- | Equality check (ask semantics, Prolog @==@). Returns true if
    -- the two terms are structurally identical. Two distinct unbound
    -- variables are not equal. No mutation occurs.
    GuardEqual Term Term
  | -- | Call a host language function as a boolean test. The function
    -- should return a boolean; the guard succeeds if it returns true.
    GuardHostCall String [Term]
  deriving (Show, Eq)

-- | Body goals (tell semantics, may mutate state).
--
-- Body goals are executed when a rule fires. They may add constraints,
-- bind variables, or perform side effects.
data BodyGoal
  = -- | A common goal ('GoalTrue' or 'GoalFail').
    BodyCommon CommonGoal
  | -- | Add a CHR constraint to the store. This triggers activation
    -- of the new constraint (searching for applicable rules).
    BodyConstraint Constraint
  | -- | Unify two terms (tell semantics, Prolog @=@). May bind
    -- logical variables. Triggers reactivation of affected constraints.
    BodyUnify Term Term
  | -- | Execute a host language statement for its side effects.
    -- The result (if any) is discarded.
    BodyHostStmt String [Term]
  | -- | Call a host language function and bind the result to a variable.
    --
    -- @BodyHostCall varName funcName args@
    --
    -- Calls the host function @funcName@ with the given arguments and
    -- binds the result to the variable named @varName@.
    BodyHostCall String String [Term]
  deriving (Show, Eq)
