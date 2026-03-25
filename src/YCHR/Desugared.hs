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

import Data.Text (Text)
import YCHR.Types

data Program = Program [Rule] deriving (Show, Eq)

data Rule = Rule
  { ruleName :: Maybe Text,
    ruleHead :: Head,
    ruleGuard :: [Guard],
    ruleBody :: [BodyGoal]
  }
  deriving (Show, Eq)

data Head = Head
  { headKept :: [Constraint],
    headRemoved :: [Constraint]
  }
  deriving (Show, Eq)

data CommonGoal = GoalTrue | GoalFail deriving (Show, Eq)

data Guard
  = GuardCommon CommonGoal
  | GuardEqual Term Term
  | GuardExpr Term
  deriving (Show, Eq)

data BodyGoal
  = BodyCommon CommonGoal
  | BodyConstraint Constraint
  | BodyUnify Term Term
  | BodyHostStmt Text [Term]
  | BodyHostCall Text Text [Term]
  | BodyIs Text Term
  deriving (Show, Eq)
