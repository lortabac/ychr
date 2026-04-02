{-# LANGUAGE DuplicateRecordFields #-}

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
    Function (..),
    Equation (..),

    -- * Goals
    CommonGoal (..),
    Guard (..),
    BodyGoal (..),

    -- * Re-exports from CHR.Types
    Constraint (..),
    Term (..),
    TypeExpr (..),
    TypeDefinition (..),
  )
where

import Data.Map.Strict (Map)
import Data.Text (Text)
import YCHR.Pretty (AnnP)
import YCHR.Types

data Program = Program
  { rules :: [Rule],
    functions :: [Function],
    constraintTypes :: Map Name [TypeExpr],
    typeDefinitions :: [TypeDefinition]
  }
  deriving (Show)

data Rule = Rule
  { name :: Maybe Text,
    head :: AnnP Head,
    guard :: AnnP [Guard],
    body :: AnnP [BodyGoal]
  }
  deriving (Show)

data Head = Head
  { kept :: [Constraint],
    removed :: [Constraint]
  }
  deriving (Show, Eq)

data CommonGoal = GoalTrue deriving (Show, Eq)

data Guard
  = GuardCommon CommonGoal
  | GuardEqual Term Term
  | GuardMatch Term Name Int
  | GuardGetArg Text Term Int
  | GuardExpr Term
  deriving (Show, Eq)

data BodyGoal
  = BodyCommon CommonGoal
  | BodyConstraint Constraint
  | BodyUnify Term Term
  | BodyHostStmt Text [Term]
  | BodyIs Text Term
  | BodyFunctionCall Name [Term]
  deriving (Show, Eq)

data Function = Function
  { name :: Name,
    arity :: Int,
    argTypes :: Maybe [TypeExpr],
    returnType :: Maybe TypeExpr,
    equations :: [Equation]
  }
  deriving (Show)

data Equation = Equation
  { params :: [Term],
    guards :: [Guard],
    rhs :: Term
  }
  deriving (Show)
