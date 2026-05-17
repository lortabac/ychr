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
--
--   * Constraint head names and function names are 'QualifiedName',
--     so the qualification invariant established by the renamer and
--     committed by the resolver is reflected in the type system.
module YCHR.Desugared
  ( -- * Program structure
    Program (..),
    Rule (..),
    Head (..),
    Function (..),
    Equation (..),

    -- * Goals
    Guard (..),
    BodyGoal (..),

    -- * Expressions
    Expr (..),

    -- * Re-exports from CHR.Types
    QualifiedConstraint (..),
    QualifiedName (..),
    HeadConstraint (..),
    HeadArg (..),
    Term (..),
    TypeExpr (..),
    TypeDefinition (..),
    BoundSig (..),
  )
where

import Data.Map.Strict (Map)
import Data.Text (Text)
import YCHR.Parsed (AnnP)
import YCHR.Resolved (Expr (..))
import YCHR.Types

data Program = Program
  { rules :: [Rule],
    functions :: [Function],
    constraintTypes :: Map QualifiedName [TypeExpr],
    -- | Bounds declared on each @:- chr_constraint@ that carries a
    -- @requiring@ clause. See 'YCHR.Resolved.Program' for the
    -- bounded-vs-unbounded convention (constraints without bounds are
    -- absent from the map).
    constraintBounds :: Map QualifiedName [BoundSig],
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
  { kept :: [HeadConstraint],
    removed :: [HeadConstraint]
  }
  deriving (Show, Eq)

-- | Guards over the typed 'Expr' AST. 'GuardMatch' and 'GuardGetArg'
-- always carry a 'VarExpr' as their operand: HNF only introduces
-- match/getarg guards for fresh variables it has just bound. The
-- operand type is left as 'Expr' rather than 'Text' so the lambda
-- lifter and pretty-printer can walk guards uniformly.
data Guard
  = GuardEqual Expr Expr
  | GuardMatch Expr Name Int
  | GuardGetArg Text Expr Int
  | GuardExpr Expr
  deriving (Show, Eq)

-- | Body goals over the typed 'Expr' AST.
--
-- 'BodyTell' is a tell of a user-declared constraint. Its arguments
-- are 'Expr' and are evaluated at runtime, like every other expression
-- position in the language (function args, constructor args, @is@ RHS,
-- @=@ operands). Head patterns and equation patterns still carry
-- 'Term' (see 'HeadConstraint' / 'Equation'); the call-vs-constructor
-- question is decided structurally for tells but does not arise for
-- patterns.
--
-- 'BodyCall' replaces the legacy @BodyFunctionCall@ for static calls
-- and 'BodyApply' replaces it for dynamic dispatch ('$call').
data BodyGoal
  = BodyTrue
  | BodyTell QualifiedName [Expr]
  | BodyUnify Expr Expr
  | BodyHostStmt Text [Expr]
  | BodyIs Text Expr
  | BodyCall QualifiedName [Expr]
  | BodyApply Expr [Expr]
  deriving (Show, Eq)

data Function = Function
  { name :: QualifiedName,
    arity :: Int,
    signatures :: [([TypeExpr], TypeExpr)],
    -- | Bounds declared on this function via @requiring@. Empty when
    -- the function is unbounded.
    requiring :: [BoundSig],
    equations :: AnnP [Equation]
  }
  deriving (Show)

data Equation = Equation
  { params :: [HeadArg],
    guards :: [Guard],
    rhs :: Expr
  }
  deriving (Show)
