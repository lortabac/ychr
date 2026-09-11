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
module YCHR.Internal.Desugared
  ( -- * Program structure
    Program (..),
    Rule (..),
    Head (..),
    Function (..),
    Equation (..),

    -- * Goals
    Guard (..),
    BodyGoal (..),
    FunStmt (..),

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

import Data.List.NonEmpty (NonEmpty)
import Data.Map.Strict (Map)
import Data.Text (Text)
import YCHR.Internal.Parsed (AnnP)
import YCHR.Internal.Resolved (Expr (..))
import YCHR.Internal.Types

data Program = Program
  { rules :: [Rule],
    functions :: [Function],
    constraintTypes :: Map ConstraintKey [TypeExpr],
    -- | Bounds declared on each @:- chr_constraint@ that carries a
    -- @requiring@ clause. See 'YCHR.Internal.Resolved.Program' for the
    -- bounded-vs-unbounded convention (constraints without bounds are
    -- absent from the map).
    constraintBounds :: Map ConstraintKey [BoundSig],
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
--
-- 'BodyOr' is the surface @;@ operator: a choice between two or more
-- body conjunctions, flattened out of the right-nested @;@ the parser
-- produces. It survives only as far as
-- \"YCHR.Internal.Desugar.Disjunction\", which lifts each branch into
-- its own constraint and rewrites the node into a @search:alt@ tell;
-- the type checker sees the pre-lowering form, where each branch is
-- still in the enclosing rule's scope. The 'NonEmpty' is the parser's
-- guarantee made structural: a @;@ has at least two branches, and a
-- node with none would silently mean \"fail\".
data BodyGoal
  = BodyTrue
  | BodyTell QualifiedName [Expr]
  | BodyUnify Expr Expr
  | BodyHostStmt Text [Expr]
  | BodyIs Text Expr
  | BodyCall QualifiedName [Expr]
  | BodyApply Expr [Expr]
  | BodyOr (NonEmpty [BodyGoal])
  deriving (Show, Eq)

data Function = Function
  { name :: QualifiedName,
    arity :: Int,
    signatures :: [([TypeExpr], TypeExpr)],
    -- | Bounds declared on this function via @requiring@. Empty when
    -- the function is unbounded.
    requiring :: [BoundSig],
    -- | The refinement type declared via @refining@, trusted as an
    -- axiom by the type checker. 'Nothing' for an ordinary function.
    refining :: Maybe TypeExpr,
    equations :: AnnP [Equation]
  }
  deriving (Show)

data Equation = Equation
  { params :: [HeadArg],
    guards :: [Guard],
    -- | Statements executed before evaluating 'rhs'. Empty for
    -- single-expression bodies. The desugarer is responsible for
    -- restricting which 'R.Expr' shapes are accepted in non-final
    -- position; see 'FunStmt'.
    prelude :: [FunStmt],
    rhs :: Expr
  }
  deriving (Show)

-- | A statement appearing in non-final position of a function equation's
-- right-hand side. Strictly a subset of 'BodyGoal' — rule-body-only forms
-- like 'BodyTell', 'BodyUnify', and 'BodyTrue' are intentionally not
-- representable.
data FunStmt
  = -- | @X is E@. The LHS must be a variable; the desugarer rejects
    -- non-variable LHS in this position.
    FunIs Text Expr
  | -- | @host:f(args)@ evaluated for side effects.
    FunHostStmt Text [Expr]
  | -- | Statically resolved user-function call; result discarded.
    FunCall QualifiedName [Expr]
  | -- | Dynamic dispatch (@'$call'(F, args)@); result discarded.
    FunApply Expr [Expr]
  deriving (Show, Eq)
