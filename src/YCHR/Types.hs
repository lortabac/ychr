-- | Shared types for CHR representations.
--
-- This module contains types that are identical across the surface
-- language AST ('CHR.Surface') and the internal AST ('CHR.AST').
module YCHR.Types
  ( -- * Constraints
    Constraint (..),

    -- * Terms
    Term (..),
  )
where

-- | A CHR constraint occurrence: a constraint name applied to arguments.
data Constraint = Constraint
  { -- | Constraint name (e.g., "leq")
    conName :: String,
    -- | Constraint arguments
    conArgs :: [Term]
  }
  deriving (Show, Eq)

-- | Prolog-compatible terms.
data Term
  = -- | A variable (e.g., @X@, @Y1@)
    VarTerm String
  | -- | An integer literal
    IntTerm Int
  | -- | An atom (symbolic constant, e.g., @foo@, @add@)
    AtomTerm String
  | -- | A compound term: functor applied to arguments
    --   (e.g., @f(X, g(Y))@)
    CompoundTerm String [Term]
  deriving (Show, Eq)
