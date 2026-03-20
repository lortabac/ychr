-- | Shared types for CHR representations.
--
-- This module contains types that are identical across the surface
-- language AST ('CHR.Surface') and the internal AST ('CHR.AST').

module YCHR.Types
  ( -- * Constraints
    Constraint (..)

    -- * Terms
  , Term (..)
  ) where


-- | A CHR constraint occurrence: a constraint name applied to arguments.
data Constraint = Constraint
  { conName :: String   -- ^ Constraint name (e.g., "leq")
  , conArgs :: [Term]   -- ^ Constraint arguments
  }
  deriving (Show, Eq)


-- | Prolog-compatible terms.
data Term
  = VarTerm String              -- ^ A variable (e.g., @X@, @Y1@)
  | IntTerm Int                 -- ^ An integer literal
  | AtomTerm String             -- ^ An atom (symbolic constant, e.g., @foo@, @add@)
  | CompoundTerm String [Term]  -- ^ A compound term: functor applied to arguments
                                --   (e.g., @f(X, g(Y))@)
  deriving (Show, Eq)
