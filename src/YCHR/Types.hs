-- | Shared types for CHR representations.
--
-- This module contains types that are identical across the surface
-- language AST ('YCHR.Parsed') and the internal AST ('YCHR.Desugared').
module YCHR.Types
  ( -- * Constraints
    Constraint (..),
    ConstraintType (..),
    Name (..),

    -- * Terms
    Term (..),
  )
where

import Data.Text (Text)

-- | A numeric identifier for a constraint type, assigned by the symbol table.
newtype ConstraintType = ConstraintType {unConstraintType :: Int}
  deriving (Show, Eq, Ord)

-- | Represents a name that can be either raw or module-qualified.
data Name
  = -- | e.g., "leq"
    Unqualified Text
  | -- | e.g., "Order", "leq"
    Qualified Text Text
  deriving (Show, Eq, Ord)

-- | A CHR constraint occurrence.
data Constraint = Constraint
  { conName :: Name,
    conArgs :: [Term]
  }
  deriving (Show, Eq)

-- | Prolog-compatible terms.
data Term
  = VarTerm Text
  | IntTerm Int
  | AtomTerm Text
  | CompoundTerm Name [Term]
  | Wildcard
  deriving (Show, Eq)
