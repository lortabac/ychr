-- | Shared types for CHR representations.
--
-- This module contains types that are identical across the surface
-- language AST ('YCHR.Parsed') and the internal AST ('YCHR.Desugared').
module YCHR.Types
  ( -- * Constraints
    Constraint (..),
    ConstraintType (..),
    Identifier (..),
    Name (..),

    -- * Symbol table
    SymbolTable,
    mkSymbolTable,
    lookupSymbol,
    symbolTableToList,
    symbolTableSize,

    -- * Terms
    Term (..),
  )
where

import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Text (Text)
import Language.Haskell.TH.Syntax (Lift)

-- | A numeric identifier for a constraint type, assigned by the symbol table.
newtype ConstraintType = ConstraintType {unConstraintType :: Int}
  deriving (Show, Eq, Ord)

-- | A name together with its arity, identifying a constraint or function.
data Identifier = Identifier {name :: Name, arity :: Int}
  deriving (Show, Eq, Ord)

-- | Maps identifiers (name + arity) to unique 0-indexed numeric IDs.
newtype SymbolTable = SymbolTable (Map Identifier ConstraintType)
  deriving (Show, Eq)

mkSymbolTable :: [(Identifier, ConstraintType)] -> SymbolTable
mkSymbolTable = SymbolTable . Map.fromList

lookupSymbol :: Identifier -> SymbolTable -> Maybe ConstraintType
lookupSymbol n (SymbolTable m) = Map.lookup n m

symbolTableToList :: SymbolTable -> [(Identifier, ConstraintType)]
symbolTableToList (SymbolTable m) = Map.toList m

symbolTableSize :: SymbolTable -> Int
symbolTableSize (SymbolTable m) = Map.size m

-- | Represents a name that can be either raw or module-qualified.
data Name
  = -- | e.g., "leq"
    Unqualified Text
  | -- | e.g., "Order", "leq"
    Qualified Text Text
  deriving (Show, Eq, Ord, Lift)

-- | A CHR constraint occurrence.
data Constraint = Constraint
  { name :: Name,
    args :: [Term]
  }
  deriving (Show, Eq, Lift)

-- | Prolog-compatible terms.
data Term
  = VarTerm Text
  | IntTerm Int
  | AtomTerm Text
  | TextTerm Text
  | CompoundTerm Name [Term]
  | Wildcard
  deriving (Show, Eq, Lift)
