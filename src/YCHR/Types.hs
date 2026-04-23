{-# LANGUAGE OverloadedStrings #-}

-- | Shared types for CHR representations.
--
-- This module contains types that are identical across the surface
-- language AST ('YCHR.Parsed') and the internal AST ('YCHR.Desugared').
module YCHR.Types
  ( -- * Constraints
    Constraint (..),
    ConstraintType (..),
    Identifier (..),
    QualifiedIdentifier (..),
    UnqualifiedIdentifier (..),
    Name (..),

    -- * Rules
    RuleId (..),

    -- * Symbol table
    SymbolTable,
    mkSymbolTable,
    lookupSymbol,
    symbolTableToList,
    symbolTableSize,

    -- * Name helpers
    flattenName,

    -- * Terms
    Term (..),

    -- * Type declarations
    TypeDefinition (..),
    DataConstructor (..),
    TypeExpr (..),
  )
where

import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Text (Text)
import Language.Haskell.TH.Syntax (Lift)

-- | A numeric identifier for a constraint type, assigned by the symbol table.
newtype ConstraintType = ConstraintType {unConstraintType :: Int}
  deriving (Show, Eq, Ord, Lift)

-- | A numeric identifier for a rule, assigned in source order during
-- occurrence collection. Used as the propagation history key. Keeping
-- identity numeric (rather than textual) ensures two rules named
-- @trans@ in different modules cannot collide in the history.
newtype RuleId = RuleId {unRuleId :: Int}
  deriving (Show, Eq, Ord, Lift)

-- | A name together with its arity, identifying a constraint or function.
data Identifier = Identifier {name :: Name, arity :: Int}
  deriving (Show, Eq, Ord, Lift)

-- | An unqualified name with its arity.  Used in 'exportMap' where
-- names are looked up before qualification.
data UnqualifiedIdentifier = UnqualifiedIdentifier
  { localName :: Text,
    arity :: Int
  }
  deriving (Show, Eq, Ord, Lift)

-- | A fully-qualified name with its arity.  Used in 'exportedSet' where
-- all names are guaranteed to be module-qualified.
data QualifiedIdentifier = QualifiedIdentifier
  { moduleName :: Text,
    localName :: Text,
    arity :: Int
  }
  deriving (Show, Eq, Ord, Lift)

-- | Maps identifiers (name + arity) to unique 0-indexed numeric IDs.
newtype SymbolTable = SymbolTable (Map Identifier ConstraintType)
  deriving (Show, Eq, Lift)

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

-- | Flatten a 'Name' to its surface 'Text' form. Qualified names are
-- rendered as @"Module:name"@.
flattenName :: Name -> Text
flattenName (Unqualified t) = t
flattenName (Qualified m t) = m <> ":" <> t

-- | A CHR constraint occurrence.
data Constraint = Constraint
  { name :: Name,
    args :: [Term]
  }
  deriving (Show, Eq, Lift)

-- | A CHR type declaration.
data TypeDefinition = TypeDefinition
  { name :: Name,
    typeVars :: [Text],
    constructors :: [DataConstructor]
  }
  deriving (Show, Eq, Lift)

-- | A data constructor within a type declaration.
data DataConstructor = DataConstructor
  { conName :: Name,
    conArgs :: [TypeExpr]
  }
  deriving (Show, Eq, Lift)

-- | A type expression (argument of a data constructor).
data TypeExpr
  = TypeVar Text
  | TypeCon Name [TypeExpr]
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
