{-# LANGUAGE OverloadedStrings #-}

-- | Shared types for CHR representations.
--
-- This module contains types that are identical across the surface
-- language AST ('YCHR.Parsed') and the internal AST ('YCHR.Desugared').
module YCHR.Types
  ( -- * Constraints
    Constraint (..),
    QualifiedConstraint (..),
    ConstraintType (..),
    Identifier (..),
    QualifiedIdentifier (..),
    UnqualifiedIdentifier (..),
    Name (..),
    QualifiedName (..),

    -- * Post-HNF head constraints
    HeadConstraint (..),
    HeadArg (..),
    headArgToTerm,
    headConstraintToConstraint,

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
    qualifiedToName,
    qualifiedNameToIdentifier,

    -- * Terms
    Term (..),

    -- * Type declarations
    TypeDefinition (..),
    DataConstructor (..),
    TypeExpr (..),

    -- * Bounded polymorphism
    BoundSig (..),
  )
where

import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Text (Text)
import YCHR.Loc (SourceLoc)

-- | A numeric identifier for a constraint type, assigned by the symbol table.
newtype ConstraintType = ConstraintType {unConstraintType :: Int}
  deriving (Show, Eq, Ord)

-- | A numeric identifier for a rule, assigned in source order during
-- occurrence collection. Used as the propagation history key. Keeping
-- identity numeric (rather than textual) ensures two rules named
-- @trans@ in different modules cannot collide in the history.
newtype RuleId = RuleId {unRuleId :: Int}
  deriving (Show, Eq, Ord)

-- | A name together with its arity, identifying a constraint or function.
data Identifier = Identifier {name :: Name, arity :: Int}
  deriving (Show, Eq, Ord)

-- | An unqualified name with its arity.  Used in 'exportMap' where
-- names are looked up before qualification.
data UnqualifiedIdentifier = UnqualifiedIdentifier
  { localName :: Text,
    arity :: Int
  }
  deriving (Show, Eq, Ord)

-- | A fully-qualified name with its arity.  Used in 'exportedSet' where
-- all names are guaranteed to be module-qualified.
data QualifiedIdentifier = QualifiedIdentifier
  { moduleName :: Text,
    localName :: Text,
    arity :: Int
  }
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
  deriving (Show, Eq, Ord)

-- | A name guaranteed to be module-qualified. Established by the
-- resolve phase and propagated through 'YCHR.Resolved' and
-- 'YCHR.Desugared'. Compare with 'Name', which admits an
-- 'Unqualified' constructor used in the parser and renamer.
data QualifiedName = QualifiedName
  { moduleName :: !Text,
    baseName :: !Text
  }
  deriving (Show, Eq, Ord)

-- | Flatten a 'Name' to its surface 'Text' form. Qualified names are
-- rendered as @"Module:name"@.
flattenName :: Name -> Text
flattenName (Unqualified t) = t
flattenName (Qualified m t) = m <> ":" <> t

-- | Lift a 'QualifiedName' back to the loose 'Name' for display,
-- diagnostics, or compatibility with code that has not yet been
-- tightened.
qualifiedToName :: QualifiedName -> Name
qualifiedToName (QualifiedName m b) = Qualified m b

-- | Build an 'Identifier' from a 'QualifiedName' and arity.
qualifiedNameToIdentifier :: QualifiedName -> Int -> Identifier
qualifiedNameToIdentifier qn a = Identifier (qualifiedToName qn) a

-- | A CHR constraint occurrence.
data Constraint = Constraint
  { name :: Name,
    args :: [Term]
  }
  deriving (Show, Eq)

-- | A CHR constraint occurrence with a qualified head name. Used in
-- 'YCHR.Resolved' and 'YCHR.Desugared' rule heads and bodies, where
-- the resolve phase has guaranteed every constraint name is
-- module-qualified.
data QualifiedConstraint = QualifiedConstraint
  { name :: QualifiedName,
    args :: [Term]
  }
  deriving (Show, Eq)

-- | A head argument after Head Normal Form. The desugarer guarantees
-- that every head argument is either a variable or a wildcard;
-- non-variable patterns are lifted into 'YCHR.Desugared.GuardMatch',
-- 'YCHR.Desugared.GuardGetArg', and 'YCHR.Desugared.GuardEqual' guards
-- and replaced with fresh variables in the head. This narrower type
-- enforces that invariant.
data HeadArg
  = HeadVar Text
  | HeadWildcard
  deriving (Show, Eq)

-- | A constraint occurrence in a post-HNF rule head. Mirrors
-- 'QualifiedConstraint' but with the narrower 'HeadArg' for arguments.
data HeadConstraint = HeadConstraint
  { name :: QualifiedName,
    args :: [HeadArg]
  }
  deriving (Show, Eq)

-- | Lossless conversion from a 'HeadArg' to a 'Term'. Used at the
-- boundary with code that operates uniformly on terms (the
-- typechecker, pretty-printers).
headArgToTerm :: HeadArg -> Term
headArgToTerm (HeadVar v) = VarTerm v
headArgToTerm HeadWildcard = Wildcard

-- | Lossless conversion from a 'HeadConstraint' to a
-- 'QualifiedConstraint'.
headConstraintToConstraint :: HeadConstraint -> QualifiedConstraint
headConstraintToConstraint hc =
  QualifiedConstraint hc.name (map headArgToTerm hc.args)

-- | A CHR type declaration.
data TypeDefinition = TypeDefinition
  { name :: Name,
    typeVars :: [Text],
    constructors :: [DataConstructor],
    loc :: SourceLoc
  }
  deriving (Show, Eq)

-- | A data constructor within a type declaration.
data DataConstructor = DataConstructor
  { conName :: Name,
    conArgs :: [TypeExpr]
  }
  deriving (Show, Eq)

-- | A type expression (argument of a data constructor).
data TypeExpr
  = TypeVar Text
  | TypeCon Name [TypeExpr]
  deriving (Show, Eq)

-- | A required signature appearing inside a @requiring@ clause on a
-- bounded function or constraint declaration. Carries the same shape
-- as a function signature (name + arg types + return type) plus the
-- arity (redundant with @length argTypes@ but kept explicit so the
-- bound-graph code can compare against function declarations by
-- @(name, arity)@ without re-counting).
--
-- The 'name' field follows the same Unqualified-to-Qualified
-- progression as 'Constraint.name': the parser emits 'Unqualified',
-- the renamer rewrites it to 'Qualified', and the resolver checks
-- it against the program's declared functions.
data BoundSig = BoundSig
  { name :: Name,
    arity :: Int,
    argTypes :: [TypeExpr],
    returnType :: TypeExpr,
    loc :: SourceLoc
  }
  deriving (Show, Eq)

-- | Prolog-compatible terms.
--
-- Atoms and zero-arity compounds collapse to the same AST form
-- @CompoundTerm name []@: downstream phases (Resolve, Desugar,
-- TypeCheck, Compile) dispatch on a uniform shape. The runtime
-- representation is asymmetric — zero-arity compounds become 'VAtom'
-- for cheap allocation and comparison — but the AST keeps the
-- compound form so pattern matching stays uniform.
data Term
  = VarTerm Text
  | IntTerm Integer
  | FloatTerm Double
  | TextTerm Text
  | CompoundTerm Name [Term]
  | Wildcard
  deriving (Show, Eq)
