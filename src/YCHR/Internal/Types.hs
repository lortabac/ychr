{-# LANGUAGE OverloadedStrings #-}

-- | Shared types for CHR representations.
--
-- This module contains types that are identical across the surface
-- language AST ('YCHR.Internal.Parsed') and the internal AST
-- ('YCHR.Internal.Desugared'). The embedder-facing subset ('Term',
-- 'Name', 'Constraint', and the type-declaration vocabulary) is
-- re-exported from "YCHR.Types", which is the module covered by the
-- package version policy; everything else here is compiler-internal.
module YCHR.Internal.Types
  ( -- * Constraints
    Constraint (..),
    QualifiedConstraint (..),
    ConstraintType (..),
    Identifier (..),
    QualifiedIdentifier (..),
    UnqualifiedIdentifier (..),
    Name (..),
    QualifiedName (..),
    ConstraintKey (..),

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
    unqualifiedText,
    qualifiedToName,
    qualifiedNameToIdentifier,
    preludeBool,
    hostBool,

    -- * Terms
    Term (..),

    -- * Type declarations
    TypeDefinition (..),
    TypeKind (..),
    typeConstructors,
    DataConstructor (..),
    TypeExpr (..),

    -- * Bounded polymorphism
    BoundSig (..),
  )
where

import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Text (Text)
import YCHR.Internal.Loc (SourceLoc)

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

-- | Build a 'SymbolTable' from identifier\/ID pairs. Later entries win on
-- a duplicate 'Identifier', following 'Map.fromList'.
mkSymbolTable :: [(Identifier, ConstraintType)] -> SymbolTable
mkSymbolTable = SymbolTable . Map.fromList

-- | Look up the 'ConstraintType' assigned to an identifier, or 'Nothing'
-- if the constraint is not in the table.
lookupSymbol :: Identifier -> SymbolTable -> Maybe ConstraintType
lookupSymbol n (SymbolTable m) = Map.lookup n m

-- | All entries, ordered by 'Identifier' (name, then arity) — /not/ by
-- 'ConstraintType' index. Sort on the ID when index order matters.
symbolTableToList :: SymbolTable -> [(Identifier, ConstraintType)]
symbolTableToList (SymbolTable m) = Map.toList m

-- | Number of distinct constraints in the table. Because IDs are
-- 0-indexed and contiguous, this is also one past the largest
-- 'ConstraintType' — the store's pre-allocation size.
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
-- resolve phase and propagated through 'YCHR.Internal.Resolved' and
-- 'YCHR.Internal.Desugared'. Compare with 'Name', which admits an
-- 'Unqualified' constructor used in the parser and renamer.
data QualifiedName = QualifiedName
  { moduleName :: !Text,
    baseName :: !Text
  }
  deriving (Show, Eq, Ord)

-- | Key of the per-constraint declaration maps (@constraintTypes@,
-- @constraintBounds@). Constraints are arity-overloadable, so the
-- name alone does not identify a declaration: keying by name let an
-- arity-overloaded constraint shadow its sibling's declared types.
data ConstraintKey = ConstraintKey
  { name :: !QualifiedName,
    arity :: !Int
  }
  deriving (Show, Eq, Ord)

-- | Flatten a 'Name' to its surface 'Text' form. Qualified names are
-- rendered as @"Module:name"@.
flattenName :: Name -> Text
flattenName (Unqualified t) = t
flattenName (Qualified m t) = m <> ":" <> t

-- | The base (module-less) part of a 'Name'. Unlike 'flattenName' this
-- discards the qualifier rather than rendering it, which is what
-- name-keyed environments and same-name checks want: a name means the
-- same thing to those whether or not a phase has already qualified it.
unqualifiedText :: Name -> Text
unqualifiedText (Unqualified t) = t
unqualifiedText (Qualified _ t) = t

-- | Lift a 'QualifiedName' back to the loose 'Name' for display,
-- diagnostics, or compatibility with code that has not yet been
-- tightened.
qualifiedToName :: QualifiedName -> Name
qualifiedToName (QualifiedName m b) = Qualified m b

-- | Build an 'Identifier' from a 'QualifiedName' and arity.
qualifiedNameToIdentifier :: QualifiedName -> Int -> Identifier
qualifiedNameToIdentifier qn a = Identifier (qualifiedToName qn) a

-- | The two prelude data constructors that are represented as a native
-- boolean rather than as an atom, on every backend.
--
-- Only the renamer-canonicalized qualified form counts: the renamer
-- rewrites a bare @true@ \/ @false@ to @prelude:true@ \/ @prelude:false@
-- in every position, expression and pattern alike (see
-- 'YCHR.Internal.Rename.canonicalizeDataCon'). An @Unqualified@ spelling
-- that survived canonicalization is an ambiguous or user-declared
-- constructor and stays an ordinary atom.
--
-- This is the single statement of that correspondence for the
-- renamed-AST consumers: both sides of the compiler (value and
-- pattern), the query evaluator, and the Scheme driver. Keeping it in
-- one place is what stops the two sides from disagreeing about the
-- representation. The host-value bridges ('YCHR.Convert',
-- 'YCHR.DSL', 'YCHR.Internal.Meta') deal in the unqualified spelling
-- and are deliberately not covered.
preludeBool :: Name -> Maybe Bool
preludeBool (Qualified "prelude" "true") = Just True
preludeBool (Qualified "prelude" "false") = Just False
preludeBool _ = Nothing

-- | The bool constructors as they arrive from /outside/ the renamer:
-- built by a host program through "YCHR.Convert" or "YCHR.DSL", or
-- parsed straight to a 'Term' by @read_term_from_string@. Such a term
-- never passes through 'YCHR.Internal.Rename.canonicalizeDataCon', so
-- it carries the bare @true@ \/ @false@ the host wrote; this accepts
-- that spelling on top of the canonical one 'preludeBool' recognizes.
--
-- Use this only at the host-value bridge
-- ('YCHR.Internal.Meta.termToValue'). Everything downstream of the
-- renamer must use 'preludeBool' instead, because /there/ a surviving
-- unqualified @true@ means an ambiguous or user-declared constructor
-- and stays an atom. The corollary is a corner this cannot resolve: a
-- module that declares its own @true\/0@ constructor cannot carry it
-- across the bridge, since nothing in a host-built term distinguishes
-- it from the boolean.
hostBool :: Name -> Maybe Bool
hostBool (Unqualified "true") = Just True
hostBool (Unqualified "false") = Just False
hostBool name = preludeBool name

-- | A CHR constraint occurrence.
data Constraint = Constraint
  { name :: Name,
    args :: [Term]
  }
  deriving (Show, Eq)

-- | A CHR constraint occurrence with a qualified head name. Used in
-- 'YCHR.Internal.Resolved' and 'YCHR.Internal.Desugared' rule heads and bodies, where
-- the resolve phase has guaranteed every constraint name is
-- module-qualified.
data QualifiedConstraint = QualifiedConstraint
  { name :: QualifiedName,
    args :: [Term]
  }
  deriving (Show, Eq)

-- | A head argument after Head Normal Form. The desugarer guarantees
-- that every head argument is either a variable or a wildcard;
-- non-variable patterns are lifted into 'YCHR.Internal.Desugared.GuardMatch',
-- 'YCHR.Internal.Desugared.GuardGetArg', and 'YCHR.Internal.Desugared.GuardEqual' guards
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
    kind :: TypeKind,
    loc :: SourceLoc
  }
  deriving (Show, Eq)

-- | The kind of a type declaration.
--
-- An 'Algebraic' type is declared with @:- chr_type@ and carries one or
-- more data constructors. An 'Opaque' type is declared with
-- @:- opaque_type@, is nominal, and has no data constructors — its
-- values are introduced and eliminated only by (host-backed) functions.
-- Encoding opacity as a sum makes "opaque implies no constructors"
-- unrepresentable rather than a runtime invariant.
data TypeKind
  = Algebraic [DataConstructor]
  | Opaque
  deriving (Show, Eq)

-- | The data constructors of a type definition: the declared
-- constructors for an 'Algebraic' type, and none for an 'Opaque' type.
typeConstructors :: TypeDefinition -> [DataConstructor]
typeConstructors td = case td.kind of
  Algebraic cs -> cs
  Opaque -> []

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
-- The 'Ord' instance carries no semantic meaning — it exists so that a
-- 'Term' can key a 'Data.Map.Map' or inhabit a 'Data.Set.Set'. Structural
-- CHR equality on /runtime/ values is 'YCHR.Run.equal', not this instance.
--
-- Caveat: it inherits 'Double''s NaN behaviour, so it is not a total
-- order. A @'FloatTerm' nan@ (reachable from CHR — @R is 0.0 \/ 0.0@)
-- compares unequal to itself, which breaks the 'Data.Map.Map' and
-- 'Data.Set.Set' invariants for that one key: the term cannot be looked
-- up again, and a set will hold duplicates of it. Filter or normalize
-- NaN before using a 'Term' as a key if floats can reach it.
data Term
  = VarTerm Text
  | IntTerm Integer
  | FloatTerm Double
  | TextTerm Text
  | CompoundTerm Name [Term]
  | Wildcard
  deriving (Show, Eq, Ord)
