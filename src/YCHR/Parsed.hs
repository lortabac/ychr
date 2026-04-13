{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Surface Language AST
--
-- This module defines the AST that is the direct output of the parser.
-- It represents CHR programs in a form close to the Prolog-compatible
-- surface syntax, before any desugaring or semantic analysis.
--
-- Key differences from the internal AST ('YCHR.Desugared'):
--
--   * All three rule kinds (simplification, propagation, simpagation)
--     are represented explicitly, not yet desugared to simpagation.
--
--   * Guards and bodies are both lists of 'Term', with no type
--     distinction. The classification of goals into guard-specific
--     and body-specific forms happens during desugaring.
--
--   * Goals are just terms. For example, @X = Y@ is represented as
--     @CompoundTerm "=" [VarTerm "X", VarTerm "Y"]@, and @leq(X, Z)@
--     as @CompoundTerm "leq" [VarTerm "X", VarTerm "Z"]@.
--     The atom @true@ is represented as @AtomTerm "true"@.
module YCHR.Parsed
  ( -- * Source locations
    SourceLoc (..),
    Ann (..),
    noAnn,
    dummyLoc,

    -- * Annotated parsed node
    AnnP (..),
    noAnnP,

    -- * Program structure
    Module (..),
    Import (..),
    Declaration (..),
    OpType (..),
    OpDecl (..),
    Rule (..),
    Head (..),
    FunctionEquation (..),

    -- * Re-exports from YCHR.Types
    Constraint (..),
    Term (..),
    TypeDefinition (..),
    DataConstructor (..),
    TypeExpr (..),
  )
where

import Data.Text (Text)
import Language.Haskell.TH.Syntax (Lift)
import YCHR.Loc (Ann (..), SourceLoc (..), dummyLoc, noAnn)
import YCHR.PExpr (OpType (..), PExpr (..))
import YCHR.Types (Constraint (..), DataConstructor (..), Term (..), TypeDefinition (..), TypeExpr (..))

-- | A node annotated with a source location and the original 'PExpr'
-- that produced it.
data AnnP a = AnnP
  { node :: a,
    sourceLoc :: SourceLoc,
    parsed :: PExpr
  }
  deriving (Show, Eq, Lift, Functor, Foldable, Traversable)

-- | Wrap a node with a dummy source location and a dummy parsed origin.
-- Useful for constructing values in tests where provenance is irrelevant.
noAnnP :: a -> AnnP a
noAnnP x = AnnP x dummyLoc (Atom "")

data Import
  = ModuleImport Text
  | LibraryImport Text
  deriving (Show, Eq, Lift)

data Module = Module
  { name :: Text,
    imports :: [Ann Import],
    decls :: [Ann Declaration],
    typeDecls :: [Ann TypeDefinition],
    rules :: [Rule],
    equations :: [AnnP FunctionEquation],
    exports :: Maybe [Declaration]
  }
  deriving (Show, Eq, Lift)

data Declaration
  = ConstraintDecl {name :: Text, arity :: Int, argTypes :: Maybe [TypeExpr]}
  | FunctionDecl {name :: Text, arity :: Int, argTypes :: Maybe [TypeExpr], returnType :: Maybe TypeExpr}
  | OperatorDecl OpDecl
  | TypeExportDecl {name :: Text, arity :: Int}
  deriving (Show, Eq, Lift)

data OpDecl = OpDecl
  { fixity :: Int,
    opType :: OpType,
    opName :: Text
  }
  deriving (Show, Eq, Lift)

data FunctionEquation = FunctionEquation
  { funName :: Text,
    args :: [Term],
    guard :: AnnP [Term],
    rhs :: AnnP Term
  }
  deriving (Show, Eq, Lift)

data Rule = Rule
  { name :: Maybe (Ann Text),
    head :: AnnP Head,
    guard :: AnnP [Term],
    body :: AnnP [Term]
  }
  deriving (Show, Eq, Lift)

data Head
  = Simplification [Constraint]
  | Propagation [Constraint]
  | Simpagation [Constraint] [Constraint]
  deriving (Show, Eq, Lift)
