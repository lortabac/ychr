{-# LANGUAGE DuplicateRecordFields #-}

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
import YCHR.Types (Constraint (..), DataConstructor (..), Term (..), TypeDefinition (..), TypeExpr (..))

-- | A source file location (file, line, column).
data SourceLoc = SourceLoc
  { file :: String,
    line :: Int,
    col :: Int
  }
  deriving (Show, Eq, Lift)

-- | A value annotated with a source location.
data Ann a = Ann
  { node :: a,
    sourceLoc :: SourceLoc
  }
  deriving (Show, Eq, Lift, Functor, Foldable, Traversable)

-- | A dummy source location for programmatically-constructed nodes.
dummyLoc :: SourceLoc
dummyLoc = SourceLoc "<generated>" 1 1

-- | Wrap a value with a dummy source location.
noAnn :: a -> Ann a
noAnn x = Ann x dummyLoc

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
    equations :: [Ann FunctionEquation],
    exports :: Maybe [Declaration]
  }
  deriving (Show, Eq, Lift)

data Declaration
  = ConstraintDecl {name :: Text, arity :: Int}
  | FunctionDecl {name :: Text, arity :: Int}
  | OperatorDecl OpDecl
  deriving (Show, Eq, Lift)

data OpType
  = InfixL_
  | InfixR_
  | InfixN_
  | Prefix_
  | Postfix_
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
    guard :: Ann [Term],
    rhs :: Ann Term
  }
  deriving (Show, Eq, Lift)

data Rule = Rule
  { name :: Maybe (Ann Text),
    head :: Ann Head,
    guard :: Ann [Term],
    body :: Ann [Term]
  }
  deriving (Show, Eq, Lift)

data Head
  = Simplification [Constraint]
  | Propagation [Constraint]
  | Simpagation [Constraint] [Constraint]
  deriving (Show, Eq, Lift)
