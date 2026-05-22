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
    noAnnPAt,

    -- * Program structure
    Module (..),
    Import (..),
    Declaration (..),
    FunctionDeclKind (..),
    OpType (..),
    OpDecl (..),
    Rule (..),
    Head (..),
    FunctionEquation (..),

    -- * Re-exports from YCHR.Types
    Name (..),
    Constraint (..),
    Term (..),
    TypeDefinition (..),
    DataConstructor (..),
    TypeExpr (..),
    BoundSig (..),
  )
where

import Data.Text (Text)
import YCHR.Loc (Ann (..), SourceLoc (..), dummyLoc, noAnn)
import YCHR.PExpr (OpType (..), PExpr (..))
import YCHR.Types
  ( BoundSig (..),
    Constraint (..),
    DataConstructor (..),
    Name (..),
    Term (..),
    TypeDefinition (..),
    TypeExpr (..),
  )

-- | A node annotated with a source location and the original 'PExpr'
-- that produced it.
data AnnP a = AnnP
  { node :: a,
    sourceLoc :: SourceLoc,
    parsed :: PExpr
  }
  deriving (Show, Eq, Functor, Foldable, Traversable)

-- | Wrap a node with a dummy source location and a dummy parsed origin.
-- Useful for constructing values in tests where provenance is irrelevant.
noAnnP :: a -> AnnP a
noAnnP x = AnnP x dummyLoc (Atom "")

-- | Wrap a node with a real source location but a dummy parsed origin.
-- Used by the parser to synthesize annotations (e.g. empty guard lists)
-- that have a meaningful location but no underlying surface 'PExpr'.
noAnnPAt :: SourceLoc -> a -> AnnP a
noAnnPAt loc x = AnnP x loc (Atom "")

data Import
  = ModuleImport Text (Maybe [Declaration])
  | LibraryImport Text (Maybe [Declaration])
  deriving (Show, Eq)

data Module = Module
  { name :: Text,
    -- | Source location of the @:- module(...)@ directive. For
    -- header-less files, or synthetic modules built outside the
    -- parser (DSL, query scaffolding), this is 'dummyLoc'.
    nameLoc :: SourceLoc,
    imports :: [AnnP Import],
    decls :: [Ann Declaration],
    extensionTypes :: [Ann Declaration],
    typeDecls :: [Ann TypeDefinition],
    rules :: [Rule],
    equations :: [AnnP FunctionEquation],
    -- | Equations contributed by @:- extend_function@ directives.
    -- Each must target an @:- open_function@.
    extensions :: [AnnP FunctionEquation],
    -- | Equations contributed by @:- extend_class@ directives.
    -- Each must target an @:- open_class@.
    classExtensions :: [AnnP FunctionEquation],
    exports :: Maybe (AnnP [Declaration])
  }
  deriving (Show, Eq)

-- | Whether a function-like declaration was written with the
-- @:- function@ / @:- open_function@ keyword (single signature
-- only, may carry @requiring@) or the @:- class@ / @:- open_class@
-- keyword (overloaded signatures permitted, never carries
-- @requiring@). The two forms produce the same downstream
-- 'YCHR.Resolved.FunctionDef'; the kind only affects source-level
-- validation.
data FunctionDeclKind = DKFunction | DKClass
  deriving (Show, Eq)

data Declaration
  = ConstraintDecl
      { name :: Text,
        arity :: Int,
        argTypes :: Maybe [TypeExpr],
        -- | Bounded polymorphism: a non-'Nothing' value carries the
        -- @requiring@ clause's bound signatures. Permitted only on
        -- the typed form of a constraint declaration; the parser
        -- enforces this.
        requiring :: Maybe [BoundSig]
      }
  | FunctionDecl
      { name :: Text,
        arity :: Int,
        argTypes :: Maybe [TypeExpr],
        returnType :: Maybe TypeExpr,
        isOpen :: Bool,
        kind :: FunctionDeclKind,
        -- | Bounded polymorphism: a non-'Nothing' value carries the
        -- @requiring@ clause's bound signatures. Permitted only on
        -- the @:- function@ / @:- open_function@ forms (i.e. with
        -- @kind == DKFunction@). The parser rejects @requiring@ on
        -- @:- class@ / @:- open_class@ declarations.
        requiring :: Maybe [BoundSig]
      }
  | -- | Adds an overloaded type signature to an @:- open_class@
    -- declared in another module. The renamer fills in @target@ with
    -- the class's resolved qualified name. After the rename phase,
    -- @target@ is always @Just (Qualified _ _)@; @Nothing@ only appears
    -- in the freshly-parsed AST, before the renamer has run.
    ExtendClassTypeDecl
      { name :: Text,
        arity :: Int,
        argTypes :: Maybe [TypeExpr],
        returnType :: Maybe TypeExpr,
        target :: Maybe Name
      }
  | OperatorDecl OpDecl
  | TypeExportDecl {name :: Text, arity :: Int, conExports :: Maybe [Text]}
  deriving (Show, Eq)

data OpDecl = OpDecl
  { fixity :: Int,
    opType :: OpType,
    opName :: Text
  }
  deriving (Show, Eq)

data FunctionEquation = FunctionEquation
  { funName :: Name,
    args :: [Term],
    guard :: AnnP [Term],
    rhs :: AnnP Term
  }
  deriving (Show, Eq)

data Rule = Rule
  { name :: Maybe (Ann Text),
    head :: AnnP Head,
    guard :: AnnP [Term],
    body :: AnnP [Term]
  }
  deriving (Show, Eq)

data Head
  = Simplification [Constraint]
  | Propagation [Constraint]
  | Simpagation [Constraint] [Constraint]
  deriving (Show, Eq)
