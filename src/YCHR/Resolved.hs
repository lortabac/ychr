{-# LANGUAGE DuplicateRecordFields #-}

-- | Resolved AST
--
-- This module defines the AST produced by the resolve phase, which sits
-- between renaming and desugaring. It is the result of flattening all
-- modules into a single program and grouping function equations under
-- their declarations.
--
-- Key properties that hold by construction:
--
--   * Function equations live inside their 'FunctionDef', so there is
--     no way for a constraint-declared name to have equations.
--
--   * Rule heads are verified during resolution: no function-declared
--     name can appear in a rule head.
--
--   * Constraint head names and function names are 'QualifiedName',
--     so the qualification invariant established by the renamer is
--     reflected in the type system.
module YCHR.Resolved
  ( Program (..),
    Rule (..),
    Head (..),
    FunctionDef (..),
    FunctionEquation (..),
  )
where

import Data.Map.Strict (Map)
import Data.Set (Set)
import Data.Text (Text)
import YCHR.Loc (Ann)
import YCHR.Parsed (AnnP)
import YCHR.Types
  ( BoundSig,
    QualifiedConstraint,
    QualifiedName,
    Term,
    TypeDefinition,
    TypeExpr,
  )

-- | A resolved program: all modules flattened, equations grouped under
-- their function declarations.
data Program = Program
  { rules :: [Rule],
    functions :: [FunctionDef],
    constraintTypes :: Map QualifiedName [TypeExpr],
    -- | Bounds declared on each @:- chr_constraint@ that carries a
    -- @requiring@ clause. Constraints without bounds do not appear in
    -- this map (rather than mapping to @[]@) so a single membership
    -- check distinguishes "bounded constraint" from "unbounded".
    constraintBounds :: Map QualifiedName [BoundSig],
    functionNames :: Set QualifiedName,
    typeDefinitions :: [TypeDefinition]
  }
  deriving (Show)

-- | A rule in the resolved AST. Structurally identical to the parsed
-- rule; the three head kinds are preserved for desugaring to flatten.
data Rule = Rule
  { name :: Maybe (Ann Text),
    head :: AnnP Head,
    guard :: AnnP [Term],
    body :: AnnP [Term]
  }
  deriving (Show)

-- | Resolved rule head. Mirrors 'YCHR.Parsed.Head' but with
-- 'QualifiedConstraint' so the constraint-name qualification invariant
-- is reflected in the type. Desugaring flattens the three kinds into
-- the uniform @kept \/ removed@ shape of 'YCHR.Desugared.Head'.
data Head
  = Simplification [QualifiedConstraint]
  | Propagation [QualifiedConstraint]
  | Simpagation [QualifiedConstraint] [QualifiedConstraint]
  deriving (Show, Eq)

-- | A function definition with its equations grouped together.
data FunctionDef = FunctionDef
  { name :: QualifiedName,
    arity :: Int,
    signatures :: [([TypeExpr], TypeExpr)],
    isOpen :: Bool,
    -- | Bounds declared on this function via @requiring@. Empty when
    -- the function is unbounded.
    requiring :: [BoundSig],
    equations :: [AnnP FunctionEquation]
  }
  deriving (Show)

-- | A function equation. Unlike 'YCHR.Parsed.FunctionEquation', there
-- is no @funName@ field — the name comes from the enclosing 'FunctionDef'.
data FunctionEquation = FunctionEquation
  { args :: [Term],
    guard :: AnnP [Term],
    rhs :: AnnP Term
  }
  deriving (Show)
