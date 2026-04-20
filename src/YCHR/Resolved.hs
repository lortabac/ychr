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
module YCHR.Resolved
  ( Program (..),
    Rule (..),
    FunctionDef (..),
    FunctionEquation (..),
  )
where

import Data.Map.Strict (Map)
import Data.Set (Set)
import Data.Text (Text)
import YCHR.Loc (Ann)
import YCHR.Parsed (AnnP, Head)
import YCHR.Types (Name, Term, TypeDefinition, TypeExpr)

-- | A resolved program: all modules flattened, equations grouped under
-- their function declarations.
data Program = Program
  { rules :: [Rule],
    functions :: [FunctionDef],
    constraintTypes :: Map Name [TypeExpr],
    functionNames :: Set Name,
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

-- | A function definition with its equations grouped together.
data FunctionDef = FunctionDef
  { name :: Name,
    arity :: Int,
    argTypes :: Maybe [TypeExpr],
    returnType :: Maybe TypeExpr,
    isOpen :: Bool,
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
