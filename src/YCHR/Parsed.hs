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
  ( -- * Program structure
    Module (..),
    Declaration (..),
    Rule (..),
    Head (..),

    -- * Re-exports from YCHR.Types
    Constraint (..),
    Term (..),
  )
where

import YCHR.Types (Constraint (..), Term (..))

data Module = Module
  { modName :: String,
    modImports :: [String],
    modDecls :: [Declaration],
    modRules :: [Rule]
  }
  deriving (Show, Eq)

data Declaration = ConstraintDecl
  { declName :: String,
    declArity :: Int
  }
  deriving (Show, Eq)

data Rule = Rule
  { ruleName :: Maybe String,
    ruleHead :: Head,
    ruleGuard :: [Term],
    ruleBody :: [Term]
  }
  deriving (Show, Eq)

data Head
  = Simplification [Constraint]
  | Propagation [Constraint]
  | Simpagation [Constraint] [Constraint]
  deriving (Show, Eq)
