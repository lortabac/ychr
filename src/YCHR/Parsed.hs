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
    Import (..),
    Declaration (..),
    Rule (..),
    Head (..),

    -- * Re-exports from YCHR.Types
    Constraint (..),
    Term (..),
  )
where

import Data.Text (Text)
import Language.Haskell.TH.Syntax (Lift)
import YCHR.Types (Constraint (..), Term (..))

data Import
  = ModuleImport Text
  | LibraryImport Text
  deriving (Show, Eq, Lift)

data Module = Module
  { modName :: Text,
    modImports :: [Import],
    modDecls :: [Declaration],
    modRules :: [Rule],
    modExports :: Maybe [Declaration]
  }
  deriving (Show, Eq, Lift)

data Declaration = ConstraintDecl
  { declName :: Text,
    declArity :: Int
  }
  deriving (Show, Eq, Lift)

data Rule = Rule
  { ruleName :: Maybe Text,
    ruleHead :: Head,
    ruleGuard :: [Term],
    ruleBody :: [Term]
  }
  deriving (Show, Eq, Lift)

data Head
  = Simplification [Constraint]
  | Propagation [Constraint]
  | Simpagation [Constraint] [Constraint]
  deriving (Show, Eq, Lift)
