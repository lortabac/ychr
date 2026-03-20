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
    Program (..),
    Declaration (..),
    Rule (..),
    Head (..),

    -- * Re-exports from YCHR.Types
    Constraint (..),
    Term (..),
  )
where

import YCHR.Types (Constraint (..), Term (..))

-- | A surface-level CHR program: declarations followed by rules.
data Program = Program
  { -- | Constraint declarations
    progDeclarations :: [Declaration],
    -- | CHR rules
    progRules :: [Rule]
  }
  deriving (Show, Eq)

-- | A constraint declaration, specifying the constraint's name and arity.
--
-- Corresponds to surface syntax like:
--
-- > :- constraint leq/2.
-- > :- constraint mem/2, pc/1, prog/4.
data Declaration = ConstraintDecl
  { -- | Constraint name
    declName :: String,
    -- | Number of arguments
    declArity :: Int
  }
  deriving (Show, Eq)

-- | A CHR rule with explicit rule kind.
--
-- Corresponds to surface syntax like:
--
-- > reflexivity @ leq(X, X) <=> true.
-- > transitivity @ leq(X, Y), leq(Y, Z) ==> leq(X, Z).
-- > idempotence @ leq(X, Y) \ leq(X, Y) <=> true.
data Rule = Rule
  { -- | Optional rule name (before @\@@)
    ruleName :: Maybe String,
    -- | Head constraints with rule kind
    ruleHead :: Head,
    -- | Guard conditions (unclassified terms)
    ruleGuard :: [Term],
    -- | Body goals (unclassified terms)
    ruleBody :: [Term]
  }
  deriving (Show, Eq)

-- | The head of a CHR rule, with explicit rule kind.
data Head
  = -- | All head constraints are removed.
    --
    -- > h1, ..., hn <=> guard | body.
    Simplification [Constraint]
  | -- | All head constraints are kept.
    --
    -- > h1, ..., hn ==> guard | body.
    Propagation [Constraint]
  | -- | Some constraints kept, some removed.
    --
    -- > kept1, ..., keptn \ removed1, ..., removedn <=> guard | body.
    Simpagation [Constraint] [Constraint]
  deriving (Show, Eq)
