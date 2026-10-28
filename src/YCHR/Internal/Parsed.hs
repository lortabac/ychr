{-# LANGUAGE OverloadedStrings #-}

-- | Surface Language AST
--
-- This module defines the AST that is the direct output of the parser.
-- It represents CHR programs in a form close to the Prolog-compatible
-- surface syntax, before any desugaring or semantic analysis.
--
-- Key differences from the internal AST ('YCHR.Internal.Desugared'):
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
--     The atom @true@ is represented as
--     @CompoundTerm (Unqualified "true") []@.
module YCHR.Internal.Parsed
  ( -- * Source locations
    SourceLoc (..),
    Ann (..),
    noAnn,
    dummyLoc,

    -- * Annotated parsed node
    AnnP (..),
    noAnnP,
    noAnnPAt,
    Site (..),
    siteOf,
    namePExpr,
    annAt,

    -- * Program structure
    Module (..),
    Import (..),
    Declaration (..),
    ConstraintDeclBody (..),
    FunctionDeclBody (..),
    ExtendClassTypeDeclBody (..),
    TypeExportDeclBody (..),
    InlineDecl (..),
    ConstraintUseDecl (..),
    FunctionDeclKind (..),
    OpType (..),
    OpDecl (..),
    Rule (..),
    Head (..),
    headAggregates,
    FunctionEquation (..),
    MacroDef (..),
    MacroKind (..),
    MacroClause (..),
    MacroExportDeclBody (..),
    ExpansionStep (..),

    -- * Re-exports from YCHR.Internal.Types
    Name (..),
    Constraint (..),
    ConstraintUse (..),
    Term (..),
    TypeDefinition (..),
    TypeKind (..),
    typeConstructors,
    DataConstructor (..),
    TypeExpr (..),
    BoundSig (..),
    Aggregate (..),
    AggregateKind (..),
    AggregateConjunct (..),
  )
where

import Data.List.NonEmpty (NonEmpty)
import Data.Text (Text)
import YCHR.Internal.Loc (Ann (..), SourceLoc (..), dummyLoc, noAnn)
import YCHR.Internal.PExpr (OpDecl (..), OpType (..), PExpr (..))
import YCHR.Internal.Types
  ( Aggregate (..),
    AggregateConjunct (..),
    AggregateKind (..),
    BoundSig (..),
    Constraint (..),
    ConstraintUse (..),
    DataConstructor (..),
    Name (..),
    Term (..),
    TypeDefinition (..),
    TypeExpr (..),
    TypeKind (..),
    typeConstructors,
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

-- | Where a diagnostic points: a source location and the 'PExpr'
-- written there. An 'AnnP' without its node.
data Site = Site
  { loc :: SourceLoc,
    origin :: PExpr
  }

-- | The site of an annotated node.
siteOf :: AnnP a -> Site
siteOf a = Site a.sourceLoc a.parsed

-- | A name as written, for a diagnostic's node line: @n@ or @m:n@.
namePExpr :: Name -> PExpr
namePExpr (Unqualified n) = Atom n
namePExpr (Qualified m n) = Compound ":" [noAnn (Atom m), noAnn (Atom n)]

-- | Annotate a node with a site.
annAt :: Site -> a -> AnnP a
annAt s x = AnnP x s.loc s.origin

-- | A @use_module@ target: a module name or @library(name)@, plus its
-- optional item list.
data Import
  = ModuleImport Text (Maybe [Declaration])
  | LibraryImport Text (Maybe [Declaration])
  deriving (Show, Eq)

-- | A parsed CHR module: header, imports, declarations, rules, and
-- equations.
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
    -- | @:- inline name\/arity, ...@ directives naming functions, declared
    -- elsewhere in this same module, whose calls should be substituted
    -- inline at eligible call sites. See 'YCHR.Internal.Desugar.Inline'.
    inlines :: [Ann InlineDecl],
    -- | @:- constraint_use Tag(name\/arity), ...@ entries naming
    -- constraints declared elsewhere in this same module. See
    -- 'YCHR.Internal.Resolve.checkConstraintUseDeclarations' and
    -- "YCHR.Internal.ConstraintUse".
    constraintUses :: [Ann ConstraintUseDecl],
    -- | @:- macro Name(V1, ..., Vn) ---> Body.@ definitions. See
    -- 'YCHR.Internal.Rename.Macro' and
    -- [the macro reference](../../docs/reference/macros.md).
    macros :: [AnnP MacroDef],
    exports :: Maybe (AnnP [Declaration])
  }
  deriving (Show, Eq)

-- | Whether a function-like declaration was written with the
-- @:- function@ / @:- open_function@ keyword (single signature
-- only, may carry @requiring@ or @refining@) or the @:- class@ /
-- @:- open_class@ keyword (overloaded signatures permitted, never
-- carries either clause). The two forms produce the same downstream
-- 'YCHR.Internal.Resolved.FunctionDef'; the kind only affects source-level
-- validation.
data FunctionDeclKind = DKFunction | DKClass
  deriving (Show, Eq)

-- | Fields of a @:- chr_constraint@ declaration.
data ConstraintDeclBody = ConstraintDeclBody
  { name :: Text,
    arity :: Int,
    argTypes :: Maybe [TypeExpr],
    -- | Bounded polymorphism: a non-'Nothing' value carries the
    -- @requiring@ clause's bound signatures. Permitted only on
    -- the typed form of a constraint declaration; the parser
    -- enforces this.
    requiring :: Maybe [BoundSig]
  }
  deriving (Show, Eq)

-- | Fields of a function-like declaration (@:- function@,
-- @:- open_function@, @:- class@, @:- open_class@).
data FunctionDeclBody = FunctionDeclBody
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
    requiring :: Maybe [BoundSig],
    -- | Refinement predicate: a non-'Nothing' value carries the
    -- @refining@ clause's refined type. Permitted only on a
    -- closed @:- function@ whose single typed signature has the
    -- shape @name(any) -> bool@; the refined type must be a base
    -- type or a type constructor applied to distinct type
    -- variables. Resolve validates all of this and reports
    -- @YCHR-16021@.
    refining :: Maybe TypeExpr
  }
  deriving (Show, Eq)

-- | Fields of an @:- extend_class_type@ declaration: it adds an
-- overloaded type signature to an @:- open_class@ declared in another
-- module. The renamer fills in @target@ with the class's resolved
-- qualified name. After the rename phase, @target@ is always
-- @Just (Qualified _ _)@; @Nothing@ only appears in the freshly-parsed
-- AST, before the renamer has run. @name@ is the target as written,
-- and may be qualified.
data ExtendClassTypeDeclBody = ExtendClassTypeDeclBody
  { name :: Name,
    arity :: Int,
    argTypes :: Maybe [TypeExpr],
    returnType :: Maybe TypeExpr,
    target :: Maybe Name
  }
  deriving (Show, Eq)

-- | Fields of a type entry in a module's export or import list, written
-- @type(T/n)@ or @type(T/n, [Con, ...])@. Covers both algebraic and
-- opaque types: they share one type namespace, so a single export
-- form is used. Opaque types have no constructors, so a constructor
-- allowlist on one is rejected by the usual unknown-constructor
-- check (@YCHR-20008@).
data TypeExportDeclBody = TypeExportDeclBody
  { name :: Text,
    arity :: Int,
    conExports :: Maybe [Text]
  }
  deriving (Show, Eq)

-- | One @name\/arity@ entry of an @:- inline@ directive. Unlike
-- 'FunctionDeclBody', the name is never qualified: an @:- inline@
-- directive only ever targets a function declared by the same
-- module (see 'YCHR.Internal.Resolve.checkInlineDeclarations').
data InlineDecl = InlineDecl
  { name :: Text,
    arity :: Int
  }
  deriving (Show, Eq)

-- | One @Tag(name\/arity)@ entry of a @:- constraint_use@ directive.
-- Like 'InlineDecl', the name is never qualified: the directive only
-- ever targets a constraint declared by the same module (see
-- 'YCHR.Internal.Resolve.checkConstraintUseDeclarations').
data ConstraintUseDecl = ConstraintUseDecl
  { use :: ConstraintUse,
    name :: Text,
    arity :: Int
  }
  deriving (Show, Eq)

-- | A macro: its kind, name and arity, and its clauses in source order.
--
-- A macro comes either from a one-line definition
-- (@:- macro Head ---> [Goals].@ or @:- macro_decls Head ---> [Clauses].@,
-- exactly one clause) or from a declaration (@:- macro Name\/N.@ or
-- @:- macro_decls Name\/N.@) together with the top-level
-- @Head ---> [...].@ clauses of the same @Name\/N@. The parser groups
-- the clauses; a declaration with no clauses has an empty 'clauses'
-- list, and every use of it fails to match. See
-- [the macro reference](../../docs/reference/macros.md).
data MacroDef = MacroDef
  { kind :: MacroKind,
    name :: Text,
    arity :: Int,
    clauses :: [AnnP MacroClause]
  }
  deriving (Show, Eq)

-- | Macro kinds. Goal macros (@:- macro@) expand to goals, in the
-- renamer. Declaration macros (@:- macro_decls@) are directives and
-- expand to clauses before conversion (see "YCHR.Internal.DeclMacro").
data MacroKind = GoalMacro | DeclMacro
  deriving (Show, Eq, Ord)

-- | One clause of a macro: @Name(P1, ..., Pn) ---> [E1, ..., Ek].@
--
-- 'params' are the head's argument /patterns/, matched syntactically
-- against the arguments of a use (see
-- 'YCHR.Internal.Rename.Macro.matchClause'). 'body' holds the elements
-- of the body list, kept exactly as written: they are not checked when
-- the macro is defined, since whether an expansion is valid depends on
-- where it is used. Elements are goals (goal macro) or clauses
-- (declaration macro), stored as 'Term's either way.
data MacroClause = MacroClause
  { params :: [Term],
    body :: [Term]
  }
  deriving (Show, Eq)

-- | One step of the chain that generated a clause: the macro and the
-- outermost directive's location. Generated rules and equations keep
-- the chain (innermost first) so later errors can show it.
data ExpansionStep = ExpansionStep
  { macroModule :: Text,
    macroName :: Text,
    macroArity :: Int,
    site :: SourceLoc
  }
  deriving (Show, Eq)

-- | Fields of a @macro(Name\/Arity)@ entry in a module's export or
-- import list. Like 'TypeExportDeclBody', this describes an
-- export\/import-list item rather than a declaration of a name in the
-- constraint\/function namespace; the parser only produces it for
-- those lists.
data MacroExportDeclBody = MacroExportDeclBody
  { name :: Text,
    arity :: Int
  }
  deriving (Show, Eq)

-- | A parsed declaration item.
--
-- Each constructor carries its fields in a dedicated single-constructor
-- record rather than declaring them on 'Declaration' itself. A field
-- shared by only some of the alternatives would make its projection
-- partial ('-Wincomplete-record-selectors'), so keeping the records
-- separate makes every field total. Pattern-match the constructor and
-- project from the payload.
--
-- 'OperatorDecl' and 'TypeExportDecl' describe entries of a module's
-- export or import list rather than declarations of a name in the
-- constraint/function namespace; the parser only produces them for
-- those lists.
data Declaration
  = ConstraintDecl ConstraintDeclBody
  | FunctionDecl FunctionDeclBody
  | ExtendClassTypeDecl ExtendClassTypeDeclBody
  | OperatorDecl OpDecl
  | TypeExportDecl TypeExportDeclBody
  | MacroExportDecl MacroExportDeclBody
  deriving (Show, Eq)

-- | A function equation: @lhs [| guard] -> rhs@.
data FunctionEquation = FunctionEquation
  { funName :: Name,
    args :: [Term],
    guard :: AnnP [Term],
    rhs :: AnnP (NonEmpty Term),
    -- | Declaration macros that generated this equation, innermost
    -- first. Empty if the user wrote it.
    expansion :: [ExpansionStep]
  }
  deriving (Show, Eq)

-- | A CHR rule: optional name, head, guard, and body.
data Rule = Rule
  { name :: Maybe (Ann Text),
    head :: AnnP Head,
    guard :: AnnP [Term],
    body :: AnnP [Term],
    -- | Declaration macros that generated this rule, innermost first.
    -- Empty if the user wrote it.
    expansion :: [ExpansionStep]
  }
  deriving (Show, Eq)

-- | A rule head: the constraints to match, split by rule kind, plus the
-- rule's aggregates.
--
-- The parser never produces an aggregate — it sees only the @Term@s a
-- macro expanded to — so a freshly parsed head has an empty
-- 'aggregates' list. The renamer fills it in when it recognizes the
-- aggregate core form or a selection form. See
-- docs/reference/aggregates.md.
data Head
  = Simplification [Constraint] [Aggregate]
  | Propagation [Constraint] [Aggregate]
  | Simpagation [Constraint] [Constraint] [Aggregate]
  deriving (Show, Eq)

-- | The aggregates of a head, whichever kind it is.
headAggregates :: Head -> [Aggregate]
headAggregates (Simplification _ aggs) = aggs
headAggregates (Propagation _ aggs) = aggs
headAggregates (Simpagation _ _ aggs) = aggs
