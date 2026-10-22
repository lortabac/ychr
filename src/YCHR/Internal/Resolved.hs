{-# LANGUAGE OverloadedStrings #-}

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
module YCHR.Internal.Resolved
  ( -- * Types
    Program (..),
    Rule (..),
    Head (..),
    headAggregates,
    Aggregate (..),
    AggregateConjunct (..),
    FunctionDef (..),
    FunctionEquation (..),
    Expr (..),

    -- * Limits
    maxCallArity,
    maxTellArity,

    -- * Operations
    exprToTerm,
  )
where

import Data.List.NonEmpty (NonEmpty)
import Data.List.NonEmpty qualified as NE
import Data.Map.Strict (Map)
import Data.Set (Set)
import Data.Text (Text)
import YCHR.Internal.Loc (Ann)
import YCHR.Internal.Parsed (AnnP)
import YCHR.Internal.Types
  ( AggregateKind,
    BoundSig,
    ConstraintKey,
    ConstraintUse,
    HeadArg,
    Name (..),
    QualifiedConstraint,
    QualifiedName,
    Term (..),
    TypeDefinition,
    TypeExpr,
    flattenName,
    headArgToTerm,
    qualifiedToName,
  )

-- | A resolved program: all modules flattened, equations grouped under
-- their function declarations.
data Program = Program
  { rules :: [Rule],
    functions :: [FunctionDef],
    constraintTypes :: Map ConstraintKey [TypeExpr],
    -- | Bounds declared on each @:- chr_constraint@ that carries a
    -- @requiring@ clause. Constraints without bounds do not appear in
    -- this map (rather than mapping to @[]@) so a single membership
    -- check distinguishes "bounded constraint" from "unbounded".
    constraintBounds :: Map ConstraintKey [BoundSig],
    -- | The @:- constraint_use@ policy of each constraint that declares
    -- one other than @any@. Constraints absent from the map are
    -- unrestricted. Checked by "YCHR.Internal.ConstraintUse".
    constraintUses :: Map ConstraintKey ConstraintUse,
    -- | For each module, every @(name, arity)@ it can name as a
    -- constraint or a function, with the qualified declarations that
    -- provide it (more than one when the bare name is ambiguous) — the
    -- view the renamer resolves a goal's name in. A dynamic @tell\/N@
    -- resolves against its calling module's entry; see
    -- 'YCHR.Internal.Compile.buildTellables'.
    nameVisibility :: Map Text (Map (Text, Int) [QualifiedName]),
    functionNames :: Set QualifiedName,
    typeDefinitions :: [TypeDefinition]
  }
  deriving (Show)

-- | A rule in the resolved AST. Structurally identical to the parsed
-- rule; the three head kinds are preserved for desugaring to flatten.
--
-- Guards and bodies are 'Expr' (not 'Term'): the resolver has already
-- decided, for every compound, whether it is a function call, a data
-- constructor application, a dynamic dispatch, a function reference,
-- or a lambda. Downstream passes dispatch structurally and never need
-- to re-check the function-name set.
data Rule = Rule
  { name :: Maybe (Ann Text),
    -- | The module the rule was written in: the scope a dynamic
    -- @tell\/N@ in its body resolves constraint names against.
    moduleName :: Text,
    head :: AnnP Head,
    guard :: AnnP [Expr],
    body :: AnnP [Expr]
  }
  deriving (Show)

-- | Resolved rule head. Mirrors 'YCHR.Internal.Parsed.Head' but with
-- 'QualifiedConstraint' so the constraint-name qualification invariant
-- is reflected in the type. Desugaring flattens the three kinds into
-- the uniform @kept \/ removed@ shape of 'YCHR.Internal.Desugared.Head'.
--
-- Each kind carries the rule's aggregates alongside its head
-- constraints. Aggregates are neither kept nor removed, so they do not
-- affect which kind the rule is.
data Head
  = Simplification [QualifiedConstraint] [Aggregate]
  | Propagation [QualifiedConstraint] [Aggregate]
  | Simpagation [QualifiedConstraint] [QualifiedConstraint] [Aggregate]
  deriving (Show, Eq)

-- | A resolved rule's aggregates, whichever kind it is.
headAggregates :: Head -> [Aggregate]
headAggregates (Simplification _ aggs) = aggs
headAggregates (Propagation _ aggs) = aggs
headAggregates (Simpagation _ _ aggs) = aggs

-- | A resolved aggregate. Same shape as
-- 'YCHR.Internal.Types.Aggregate', with the goal's constraint names
-- qualified like head constraints and the four expressions typed.
data Aggregate = Aggregate
  { kind :: AggregateKind,
    agg :: Maybe Expr,
    element :: Expr,
    goal :: [AggregateConjunct],
    -- | The result pattern, kept as a 'Term' like a head argument: it
    -- is matched, not evaluated.
    result :: Term
  }
  deriving (Show, Eq)

-- | A resolved aggregate-goal conjunct.
data AggregateConjunct
  = -- | A CHR constraint, a /goal occurrence/ of its type.
    AggConstraint QualifiedConstraint
  | -- | A nested aggregate.
    AggNested Aggregate
  | -- | A @? Guard@, an ask-only boolean over the goal's variables.
    AggGuard Expr
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
    -- | The refinement type declared via @refining@, trusted as an
    -- axiom: a successful call of this function on a bare variable
    -- proves that variable has this type. 'Nothing' for an ordinary
    -- function.
    refining :: Maybe TypeExpr,
    -- | Whether this function was named by an @:- inline@ directive in
    -- its declaring module. 'YCHR.Internal.Resolve.checkInlineDeclarations'
    -- has already verified it is local and closed; the remaining
    -- eligibility checks (single equation, no guards, no prelude, no
    -- inline-to-inline cycle) run on the desugared AST, after HNF — see
    -- 'YCHR.Internal.Desugar.Inline'.
    inline :: Bool,
    equations :: [AnnP FunctionEquation]
  }
  deriving (Show)

-- | A function equation. Unlike 'YCHR.Internal.Parsed.FunctionEquation', there
-- is no @funName@ field — the name comes from the enclosing 'FunctionDef'.
--
-- 'args' stays as @[Term]@ because equation arguments are patterns:
-- they are normalized to 'HeadArg's by HNF in the desugarer, and the
-- call-vs-constructor question does not arise for them. 'guard' and
-- 'rhs' carry expression-position 'Expr's.
data FunctionEquation = FunctionEquation
  { args :: [Term],
    guard :: AnnP [Expr],
    rhs :: AnnP (NonEmpty Expr)
  }
  deriving (Show)

-- | An expression in a body, guard, or function RHS. Each constructor
-- corresponds to a single dynamic behavior at runtime, eliminating the
-- ambiguity of the uniform 'Term' shape:
--
--   * 'CallExpr' is a statically-known call to a user-declared
--     function.
--   * 'CtorExpr' is a data constructor application — compiled to a
--     @MakeTerm@ in the VM.
--   * 'ApplyExpr' is dynamic dispatch (the surface @'$call'(F, A1..An)@).
--   * 'FunRefExpr' is a first-class function reference
--     (the surface @fun name/arity@).
--   * 'LambdaExpr' is an anonymous function value. It exists between
--     resolution and the desugarer's lambda-lifting pass, after which
--     it is rewritten to a @__closure@-headed 'CtorExpr'. The
--     parameter list is 'NonEmpty': the resolver rejects
--     @fun() -> Body end@ with 'EmptyLambdaParams' (YCHR-16018) and
--     downstream stages can rely on at least one parameter.
--   * 'HostExpr' is a call into the host language
--     (the surface @host:f(args)@).
data Expr
  = VarExpr Text
  | IntExpr Integer
  | FloatExpr Double
  | TextExpr Text
  | WildcardExpr
  | CtorExpr Name [Expr]
  | CallExpr QualifiedName [Expr]
  | ApplyExpr Expr [Expr]
  | FunRefExpr QualifiedName Int
  | LambdaExpr (NonEmpty HeadArg) (NonEmpty Expr)
  | HostExpr Text [Expr]
  deriving (Show, Eq)

-- | The largest number of arguments an 'ApplyExpr' (surface
-- @'$call'(F, A1, …, An)@) may carry. The resolver rejects @'$call'@
-- beyond this limit with 'UnsupportedCallArity'; see the @$call\/N@
-- entry in @dev-docs\/INVARIANTS.md@.
--
-- The limit is a surface-language choice, aligned with the prelude's
-- @call\/N@ wrapper family, not a backend restriction: keyed @'$call'@
-- dispatch compiles a dynamic call to the arity-generic
-- 'YCHR.Internal.VM.ApplyClosure' construct, which works at any arity.
maxCallArity :: Int
maxCallArity = 10

-- | The largest number of arguments the built-in @tell\/N@ goal may
-- carry: the goal term plus up to nine arguments appended to it,
-- mirroring Prolog's @call\/1@ … @call\/10@. Checked by the renamer
-- ('YCHR.Internal.Rename.UnsupportedTellArity'). Like 'maxCallArity'
-- this is a surface-language limit; the VM's
-- 'YCHR.Internal.VM.TellTerm' works at any arity.
maxTellArity :: Int
maxTellArity = 10

-- | Convert an 'Expr' back to a surface-shaped 'Term'. Used as a
-- narrow bridge for code that still operates on 'Term' (notably the
-- @args@ field of 'YCHR.Internal.Types.QualifiedConstraint', which body-
-- constraint goals carry verbatim).
--
-- The conversion flattens every node to its surface compound shape:
-- 'CallExpr' becomes a 'CompoundTerm' with the function's qualified
-- 'Name' as the head, 'ApplyExpr' becomes a @'$call'@ compound,
-- 'LambdaExpr' becomes its surface @fun(...) -> body@ shape, and so
-- on. The result discards the call/host/apply distinctions — those
-- live only in the 'Expr' tree. This is intentional: every consumer
-- of the resulting 'Term' (e.g. 'YCHR.Internal.Compile.compileTerm',
-- 'YCHR.Run.termToValue') treats every compound as data, which
-- matches CHR's value semantics for constraint arguments and quoted
-- @quote\/1@ subtrees.
exprToTerm :: Expr -> Term
exprToTerm (VarExpr v) = VarTerm v
exprToTerm (IntExpr n) = IntTerm n
exprToTerm (FloatExpr n) = FloatTerm n
exprToTerm (TextExpr s) = TextTerm s
exprToTerm WildcardExpr = Wildcard
exprToTerm (CtorExpr name args) = CompoundTerm name (map exprToTerm args)
exprToTerm (CallExpr qn args) =
  CompoundTerm (qualifiedToName qn) (map exprToTerm args)
exprToTerm (ApplyExpr f args) =
  CompoundTerm (Unqualified "$call") (exprToTerm f : map exprToTerm args)
exprToTerm (HostExpr f args) =
  CompoundTerm (Qualified "host" f) (map exprToTerm args)
exprToTerm (FunRefExpr qn arity) =
  CompoundTerm
    (Unqualified "/")
    [ CompoundTerm (Unqualified (flattenName (qualifiedToName qn))) [],
      IntTerm (fromIntegral arity)
    ]
exprToTerm (LambdaExpr params body) =
  CompoundTerm
    (Unqualified "->")
    [ CompoundTerm (Unqualified "fun") (map headArgToTerm (NE.toList params)),
      sequenceToTerm body
    ]

-- | Re-build a comma-sequence 'Term' from a non-empty list of 'Expr's.
-- Inverse of the comma flattening done at the equation- and lambda-body
-- boundaries.
sequenceToTerm :: NonEmpty Expr -> Term
sequenceToTerm = go . NE.toList
  where
    go [e] = exprToTerm e
    go (e : es) = CompoundTerm (Unqualified ",") [exprToTerm e, go es]
    go [] = CompoundTerm (Unqualified "true") [] -- unreachable: NonEmpty
