{-# LANGUAGE DuplicateRecordFields #-}
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
module YCHR.Resolved
  ( Program (..),
    Rule (..),
    Head (..),
    FunctionDef (..),
    FunctionEquation (..),
    Expr (..),
    exprToTerm,
  )
where

import Data.List.NonEmpty (NonEmpty)
import Data.List.NonEmpty qualified as NE
import Data.Map.Strict (Map)
import Data.Set (Set)
import Data.Text (Text)
import YCHR.Loc (Ann)
import YCHR.Parsed (AnnP)
import YCHR.Types
  ( BoundSig,
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
--
-- Guards and bodies are 'Expr' (not 'Term'): the resolver has already
-- decided, for every compound, whether it is a function call, a data
-- constructor application, a dynamic dispatch, a function reference,
-- or a lambda. Downstream passes dispatch structurally and never need
-- to re-check the function-name set.
data Rule = Rule
  { name :: Maybe (Ann Text),
    head :: AnnP Head,
    guard :: AnnP [Expr],
    body :: AnnP [Expr]
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
  | AtomExpr Text
  | TextExpr Text
  | WildcardExpr
  | CtorExpr Name [Expr]
  | CallExpr QualifiedName [Expr]
  | ApplyExpr Expr [Expr]
  | FunRefExpr QualifiedName Int
  | LambdaExpr (NonEmpty HeadArg) (NonEmpty Expr)
  | HostExpr Text [Expr]
  deriving (Show, Eq)

-- | Convert an 'Expr' back to a surface-shaped 'Term'. Used as a
-- narrow bridge for code that still operates on 'Term' (notably the
-- @args@ field of 'YCHR.Types.QualifiedConstraint', which body-
-- constraint goals carry verbatim).
--
-- The conversion flattens every node to its surface compound shape:
-- 'CallExpr' becomes a 'CompoundTerm' with the function's qualified
-- 'Name' as the head, 'ApplyExpr' becomes a @'$call'@ compound,
-- 'LambdaExpr' becomes its surface @fun(...) -> body@ shape, and so
-- on. The result discards the call/host/apply distinctions — those
-- live only in the 'Expr' tree. This is intentional: every consumer
-- of the resulting 'Term' (e.g. 'YCHR.Compile.compileTerm',
-- 'YCHR.Run.termToValue') treats every compound as data, which
-- matches CHR's value semantics for constraint arguments and quoted
-- @term\/1@ subtrees.
exprToTerm :: Expr -> Term
exprToTerm (VarExpr v) = VarTerm v
exprToTerm (IntExpr n) = IntTerm n
exprToTerm (FloatExpr n) = FloatTerm n
exprToTerm (AtomExpr s) = AtomTerm s
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
    [AtomTerm (flattenName (qualifiedToName qn)), IntTerm (fromIntegral arity)]
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
    go [] = AtomTerm "true" -- unreachable: NonEmpty
