{-# LANGUAGE OverloadedStrings #-}

-- |
-- Module      : YCHR.Internal.Desugar.Vars
-- Description : The variables an expression or a guard mentions.
--
-- One walker, shared by "YCHR.Internal.Desugar" (lambda lifting) and
-- "YCHR.Internal.Desugar.AggregateScope", so both agree on what a
-- lambda captures.
module YCHR.Internal.Desugar.Vars
  ( exprVars,
    sequenceFree,
    guardVars,
    headArgVars,
  )
where

import Data.List.NonEmpty qualified as NE
import Data.Set qualified as Set
import Data.Text (Text)
import YCHR.Internal.Desugared qualified as D
import YCHR.Internal.Types

-- | Collect all variable names referenced inside an expression.
exprVars :: D.Expr -> Set.Set Text
exprVars (D.VarExpr v) = Set.singleton v
exprVars (D.CtorExpr _ args) = Set.unions (map exprVars args)
exprVars (D.CallExpr _ args) = Set.unions (map exprVars args)
exprVars (D.ApplyExpr f args) =
  exprVars f `Set.union` Set.unions (map exprVars args)
exprVars (D.HostExpr _ args) = Set.unions (map exprVars args)
exprVars (D.LambdaExpr params body) =
  sequenceFree (NE.toList body)
    `Set.difference` Set.fromList [v | HeadVar v <- NE.toList params]
exprVars (D.FunRefExpr _ _) = Set.empty
exprVars (D.IntExpr _) = Set.empty
exprVars (D.FloatExpr _) = Set.empty
exprVars (D.TextExpr _) = Set.empty
exprVars D.WildcardExpr = Set.empty

-- | Free variables of a sequenced expression list (lambda body or
-- top-level function body), treating an @X is E@ item as a binder for
-- X: uses of X /before/ the binding (and uses of X in @E@ itself, which
-- is evaluated /before/ the binding takes effect) still count, while
-- uses in /later/ items resolve to the local binding and do not escape.
sequenceFree :: [D.Expr] -> Set.Set Text
sequenceFree = go Set.empty
  where
    go _ [] = Set.empty
    go bound (e : es) =
      let usedHere = case e of
            D.CtorExpr (Unqualified "is") [D.VarExpr _, rhs] -> exprVars rhs
            _ -> exprVars e
          contrib = usedHere `Set.difference` bound
          bound' = case e of
            D.CtorExpr (Unqualified "is") [D.VarExpr v, _] ->
              Set.insert v bound
            _ -> bound
       in contrib `Set.union` go bound' es

-- | Collect all variables from a list of guards.
guardVars :: [D.Guard] -> Set.Set Text
guardVars = Set.unions . map gVars
  where
    gVars (D.GuardExpr e) = exprVars e
    gVars (D.GuardEqual e1 e2) = exprVars e1 `Set.union` exprVars e2
    gVars (D.GuardGetArg v e _) = Set.insert v (exprVars e)
    gVars (D.GuardMatch e _ _) = exprVars e

-- | Variables introduced by a single 'HeadArg'. Wildcards contribute
-- nothing.
headArgVars :: HeadArg -> Set.Set Text
headArgVars (HeadVar v) = Set.singleton v
headArgVars HeadWildcard = Set.empty
