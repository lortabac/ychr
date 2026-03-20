{-# LANGUAGE DataKinds #-}

-- |
-- Module      : YCHR.Desugar
-- Description : Erases module boundaries and flattens CHR rules into an internal AST.
--
-- The Desugarer is the final transformation pass before code generation. Its
-- responsibilities include:
--
-- 1. Module Erasure: Flattens a collection of 'YCHR.Parsed.Module' objects into
--    a single 'YCHR.Desugared.Program'.
-- 2. Goal Classification: Uses the 'Name' sum-type (populated by the Renamer)
--    to partition rule bodies into CHR Constraints, Host Statements,
--    Unifications, or Host Calls.
-- 3. Head Normalization: Maps the various surface rule types (Simplification,
--    Propagation, Simpagation) into a uniform 'Kept/Removed' head structure.
-- 4. Symbol Table Generation: Performs a whole-program scan to assign
--    unique, sequential 0-indexed integers to every 'Qualified' CHR constraint,
--    enabling efficient array-based dispatch in the VM.
--
-- By the end of this pass, the program is no longer a set of human-readable
-- files, but a structured list of instructions and a numeric symbol map.
module YCHR.Desugar
  ( DesugarError (..),
    desugarProgram,
    SymbolTable,
    extractSymbolTable,
  )
where

import Data.Map qualified as Map
import Data.Set qualified as Set
import Effectful (Eff, runPureEff)
import Effectful.Writer.Static.Local (Writer, runWriter, tell)
import YCHR.Desugared qualified as D
import YCHR.Parsed qualified as P
import YCHR.Types

data DesugarError
  = UnexpectedBodyTerm Term
  deriving (Eq, Show)

-- | A map from a fully qualified CHR name to a unique, 0-indexed integer.
-- This is used by the compiler to generate efficient instructions.
type SymbolTable = Map.Map Name ConstraintType

-- | The primary entry point: converts parsed modules to a desugared program.
desugarProgram :: [P.Module] -> Either [DesugarError] D.Program
desugarProgram mods =
  let (result, errs) = runPureEff . runWriter $ do
        rules <- mapM desugarRule [r | m <- mods, r <- P.modRules m]
        pure (D.Program rules)
   in if null errs then Right result else Left errs

-- | Scans a desugared program and builds the optimization map.
-- It ensures that all Qualified names get a sequential ID starting from 0.
extractSymbolTable :: D.Program -> SymbolTable
extractSymbolTable (D.Program rules) =
  let -- 1. Collect every name used in a CHR constraint position
      allNames = Set.fromList [conName c | r <- rules, c <- getRuleConstraints r]

      -- 2. Only include 'Qualified' names in the table.
      -- Unqualified names (host calls) do not get integer IDs.
      qualifiedNames = [n | n@(Qualified _ _) <- Set.toList allNames]
   in Map.fromList (zip qualifiedNames (map ConstraintType [0 ..]))

-- | Helper to find every constraint instance in a desugared rule.
getRuleConstraints :: D.Rule -> [Constraint]
getRuleConstraints r =
  D.headKept (D.ruleHead r)
    ++ D.headRemoved (D.ruleHead r)
    ++ [c | D.BodyConstraint c <- D.ruleBody r]

desugarRule :: P.Rule -> Eff '[Writer [DesugarError]] D.Rule
desugarRule r = do
  body <- mapM desugarBodyGoal (P.ruleBody r)
  pure
    D.Rule
      { D.ruleName = P.ruleName r,
        D.ruleHead = desugarHead (P.ruleHead r),
        D.ruleGuard = map desugarGuard (P.ruleGuard r),
        D.ruleBody = body
      }

desugarHead :: P.Head -> D.Head
desugarHead h = case h of
  P.Simplification rs -> D.Head [] rs
  P.Propagation ks -> D.Head ks []
  P.Simpagation ks rs -> D.Head ks rs

desugarGuard :: Term -> D.Guard
desugarGuard (CompoundTerm (Unqualified "==") [l, r]) = D.GuardEqual l r
desugarGuard (CompoundTerm (Unqualified f) args) = D.GuardHostCall f args
desugarGuard (AtomTerm "true") = D.GuardCommon D.GoalTrue
desugarGuard _ = D.GuardCommon D.GoalTrue

desugarBodyGoal :: Term -> Eff '[Writer [DesugarError]] D.BodyGoal
desugarBodyGoal t = case t of
  CompoundTerm (Unqualified "=") [l, r] -> pure $ D.BodyUnify l r
  CompoundTerm (Unqualified "<-") [VarTerm v, CompoundTerm (Unqualified f) args] ->
    pure $ D.BodyHostCall v f args
  CompoundTerm (Qualified m n) args ->
    pure $ D.BodyConstraint (Constraint (Qualified m n) args)
  CompoundTerm (Unqualified "$") [CompoundTerm (Unqualified f) args] ->
    pure $ D.BodyHostStmt f args
  AtomTerm "true" -> pure $ D.BodyCommon D.GoalTrue
  CompoundTerm (Unqualified _) _ -> do
    tell [UnexpectedBodyTerm t]
    pure $ D.BodyCommon D.GoalTrue
  _ -> pure $ D.BodyCommon D.GoalTrue
