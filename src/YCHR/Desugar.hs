{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}

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

import Data.List (mapAccumL)
import Data.Map qualified as Map
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as T
import Effectful (Eff, runPureEff)
import Effectful.Writer.Static.Local (Writer, runWriter, tell)
import YCHR.Desugared qualified as D
import YCHR.Parsed qualified as P
import YCHR.Types

data DesugarError
  = UnexpectedBodyTerm Term
  deriving (Eq, Show)

-- | The primary entry point: converts parsed modules to a desugared program.
desugarProgram :: [P.Module] -> Either [DesugarError] D.Program
desugarProgram mods =
  let (result, errs) = runPureEff . runWriter $ do
        rules <- traverse desugarRule [r | m <- mods, r <- P.modRules m]
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
   in mkSymbolTable (zip qualifiedNames (map ConstraintType [0 ..]))

-- | Helper to find every constraint instance in a desugared rule.
getRuleConstraints :: D.Rule -> [Constraint]
getRuleConstraints r =
  D.headKept (D.ruleHead r)
    ++ D.headRemoved (D.ruleHead r)
    ++ [c | D.BodyConstraint c <- D.ruleBody r]

desugarRule :: P.Rule -> Eff '[Writer [DesugarError]] D.Rule
desugarRule r = do
  body <- traverse desugarBodyGoal (P.node (P.ruleBody r))
  let rawHead = desugarHead (P.node (P.ruleHead r))
      (hnfGuards, normalizedHead) = normalizeHead rawHead
      userGuards = map desugarGuard (P.node (P.ruleGuard r))
  pure
    D.Rule
      { D.ruleName = fmap P.node (P.ruleName r),
        D.ruleHead = normalizedHead,
        D.ruleGuard = hnfGuards ++ userGuards,
        D.ruleBody = body
      }

desugarHead :: P.Head -> D.Head
desugarHead h = case h of
  P.Simplification rs -> D.Head [] rs
  P.Propagation ks -> D.Head ks []
  P.Simpagation ks rs -> D.Head ks rs

-- Head Normal Form (HNF) transformation
-- All head arguments become distinct variables; duplicate variables and
-- non-variable terms are replaced with fresh variables and explicit
-- GuardEqual guards are generated.

data HnfState = HnfState
  { hnfCounter :: !Int,
    hnfSeen :: Map.Map Text (),
    hnfGuards :: [D.Guard] -- accumulated in reverse
  }

normalizeHead :: D.Head -> ([D.Guard], D.Head)
normalizeHead (D.Head kept removed) =
  let initState = HnfState 0 Map.empty []
      (st1, kept') = mapAccumL normalizeConstraint initState kept
      (st2, removed') = mapAccumL normalizeConstraint st1 removed
   in (reverse (hnfGuards st2), D.Head kept' removed')

normalizeConstraint :: HnfState -> Constraint -> (HnfState, Constraint)
normalizeConstraint st (Constraint name args) =
  let (st', args') = mapAccumL normalizeArg st args
   in (st', Constraint name args')

normalizeArg :: HnfState -> Term -> (HnfState, Term)
normalizeArg st (VarTerm v)
  | Map.member v (hnfSeen st) =
      let fresh = "_hnf_" <> T.pack (show (hnfCounter st))
       in ( st
              { hnfCounter = hnfCounter st + 1,
                hnfGuards = D.GuardEqual (VarTerm v) (VarTerm fresh) : hnfGuards st
              },
            VarTerm fresh
          )
  | otherwise =
      (st {hnfSeen = Map.insert v () (hnfSeen st)}, VarTerm v)
normalizeArg st Wildcard = (st, Wildcard)
normalizeArg st (CompoundTerm name args) =
  let fresh = "_hnf_" <> T.pack (show (hnfCounter st))
      st' = st {hnfCounter = hnfCounter st + 1}
      st'' = decomposeCompound st' fresh name args
   in (st'', VarTerm fresh)
normalizeArg st term =
  let fresh = "_hnf_" <> T.pack (show (hnfCounter st))
   in ( st
          { hnfCounter = hnfCounter st + 1,
            hnfGuards = D.GuardEqual (VarTerm fresh) term : hnfGuards st
          },
        VarTerm fresh
      )

-- | Decompose a compound term into match and extraction guards.
decomposeCompound :: HnfState -> Text -> Name -> [Term] -> HnfState
decomposeCompound st parentVar name args =
  let matchGuard = D.GuardMatch (VarTerm parentVar) name (length args)
      st' = st {hnfGuards = matchGuard : hnfGuards st}
   in foldl' (\s (i, arg) -> decomposeArg s parentVar i arg) st' (zip [0 ..] args)

-- | Decompose a single argument of a compound term.
decomposeArg :: HnfState -> Text -> Int -> Term -> HnfState
decomposeArg st parentVar i (VarTerm v)
  | Map.member v (hnfSeen st) =
      -- Duplicate variable: extract and check equality
      let fresh = "_hnf_" <> T.pack (show (hnfCounter st))
          getGuard = D.GuardGetArg fresh (VarTerm parentVar) i
          eqGuard = D.GuardEqual (VarTerm v) (VarTerm fresh)
       in st
            { hnfCounter = hnfCounter st + 1,
              hnfGuards = eqGuard : getGuard : hnfGuards st
            }
  | otherwise =
      -- First occurrence: extract and bind
      let getGuard = D.GuardGetArg v (VarTerm parentVar) i
       in st
            { hnfGuards = getGuard : hnfGuards st,
              hnfSeen = Map.insert v () (hnfSeen st)
            }
decomposeArg st _ _ Wildcard = st
decomposeArg st parentVar i (CompoundTerm name args) =
  -- Nested compound: extract then recursively decompose
  let fresh = "_hnf_" <> T.pack (show (hnfCounter st))
      getGuard = D.GuardGetArg fresh (VarTerm parentVar) i
      st' =
        st
          { hnfCounter = hnfCounter st + 1,
            hnfGuards = getGuard : hnfGuards st
          }
   in decomposeCompound st' fresh name args
decomposeArg st parentVar i term =
  -- Ground term (atom, integer, string): extract and check equality
  let fresh = "_hnf_" <> T.pack (show (hnfCounter st))
      getGuard = D.GuardGetArg fresh (VarTerm parentVar) i
      eqGuard = D.GuardEqual (VarTerm fresh) term
   in st
        { hnfCounter = hnfCounter st + 1,
          hnfGuards = eqGuard : getGuard : hnfGuards st
        }

desugarGuard :: Term -> D.Guard
desugarGuard (AtomTerm "true") = D.GuardCommon D.GoalTrue
desugarGuard t@(CompoundTerm _ _) = D.GuardExpr t
desugarGuard _ = D.GuardCommon D.GoalTrue

desugarBodyGoal :: Term -> Eff '[Writer [DesugarError]] D.BodyGoal
desugarBodyGoal t = case t of
  CompoundTerm (Unqualified "=") [l, r] -> pure $ D.BodyUnify l r
  CompoundTerm (Unqualified ":=") [VarTerm v, CompoundTerm (Unqualified f) args] ->
    pure $ D.BodyHostCall v f args
  CompoundTerm (Unqualified ":=") [Wildcard, CompoundTerm (Unqualified f) args] ->
    pure $ D.BodyHostStmt f args
  CompoundTerm (Unqualified "is") [VarTerm v, expr] ->
    pure $ D.BodyIs v expr
  CompoundTerm (Qualified m n) args ->
    pure $ D.BodyConstraint (Constraint (Qualified m n) args)
  CompoundTerm (Unqualified "host") [CompoundTerm (Unqualified f) args] ->
    pure $ D.BodyHostStmt f args
  AtomTerm "true" -> pure $ D.BodyCommon D.GoalTrue
  CompoundTerm (Unqualified _) _ -> do
    tell [UnexpectedBodyTerm t]
    pure $ D.BodyCommon D.GoalTrue
  _ -> pure $ D.BodyCommon D.GoalTrue
