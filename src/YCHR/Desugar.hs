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
import YCHR.Pretty (AnnP (..), PrettyE (..))
import YCHR.Types

data DesugarError
  = UnexpectedBodyTerm P.SourceLoc Term
  deriving (Eq, Show)

-- | The primary entry point: converts parsed modules to a desugared program.
desugarProgram :: [P.Module] -> Either [DesugarError] D.Program
desugarProgram mods =
  let (result, errs) = runPureEff . runWriter $ do
        rules <- traverse desugarRule [r | m <- mods, r <- m.rules]
        pure (D.Program rules)
   in if null errs then Right result else Left errs

-- | Scans a desugared program and builds the optimization map.
-- It ensures that all Qualified names get a sequential ID starting from 0.
extractSymbolTable :: D.Program -> SymbolTable
extractSymbolTable (D.Program rules) =
  let -- 1. Collect every name used in a CHR constraint position
      allNames = Set.fromList [c.name | r <- rules, c <- getRuleConstraints r]

      -- 2. Only include 'Qualified' names in the table.
      -- Unqualified names (host calls) do not get integer IDs.
      qualifiedNames = [n | n@(Qualified _ _) <- Set.toList allNames]
   in mkSymbolTable (zip qualifiedNames (map ConstraintType [0 ..]))

-- | Helper to find every constraint instance in a desugared rule.
getRuleConstraints :: D.Rule -> [Constraint]
getRuleConstraints r =
  let AnnP {node = rHead} = r.head
      AnnP {node = rBody} = r.body
   in rHead.kept
        ++ rHead.removed
        ++ [c | D.BodyConstraint c <- rBody]

desugarRule :: P.Rule -> Eff '[Writer [DesugarError]] D.Rule
desugarRule r = do
  ruleBody <- traverse (desugarBodyGoal r.body.sourceLoc) r.body.node
  let rawHead = desugarHead r.head.node
      (hnfGuards, normalizedHead) = normalizeHead rawHead
      userGuards = map desugarGuard r.guard.node
  pure
    D.Rule
      { name = fmap (.node) r.name,
        head = AnnP normalizedHead r.head.sourceLoc (PrettyE r.head.node),
        guard = AnnP (hnfGuards ++ userGuards) r.guard.sourceLoc (PrettyE r.guard.node),
        body = AnnP ruleBody r.body.sourceLoc (PrettyE r.body.node)
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
normalizeHead h =
  let initState = HnfState 0 Map.empty []
      (st1, kept') = mapAccumL normalizeConstraint initState h.kept
      (st2, removed') = mapAccumL normalizeConstraint st1 h.removed
   in (reverse st2.hnfGuards, D.Head kept' removed')

normalizeConstraint :: HnfState -> Constraint -> (HnfState, Constraint)
normalizeConstraint st (Constraint cname cargs) =
  let (st', args') = mapAccumL normalizeArg st cargs
   in (st', Constraint cname args')

normalizeArg :: HnfState -> Term -> (HnfState, Term)
normalizeArg st (VarTerm v)
  | Map.member v st.hnfSeen =
      let fresh = "_hnf_" <> T.pack (show st.hnfCounter)
       in ( st
              { hnfCounter = st.hnfCounter + 1,
                hnfGuards = D.GuardEqual (VarTerm v) (VarTerm fresh) : st.hnfGuards
              },
            VarTerm fresh
          )
  | otherwise =
      (st {hnfSeen = Map.insert v () st.hnfSeen}, VarTerm v)
normalizeArg st Wildcard = (st, Wildcard)
normalizeArg st (CompoundTerm cname cargs) =
  let fresh = "_hnf_" <> T.pack (show st.hnfCounter)
      st' = st {hnfCounter = st.hnfCounter + 1}
      st'' = decomposeCompound st' fresh cname cargs
   in (st'', VarTerm fresh)
normalizeArg st term =
  let fresh = "_hnf_" <> T.pack (show st.hnfCounter)
   in ( st
          { hnfCounter = st.hnfCounter + 1,
            hnfGuards = D.GuardEqual (VarTerm fresh) term : st.hnfGuards
          },
        VarTerm fresh
      )

-- | Decompose a compound term into match and extraction guards.
decomposeCompound :: HnfState -> Text -> Name -> [Term] -> HnfState
decomposeCompound st parentVar cname cargs =
  let matchGuard = D.GuardMatch (VarTerm parentVar) cname (length cargs)
      st' = st {hnfGuards = matchGuard : st.hnfGuards}
   in foldl' (\s (i, arg) -> decomposeArg s parentVar i arg) st' (zip [0 ..] cargs)

-- | Decompose a single argument of a compound term.
decomposeArg :: HnfState -> Text -> Int -> Term -> HnfState
decomposeArg st parentVar i (VarTerm v)
  | Map.member v st.hnfSeen =
      -- Duplicate variable: extract and check equality
      let fresh = "_hnf_" <> T.pack (show st.hnfCounter)
          getGuard = D.GuardGetArg fresh (VarTerm parentVar) i
          eqGuard = D.GuardEqual (VarTerm v) (VarTerm fresh)
       in st
            { hnfCounter = st.hnfCounter + 1,
              hnfGuards = eqGuard : getGuard : st.hnfGuards
            }
  | otherwise =
      -- First occurrence: extract and bind
      let getGuard = D.GuardGetArg v (VarTerm parentVar) i
       in st
            { hnfGuards = getGuard : st.hnfGuards,
              hnfSeen = Map.insert v () st.hnfSeen
            }
decomposeArg st _ _ Wildcard = st
decomposeArg st parentVar i (CompoundTerm cname cargs) =
  -- Nested compound: extract then recursively decompose
  let fresh = "_hnf_" <> T.pack (show st.hnfCounter)
      getGuard = D.GuardGetArg fresh (VarTerm parentVar) i
      st' =
        st
          { hnfCounter = st.hnfCounter + 1,
            hnfGuards = getGuard : st.hnfGuards
          }
   in decomposeCompound st' fresh cname cargs
decomposeArg st parentVar i term =
  -- Ground term (atom, integer, string): extract and check equality
  let fresh = "_hnf_" <> T.pack (show st.hnfCounter)
      getGuard = D.GuardGetArg fresh (VarTerm parentVar) i
      eqGuard = D.GuardEqual (VarTerm fresh) term
   in st
        { hnfCounter = st.hnfCounter + 1,
          hnfGuards = eqGuard : getGuard : st.hnfGuards
        }

desugarGuard :: Term -> D.Guard
desugarGuard (AtomTerm "true") = D.GuardCommon D.GoalTrue
desugarGuard t@(CompoundTerm _ _) = D.GuardExpr t
desugarGuard _ = D.GuardCommon D.GoalTrue

desugarBodyGoal :: P.SourceLoc -> Term -> Eff '[Writer [DesugarError]] D.BodyGoal
desugarBodyGoal loc t = case t of
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
    tell [UnexpectedBodyTerm loc t]
    pure $ D.BodyCommon D.GoalTrue
  _ -> pure $ D.BodyCommon D.GoalTrue
