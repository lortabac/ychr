{-# LANGUAGE DataKinds #-}

-- |
-- Module      : YCHR.Rename
-- Description : Resolves and qualifies symbolic names across a multi-module program.
--
-- The Renamer performs a whole-program analysis to transform 'Unqualified' names
-- into 'Qualified' ones. Its primary responsibilities are:
--
-- 1. Global Environment Building: Scans all modules to map every declared
--    constraint (Name, Arity) to its defining module.
-- 2. Namespace Resolution: Using a module's imports, it identifies which
--    module a local name refers to.
-- 3. Ambiguity Enforcement: Ensures that if multiple imports provide the same
--    constraint, the user is forced to provide an explicit qualification.
-- 4. Goal Classification: Distinguishes between top-level CHR constraints
--    (which get qualified) and nested data functors or host-language calls
--    (which remain unqualified).
--
-- This pass ensures that the subsequent Desugaring phase can treat the
-- program as a flat, unambiguous collection of rules.
module YCHR.Rename (renameProgram, RenameError (..)) where

import Data.Map qualified as Map
import Data.Set qualified as Set
import Effectful (Eff, runPureEff)
import Effectful.Writer.Static.Local (Writer, runWriter, tell)
import YCHR.Parsed
import YCHR.Types

data RenameError
  = AmbiguousName String Int [String]
  | UnknownName String Int
  deriving (Eq, Show)

-- | Map of (Name, Arity) to the Modules defining it.
type GlobalEnv = Map.Map (String, Int) [String]

buildGlobalEnv :: [Module] -> GlobalEnv
buildGlobalEnv mods =
  Map.fromListWith
    (++)
    [ ((declName d, declArity d), [modName m])
    | m <- mods,
      d <- modDecls m
    ]

reservedSymbols :: Set.Set String
reservedSymbols = Set.fromList ["true", "fail", "=", "==", ":=", "$", "is"]

renameProgram :: [Module] -> Either [RenameError] [Module]
renameProgram mods =
  let env = buildGlobalEnv mods
      (result, errs) = runPureEff . runWriter $ traverse (renameModule env) mods
   in if null errs then Right result else Left errs

renameModule :: GlobalEnv -> Module -> Eff '[Writer [RenameError]] Module
renameModule env m = do
  rules <- traverse (renameRule env m) (modRules m)
  pure m {modRules = rules}

renameRule :: GlobalEnv -> Module -> Rule -> Eff '[Writer [RenameError]] Rule
renameRule env m r = do
  h <- renameHead env m (ruleHead r)
  g <- traverse (renameTerm env m False) (ruleGuard r)
  b <- traverse (renameTerm env m True) (ruleBody r)
  pure r {ruleHead = h, ruleGuard = g, ruleBody = b}

renameHead :: GlobalEnv -> Module -> Head -> Eff '[Writer [RenameError]] Head
renameHead env m h = case h of
  Simplification cs -> Simplification <$> traverse (renameCon env m) cs
  Propagation cs -> Propagation <$> traverse (renameCon env m) cs
  Simpagation k r -> Simpagation <$> traverse (renameCon env m) k <*> traverse (renameCon env m) r

renameCon :: GlobalEnv -> Module -> Constraint -> Eff '[Writer [RenameError]] Constraint
renameCon env m (Constraint name args) = do
  renamedName <- resolveName env m name (length args)
  renamedArgs <- traverse (renameTerm env m False) args
  pure (Constraint renamedName renamedArgs)

renameTerm :: GlobalEnv -> Module -> Bool -> Term -> Eff '[Writer [RenameError]] Term
renameTerm env m isGoal t = case t of
  CompoundTerm name args -> do
    renamedArgs <- traverse (renameTerm env m False) args
    newName <- if isGoal then resolveName env m name (length args) else pure name
    pure (CompoundTerm newName renamedArgs)
  other -> pure other

resolveName :: GlobalEnv -> Module -> Name -> Int -> Eff '[Writer [RenameError]] Name
resolveName env currentMod (Unqualified n) arity
  | Set.member n reservedSymbols = pure (Unqualified n)
  | otherwise =
      let visible = modName currentMod : modImports currentMod
          providers = Map.findWithDefault [] (n, arity) env
          matches = filter (`elem` visible) providers
       in case matches of
            [m] -> pure (Qualified m n)
            [] -> do
              tell [UnknownName n arity]
              pure (Unqualified n)
            ms -> do
              tell [AmbiguousName n arity ms]
              pure (Unqualified n)
resolveName _ _ (Qualified m n) _ = pure (Qualified m n)
