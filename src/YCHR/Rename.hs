{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}

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
module YCHR.Rename (renameProgram, buildExportEnv, RenameError (..)) where

import Data.Text (Text)
import Effectful (Eff, runPureEff)
import Effectful.Writer.Static.Local (Writer, runWriter, tell)
import YCHR.Parsed
import YCHR.Rename.Types
import YCHR.Types

data RenameError
  = AmbiguousName Text Int [Text]
  | UnknownName Text Int
  deriving (Eq, Show)

-- | All declared constraints (for intra-module resolution).
buildLocalEnv :: [Module] -> LocalEnv
buildLocalEnv mods =
  makeLocalEnv
    [ ((declName d, declArity d), [modName m])
    | m <- mods,
      d <- modDecls m
    ]

-- | Only exported constraints (for cross-module resolution).
-- Modules without a @module@ directive (modExports = Nothing) export everything.
buildExportEnv :: [Module] -> GlobalEnv
buildExportEnv mods =
  makeGlobalEnv
    [ ((declName d, declArity d), [modName m])
    | m <- mods,
      d <- case modExports m of
        Nothing -> modDecls m
        Just exports -> exports
    ]

renameProgram :: [Module] -> Either [RenameError] [Module]
renameProgram mods =
  let localEnv = buildLocalEnv mods
      exportEnv = buildExportEnv mods
      (result, errs) = runPureEff . runWriter $ traverse (renameModule localEnv exportEnv) mods
   in if null errs then Right result else Left errs

renameModule :: LocalEnv -> GlobalEnv -> Module -> Eff '[Writer [RenameError]] Module
renameModule localEnv exportEnv m = do
  rules <- traverse (renameRule localEnv exportEnv m) (modRules m)
  pure m {modRules = rules}

renameRule :: LocalEnv -> GlobalEnv -> Module -> Rule -> Eff '[Writer [RenameError]] Rule
renameRule localEnv exportEnv m r = do
  h <- renameHead localEnv exportEnv m (ruleHead r)
  g <- traverse (renameTerm localEnv exportEnv m False) (ruleGuard r)
  b <- traverse (renameTerm localEnv exportEnv m True) (ruleBody r)
  pure r {ruleHead = h, ruleGuard = g, ruleBody = b}

renameHead :: LocalEnv -> GlobalEnv -> Module -> Head -> Eff '[Writer [RenameError]] Head
renameHead localEnv exportEnv m h = case h of
  Simplification cs -> Simplification <$> traverse (renameCon localEnv exportEnv m) cs
  Propagation cs -> Propagation <$> traverse (renameCon localEnv exportEnv m) cs
  Simpagation k r -> Simpagation <$> traverse (renameCon localEnv exportEnv m) k <*> traverse (renameCon localEnv exportEnv m) r

renameCon :: LocalEnv -> GlobalEnv -> Module -> Constraint -> Eff '[Writer [RenameError]] Constraint
renameCon localEnv exportEnv m (Constraint name args) = do
  renamedName <- resolveName localEnv exportEnv m name (length args)
  renamedArgs <- traverse (renameTerm localEnv exportEnv m False) args
  pure (Constraint renamedName renamedArgs)

renameTerm :: LocalEnv -> GlobalEnv -> Module -> Bool -> Term -> Eff '[Writer [RenameError]] Term
renameTerm localEnv exportEnv m isGoal t = case t of
  CompoundTerm name args -> do
    renamedArgs <- traverse (renameTerm localEnv exportEnv m False) args
    newName <- if isGoal then resolveName localEnv exportEnv m name (length args) else pure name
    pure (CompoundTerm newName renamedArgs)
  other -> pure other

resolveName :: LocalEnv -> GlobalEnv -> Module -> Name -> Int -> Eff '[Writer [RenameError]] Name
resolveName localEnv exportEnv currentMod (Unqualified n) arity
  | isReserved n reservedSymbols = pure (Unqualified n)
  | otherwise =
      let ownProviders = filter (== modName currentMod) (lookupLocal (n, arity) localEnv)
          importNames = [mn | ModuleImport mn <- modImports currentMod]
          importProviders = filter (`elem` importNames) (lookupGlobal (n, arity) exportEnv)
          matches = ownProviders ++ importProviders
       in case matches of
            [m] -> pure (Qualified m n)
            [] -> do
              tell [UnknownName n arity]
              pure (Unqualified n)
            ms -> do
              tell [AmbiguousName n arity ms]
              pure (Unqualified n)
resolveName _ _ _ (Qualified m n) _ = pure (Qualified m n)
