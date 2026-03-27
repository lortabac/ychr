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
  = AmbiguousName SourceLoc Text Int [Text]
  | UnknownName SourceLoc Text Int
  deriving (Eq, Show)

-- | All declared constraints (for intra-module resolution).
buildLocalEnv :: [Module] -> LocalEnv
buildLocalEnv mods =
  makeLocalEnv
    [ ((d.name, d.arity), [m.name])
    | m <- mods,
      Ann d _ <- m.decls
    ]

-- | Only exported constraints (for cross-module resolution).
-- Modules without a @module@ directive (modExports = Nothing) export everything.
buildExportEnv :: [Module] -> GlobalEnv
buildExportEnv mods =
  makeGlobalEnv
    [ ((d.name, d.arity), [m.name])
    | m <- mods,
      d <- case m.exports of
        Nothing -> map (.node) m.decls
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
  renamedRules <- traverse (renameRule localEnv exportEnv m) m.rules
  pure m {rules = renamedRules}

renameRule :: LocalEnv -> GlobalEnv -> Module -> Rule -> Eff '[Writer [RenameError]] Rule
renameRule localEnv exportEnv m r = do
  h <- traverse (renameHead localEnv exportEnv m r.head.sourceLoc) r.head
  g <- traverse (traverse (renameTerm localEnv exportEnv m r.guard.sourceLoc False)) r.guard
  b <- traverse (traverse (renameTerm localEnv exportEnv m r.body.sourceLoc True)) r.body
  pure r {head = h, guard = g, body = b}

renameHead :: LocalEnv -> GlobalEnv -> Module -> SourceLoc -> Head -> Eff '[Writer [RenameError]] Head
renameHead localEnv exportEnv m loc h = case h of
  Simplification cs -> Simplification <$> traverse (renameCon localEnv exportEnv m loc) cs
  Propagation cs -> Propagation <$> traverse (renameCon localEnv exportEnv m loc) cs
  Simpagation k r -> Simpagation <$> traverse (renameCon localEnv exportEnv m loc) k <*> traverse (renameCon localEnv exportEnv m loc) r

renameCon :: LocalEnv -> GlobalEnv -> Module -> SourceLoc -> Constraint -> Eff '[Writer [RenameError]] Constraint
renameCon localEnv exportEnv m loc (Constraint cname cargs) = do
  renamedName <- resolveName localEnv exportEnv m loc cname (length cargs)
  renamedArgs <- traverse (renameTerm localEnv exportEnv m loc False) cargs
  pure (Constraint renamedName renamedArgs)

renameTerm :: LocalEnv -> GlobalEnv -> Module -> SourceLoc -> Bool -> Term -> Eff '[Writer [RenameError]] Term
renameTerm localEnv exportEnv m loc isGoal t = case t of
  CompoundTerm name args -> do
    renamedArgs <- traverse (renameTerm localEnv exportEnv m loc False) args
    newName <- if isGoal then resolveName localEnv exportEnv m loc name (length args) else pure name
    pure (CompoundTerm newName renamedArgs)
  other -> pure other

resolveName :: LocalEnv -> GlobalEnv -> Module -> SourceLoc -> Name -> Int -> Eff '[Writer [RenameError]] Name
resolveName localEnv exportEnv currentMod loc (Unqualified n) arity
  | isReserved n reservedSymbols = pure (Unqualified n)
  | otherwise =
      let ownProviders = filter (== currentMod.name) (lookupLocal (n, arity) localEnv)
          importNames = [mn | Ann (ModuleImport mn) _ <- currentMod.imports]
          importProviders = filter (`elem` importNames) (lookupGlobal (n, arity) exportEnv)
          matches = ownProviders ++ importProviders
       in case matches of
            [m] -> pure (Qualified m n)
            [] -> do
              tell [UnknownName loc n arity]
              pure (Unqualified n)
            ms -> do
              tell [AmbiguousName loc n arity ms]
              pure (Unqualified n)
resolveName _ _ _ _ (Qualified m n) _ = pure (Qualified m n)
