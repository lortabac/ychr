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
module YCHR.Rename (renameProgram, buildExportEnv, renameQueryGoals, RenameError (..)) where

import Data.Foldable (traverse_)
import Data.Text (Text)
import Effectful (Eff, runPureEff)
import Effectful.Writer.Static.Local (Writer, runWriter, tell)
import YCHR.Parsed
import YCHR.Rename.Types
import YCHR.Types

data RenameError
  = AmbiguousName SourceLoc Text Int [Text]
  | UnknownName SourceLoc Text Int
  | UnknownExport Text Text Int
  deriving (Eq, Show)

-- | All declared constraints and functions across all modules.
-- Resolution to the current module is done later in 'resolveName'.
-- Functions and constraints share a namespace, so both 'ConstraintDecl'
-- and 'FunctionDecl' entries are included.
buildDeclEnv :: [Module] -> DeclEnv
buildDeclEnv mods =
  makeDeclEnv
    [ ((d.name, d.arity), [m.name])
    | m <- mods,
      Ann d _ <- m.decls
    ]

-- | Only exported constraints and functions (for cross-module resolution).
-- Modules without a @module@ directive (modExports = Nothing) export everything.
-- Operator declarations are filtered out since they are not named entities.
-- Functions and constraints share a namespace, so both kinds are included.
buildExportEnv :: [Module] -> ExportEnv
buildExportEnv mods =
  makeExportEnv
    [ ((d.name, d.arity), [m.name])
    | m <- mods,
      d <- case m.exports of
        Nothing -> map (.node) m.decls
        Just exports -> filter (not . isOperatorDecl) exports
    ]

isOperatorDecl :: Declaration -> Bool
isOperatorDecl (OperatorDecl _) = True
isOperatorDecl _ = False

renameProgram :: [Module] -> Either [RenameError] [Module]
renameProgram mods =
  let declEnv = buildDeclEnv mods
      exportEnv = buildExportEnv mods
      (result, errs) = runPureEff . runWriter $ do
        validateExports mods
        traverse (renameModule declEnv exportEnv) mods
   in if null errs then Right result else Left errs

-- | Check that every name in a module's export list is actually declared.
validateExports :: [Module] -> Eff '[Writer [RenameError]] ()
validateExports mods =
  let declaredIn m = [(d.name, d.arity) | Ann d _ <- m.decls]
   in traverse_
        ( \m -> case m.exports of
            Nothing -> pure ()
            Just exports ->
              traverse_
                ( \d ->
                    if not (isOperatorDecl d) && (d.name, d.arity) `notElem` declaredIn m
                      then tell [UnknownExport m.name d.name d.arity]
                      else pure ()
                )
                exports
        )
        mods

renameModule :: DeclEnv -> ExportEnv -> Module -> Eff '[Writer [RenameError]] Module
renameModule declEnv exportEnv m = do
  renamedRules <- traverse (renameRule declEnv exportEnv m) m.rules
  renamedEquations <- traverse (traverse (renameEquation declEnv exportEnv m)) m.equations
  pure m {rules = renamedRules, equations = renamedEquations}

-- | Controls how deeply name resolution is applied.
--
-- The mode determines both the recursion depth and the 'UnknownNamePolicy':
--
-- * 'NoResolve': head arguments and nested data terms — names are never
--   looked up because they represent data constructors, not callable entities.
--
-- * 'ResolveTop': rule bodies — the outermost functor must be a declared
--   constraint ('ErrorOnUnknownName'), but its arguments are data terms
--   (children get 'NoResolve').
--
-- * 'ResolveAll': guards and @is@ RHS — every nesting level is resolved,
--   but unknown names are tolerated ('AcceptUnknownName') because they may
--   be data constructors (e.g., @.@ for lists).
data ResolveMode
  = NoResolve
  | ResolveTop
  | ResolveAll
  deriving (Eq)

-- | Controls whether an unresolved name is an error or silently kept.
data UnknownNamePolicy
  = -- | Emit 'UnknownName' (constraints, body goals — must be declared).
    ErrorOnUnknownName
  | -- | Leave 'Unqualified' without error (expression context — may be a data constructor).
    AcceptUnknownName

renameRule :: DeclEnv -> ExportEnv -> Module -> Rule -> Eff '[Writer [RenameError]] Rule
renameRule declEnv exportEnv m r = do
  h <- traverse (renameHead declEnv exportEnv m r.head.sourceLoc) r.head
  g <- traverse (traverse (renameTerm declEnv exportEnv m r.guard.sourceLoc ResolveAll)) r.guard
  b <- traverse (traverse (renameTerm declEnv exportEnv m r.body.sourceLoc ResolveTop)) r.body
  pure r {head = h, guard = g, body = b}

renameEquation :: DeclEnv -> ExportEnv -> Module -> FunctionEquation -> Eff '[Writer [RenameError]] FunctionEquation
renameEquation declEnv exportEnv m eq = do
  -- Equation args don't carry their own SourceLoc; use the guard's as a proxy.
  let loc = eq.guard.sourceLoc
  renamedArgs <- traverse (renameTerm declEnv exportEnv m loc NoResolve) eq.args
  renamedGuard <- traverse (traverse (renameTerm declEnv exportEnv m loc ResolveAll)) eq.guard
  renamedRhs <- traverse (renameTerm declEnv exportEnv m eq.rhs.sourceLoc ResolveAll) eq.rhs
  pure eq {args = renamedArgs, guard = renamedGuard, rhs = renamedRhs}

renameHead :: DeclEnv -> ExportEnv -> Module -> SourceLoc -> Head -> Eff '[Writer [RenameError]] Head
renameHead declEnv exportEnv m loc h = case h of
  Simplification cs -> Simplification <$> traverse (renameCon declEnv exportEnv m loc) cs
  Propagation cs -> Propagation <$> traverse (renameCon declEnv exportEnv m loc) cs
  Simpagation k r -> Simpagation <$> traverse (renameCon declEnv exportEnv m loc) k <*> traverse (renameCon declEnv exportEnv m loc) r

renameCon :: DeclEnv -> ExportEnv -> Module -> SourceLoc -> Constraint -> Eff '[Writer [RenameError]] Constraint
renameCon declEnv exportEnv m loc (Constraint cname cargs) = do
  renamedName <- resolveName ErrorOnUnknownName declEnv exportEnv m loc cname (length cargs)
  renamedArgs <- traverse (renameTerm declEnv exportEnv m loc NoResolve) cargs
  pure (Constraint renamedName renamedArgs)

renameTerm :: DeclEnv -> ExportEnv -> Module -> SourceLoc -> ResolveMode -> Term -> Eff '[Writer [RenameError]] Term
renameTerm declEnv exportEnv m loc mode t = case t of
  -- Special case: @is@ passes 'ResolveAll' to its RHS expression.
  CompoundTerm (Unqualified "is") [lhs, rhs] | mode /= NoResolve -> do
    renamedLhs <- renameTerm declEnv exportEnv m loc NoResolve lhs
    renamedRhs <- renameTerm declEnv exportEnv m loc ResolveAll rhs
    pure (CompoundTerm (Unqualified "is") [renamedLhs, renamedRhs])
  CompoundTerm name args -> do
    let childMode = case mode of
          NoResolve -> NoResolve
          ResolveTop -> NoResolve
          ResolveAll -> ResolveAll
    renamedArgs <- traverse (renameTerm declEnv exportEnv m loc childMode) args
    newName <- case mode of
      NoResolve -> pure name
      ResolveTop -> resolveName ErrorOnUnknownName declEnv exportEnv m loc name (length args)
      ResolveAll -> resolveName AcceptUnknownName declEnv exportEnv m loc name (length args)
    pure (CompoundTerm newName renamedArgs)
  -- Zero-arity atom promotion: if a bare atom matches a declared
  -- constraint or function with arity 0, promote it to CompoundTerm.
  AtomTerm n | mode /= NoResolve -> do
    resolved <- resolveName AcceptUnknownName declEnv exportEnv m loc (Unqualified n) 0
    case resolved of
      Qualified _ _ -> pure (CompoundTerm resolved [])
      Unqualified _ -> pure (AtomTerm n)
  other -> pure other

-- | Resolve a name to a 'Qualified' one and verify its existence.
--
-- For 'Unqualified' names: the current module's own declarations (via
-- 'DeclEnv') are checked first, then declarations exported by imported
-- modules (via 'ExportEnv'). Exactly one match is required; zero matches
-- are handled according to 'UnknownNamePolicy', and multiple matches
-- produce an 'AmbiguousName' error.
--
-- For already-'Qualified' names: verifies the name exists in either
-- 'DeclEnv' or 'ExportEnv' with the stated module. Names qualified with
-- @\"host\"@ are external calls and bypass validation.
resolveName :: UnknownNamePolicy -> DeclEnv -> ExportEnv -> Module -> SourceLoc -> Name -> Int -> Eff '[Writer [RenameError]] Name
resolveName policy declEnv exportEnv currentMod loc (Unqualified n) arity
  | isReserved n reservedSymbols = pure (Unqualified n)
  | otherwise =
      let ownProviders = filter (== currentMod.name) (lookupDecl (n, arity) declEnv)
          importNames = [mn | Ann (ModuleImport mn) _ <- currentMod.imports]
          importProviders = filter (`elem` importNames) (lookupExport (n, arity) exportEnv)
          matches = ownProviders ++ importProviders
       in case matches of
            [m] -> pure (Qualified m n)
            [] -> case policy of
              ErrorOnUnknownName -> do
                tell [UnknownName loc n arity]
                pure (Unqualified n)
              AcceptUnknownName -> pure (Unqualified n)
            ms -> do
              tell [AmbiguousName loc n arity ms]
              pure (Unqualified n)
-- "host"-qualified names are external calls; skip validation.
resolveName _ _ _ _ _ (Qualified "host" n) _ = pure (Qualified "host" n)
resolveName policy declEnv _ _ loc (Qualified m n) arity
  | m `elem` lookupDecl (n, arity) declEnv = pure (Qualified m n)
  | otherwise = case policy of
      ErrorOnUnknownName -> do
        tell [UnknownName loc n arity]
        pure (Qualified m n)
      AcceptUnknownName -> pure (Qualified m n)

-- | Rename a list of query goal terms using all modules as the visible scope.
-- Each term is renamed at 'ResolveTop' level (same as rule bodies).
-- Returns 'Left' if any rename errors occur.
renameQueryGoals :: [Module] -> [Term] -> Either [RenameError] [Term]
renameQueryGoals mods goals =
  let declEnv = buildDeclEnv mods
      exportEnv = buildExportEnv mods
      queryMod =
        Module
          { name = "<query>",
            imports = [noAnn (ModuleImport m.name) | m <- mods],
            decls = [],
            typeDecls = [],
            rules = [],
            equations = [],
            exports = Nothing
          }
      (renamed, errs) =
        runPureEff . runWriter $
          traverse (renameTerm declEnv exportEnv queryMod dummyLoc ResolveTop) goals
   in if null errs then Right renamed else Left errs
