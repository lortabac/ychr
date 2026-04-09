{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}

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
module YCHR.Rename (renameProgram, buildExportEnv, renameQueryGoals, RenameError (..), RenameWarning (..)) where

import Data.Foldable (traverse_)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
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

data RenameWarning
  = UndeclaredDataConstructor SourceLoc Text
  | DataConstructorArityMismatch SourceLoc Text Int
  deriving (Eq, Show)

-- | Maps data constructor names to their declared arities (from type declarations).
type DataConEnv = Map Text [Int]

-- | Build a global map of data constructor names to arities from all type declarations.
buildDataConEnv :: [Module] -> DataConEnv
buildDataConEnv mods =
  Map.fromListWith
    (++)
    [ (n, [length dc.conArgs])
    | m <- mods,
      Ann td _ <- m.typeDecls,
      dc <- td.constructors,
      n <- nameText dc.conName
    ]
  where
    nameText (Unqualified t) = [t]
    nameText (Qualified _ _) = []

type RenameEffs = '[Writer [RenameWarning], Writer [RenameError]]

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
-- Operator and type export declarations are filtered out (separate namespaces).
-- Functions and constraints share a namespace, so both kinds are included.
buildExportEnv :: [Module] -> ExportEnv
buildExportEnv mods =
  makeExportEnv
    [ ((d.name, d.arity), [m.name])
    | m <- mods,
      d <- case m.exports of
        Nothing -> map (.node) m.decls
        Just exports -> filter isConstraintOrFunctionDecl exports
    ]

-- | All type declarations across all modules.
buildTypeDeclEnv :: [Module] -> DeclEnv
buildTypeDeclEnv mods =
  makeDeclEnv
    [ ((nameToText td.name, length td.typeVars), [m.name])
    | m <- mods,
      Ann td _ <- m.typeDecls
    ]

-- | Only exported types (for cross-module resolution).
-- Modules without an export list export all their types.
buildTypeExportEnv :: [Module] -> ExportEnv
buildTypeExportEnv mods =
  makeExportEnv
    [ ((d.name, d.arity), [m.name])
    | m <- mods,
      d <- case m.exports of
        Nothing -> [TypeExportDecl (nameToText td.name) (length td.typeVars) | Ann td _ <- m.typeDecls]
        Just exports -> filter isTypeExportDecl exports
    ]

isConstraintOrFunctionDecl :: Declaration -> Bool
isConstraintOrFunctionDecl ConstraintDecl {} = True
isConstraintOrFunctionDecl FunctionDecl {} = True
isConstraintOrFunctionDecl _ = False

isTypeExportDecl :: Declaration -> Bool
isTypeExportDecl (TypeExportDecl _ _) = True
isTypeExportDecl _ = False

nameToText :: Name -> Text
nameToText (Unqualified t) = t
nameToText (Qualified _ t) = t

renameProgram :: [Module] -> Either [RenameError] ([Module], [RenameWarning])
renameProgram mods =
  let declEnv = buildDeclEnv mods
      exportEnv = buildExportEnv mods
      dataConEnv = buildDataConEnv mods
      typeDeclEnv = buildTypeDeclEnv mods
      typeExportEnv = buildTypeExportEnv mods
      ((result, warnings), errs) = runPureEff . runWriter @[RenameError] . runWriter @[RenameWarning] $ do
        validateExports mods
        traverse (renameModule declEnv exportEnv dataConEnv typeDeclEnv typeExportEnv) mods
   in if null errs then Right (result, warnings) else Left errs

-- | Check that every name in a module's export list is actually declared.
validateExports :: [Module] -> Eff RenameEffs ()
validateExports mods =
  let constraintsDeclaredIn m = [(d.name, d.arity) | Ann d _ <- m.decls]
      typesDeclaredIn m = [(nameToText td.name, length td.typeVars) | Ann td _ <- m.typeDecls]
   in traverse_
        ( \m -> case m.exports of
            Nothing -> pure ()
            Just exports ->
              traverse_
                ( \d -> case d of
                    ConstraintDecl {name = n, arity = a}
                      | (n, a) `notElem` constraintsDeclaredIn m ->
                          tell @[RenameError] [UnknownExport m.name n a]
                    FunctionDecl {name = n, arity = a}
                      | (n, a) `notElem` constraintsDeclaredIn m ->
                          tell @[RenameError] [UnknownExport m.name n a]
                    TypeExportDecl n a
                      | (n, a) `notElem` typesDeclaredIn m ->
                          tell @[RenameError] [UnknownExport m.name n a]
                    _ -> pure ()
                )
                exports
        )
        mods

renameModule :: DeclEnv -> ExportEnv -> DataConEnv -> DeclEnv -> ExportEnv -> Module -> Eff RenameEffs Module
renameModule declEnv exportEnv dcEnv typeDeclEnv typeExportEnv m = do
  renamedRules <- traverse (renameRule declEnv exportEnv dcEnv m) m.rules
  renamedEquations <- traverse (traverse (renameEquation declEnv exportEnv dcEnv m)) m.equations
  let renamedTypeDecls = map (fmap (renameTypeDefinition typeDeclEnv typeExportEnv m)) m.typeDecls
  pure m {rules = renamedRules, equations = renamedEquations, typeDecls = renamedTypeDecls}

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

renameRule :: DeclEnv -> ExportEnv -> DataConEnv -> Module -> Rule -> Eff RenameEffs Rule
renameRule declEnv exportEnv dcEnv m r = do
  h <- traverse (renameHead declEnv exportEnv dcEnv m r.head.sourceLoc) r.head
  g <- traverse (traverse (renameTerm declEnv exportEnv dcEnv m r.guard.sourceLoc ResolveAll)) r.guard
  b <- traverse (traverse (renameTerm declEnv exportEnv dcEnv m r.body.sourceLoc ResolveTop)) r.body
  pure r {head = h, guard = g, body = b}

renameEquation :: DeclEnv -> ExportEnv -> DataConEnv -> Module -> FunctionEquation -> Eff RenameEffs FunctionEquation
renameEquation declEnv exportEnv dcEnv m eq = do
  -- Equation args don't carry their own SourceLoc; use the guard's as a proxy.
  let loc = eq.guard.sourceLoc
  renamedArgs <- traverse (renameTerm declEnv exportEnv dcEnv m loc NoResolve) eq.args
  renamedGuard <- traverse (traverse (renameTerm declEnv exportEnv dcEnv m loc ResolveAll)) eq.guard
  renamedRhs <- traverse (renameTerm declEnv exportEnv dcEnv m eq.rhs.sourceLoc ResolveAll) eq.rhs
  pure eq {args = renamedArgs, guard = renamedGuard, rhs = renamedRhs}

renameHead :: DeclEnv -> ExportEnv -> DataConEnv -> Module -> SourceLoc -> Head -> Eff RenameEffs Head
renameHead declEnv exportEnv dcEnv m loc h = case h of
  Simplification cs -> Simplification <$> traverse (renameCon declEnv exportEnv dcEnv m loc) cs
  Propagation cs -> Propagation <$> traverse (renameCon declEnv exportEnv dcEnv m loc) cs
  Simpagation k r -> Simpagation <$> traverse (renameCon declEnv exportEnv dcEnv m loc) k <*> traverse (renameCon declEnv exportEnv dcEnv m loc) r

renameCon :: DeclEnv -> ExportEnv -> DataConEnv -> Module -> SourceLoc -> Constraint -> Eff RenameEffs Constraint
renameCon declEnv exportEnv dcEnv m loc (Constraint cname cargs) = do
  renamedName <- resolveName ErrorOnUnknownName declEnv exportEnv dcEnv m loc cname (length cargs)
  renamedArgs <- traverse (renameTerm declEnv exportEnv dcEnv m loc NoResolve) cargs
  pure (Constraint renamedName renamedArgs)

renameTerm :: DeclEnv -> ExportEnv -> DataConEnv -> Module -> SourceLoc -> ResolveMode -> Term -> Eff RenameEffs Term
renameTerm declEnv exportEnv dcEnv m loc mode t = case t of
  -- Special case: @is@ passes 'ResolveAll' to its RHS expression.
  CompoundTerm (Unqualified "is") [lhs, rhs] | mode /= NoResolve -> do
    renamedLhs <- renameTerm declEnv exportEnv dcEnv m loc NoResolve lhs
    renamedRhs <- renameTerm declEnv exportEnv dcEnv m loc ResolveAll rhs
    pure (CompoundTerm (Unqualified "is") [renamedLhs, renamedRhs])
  -- Lambda: fun(params) -> body.  Params are variable patterns (don't resolve).
  CompoundTerm (Unqualified "->") [CompoundTerm (Unqualified "fun") params, body] | mode /= NoResolve -> do
    renamedBody <- renameTerm declEnv exportEnv dcEnv m loc ResolveAll body
    pure (CompoundTerm (Unqualified "->") [CompoundTerm (Unqualified "fun") params, renamedBody])
  -- Function reference: resolve the function name.
  CompoundTerm (Unqualified "/") [AtomTerm fname, IntTerm farity] | mode /= NoResolve -> do
    resolved <- resolveName AcceptUnknownName declEnv exportEnv dcEnv m loc (Unqualified fname) farity
    pure (CompoundTerm (Unqualified "/") [AtomTerm (flattenName resolved), IntTerm farity])
  CompoundTerm name args -> do
    let childMode = case mode of
          NoResolve -> NoResolve
          ResolveTop -> NoResolve
          ResolveAll -> ResolveAll
    renamedArgs <- traverse (renameTerm declEnv exportEnv dcEnv m loc childMode) args
    newName <- case mode of
      NoResolve -> pure name
      ResolveTop -> resolveName ErrorOnUnknownName declEnv exportEnv dcEnv m loc name (length args)
      ResolveAll -> resolveName AcceptUnknownName declEnv exportEnv dcEnv m loc name (length args)
    pure (CompoundTerm newName renamedArgs)
  -- Zero-arity atom promotion: if a bare atom matches a declared
  -- constraint or function with arity 0, promote it to CompoundTerm.
  AtomTerm n | mode /= NoResolve -> do
    resolved <- resolveName AcceptUnknownName declEnv exportEnv dcEnv m loc (Unqualified n) 0
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
resolveName :: UnknownNamePolicy -> DeclEnv -> ExportEnv -> DataConEnv -> Module -> SourceLoc -> Name -> Int -> Eff RenameEffs Name
resolveName policy declEnv exportEnv dcEnv currentMod loc (Unqualified n) arity
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
                tell @[RenameError] [UnknownName loc n arity]
                pure (Unqualified n)
              AcceptUnknownName -> do
                warnUnknownDataCon dcEnv loc n arity
                pure (Unqualified n)
            ms -> do
              tell @[RenameError] [AmbiguousName loc n arity ms]
              pure (Unqualified n)
-- "host"-qualified names are external calls; skip validation.
resolveName _ _ _ _ _ _ (Qualified "host" n) _ = pure (Qualified "host" n)
resolveName policy declEnv _ _ _ loc (Qualified m n) arity
  | m `elem` lookupDecl (n, arity) declEnv = pure (Qualified m n)
  | otherwise = case policy of
      ErrorOnUnknownName -> do
        tell @[RenameError] [UnknownName loc n arity]
        pure (Qualified m n)
      AcceptUnknownName -> pure (Qualified m n)

-- | Check an unresolved name against data constructor declarations.
-- If found with matching arity: silent. If found with wrong arity: warning.
-- If not found at all: warning.
warnUnknownDataCon :: DataConEnv -> SourceLoc -> Text -> Int -> Eff RenameEffs ()
warnUnknownDataCon dcEnv loc n arity =
  case Map.lookup n dcEnv of
    Just arities
      | arity `elem` arities -> pure ()
      | otherwise -> tell @[RenameWarning] [DataConstructorArityMismatch loc n arity]
    Nothing -> tell @[RenameWarning] [UndeclaredDataConstructor loc n]

-- ---------------------------------------------------------------------------
-- Type definition renaming
-- ---------------------------------------------------------------------------

-- | Rename a type definition: qualify the type name and constructor names
-- with the declaring module, and resolve type references in constructor args.
renameTypeDefinition :: DeclEnv -> ExportEnv -> Module -> TypeDefinition -> TypeDefinition
renameTypeDefinition typeDeclEnv typeExportEnv m td =
  TypeDefinition
    { name = Qualified m.name (nameToText td.name),
      typeVars = td.typeVars,
      constructors = map (renameDataConstructor typeDeclEnv typeExportEnv m) td.constructors
    }

renameDataConstructor :: DeclEnv -> ExportEnv -> Module -> DataConstructor -> DataConstructor
renameDataConstructor typeDeclEnv typeExportEnv m dc =
  DataConstructor
    { conName = Qualified m.name (nameToText dc.conName),
      conArgs = map (renameTypeExpr typeDeclEnv typeExportEnv m) dc.conArgs
    }

renameTypeExpr :: DeclEnv -> ExportEnv -> Module -> TypeExpr -> TypeExpr
renameTypeExpr _ _ _ (TypeVar v) = TypeVar v
renameTypeExpr typeDeclEnv typeExportEnv m (TypeCon n args) =
  TypeCon
    (resolveTypeName typeDeclEnv typeExportEnv m (nameToText n) (length args))
    (map (renameTypeExpr typeDeclEnv typeExportEnv m) args)

-- | Resolve a type name against the type declaration and export environments.
-- Unknown types (e.g., built-in @int@) are kept 'Unqualified'.
resolveTypeName :: DeclEnv -> ExportEnv -> Module -> Text -> Int -> Name
resolveTypeName typeDeclEnv typeExportEnv currentMod n arity =
  let ownProviders = filter (== currentMod.name) (lookupDecl (n, arity) typeDeclEnv)
      importNames = [mn | Ann (ModuleImport mn) _ <- currentMod.imports]
      importProviders = filter (`elem` importNames) (lookupExport (n, arity) typeExportEnv)
      matches = ownProviders ++ importProviders
   in case matches of
        [m] -> Qualified m n
        _ -> Unqualified n

-- ---------------------------------------------------------------------------
-- Query renaming
-- ---------------------------------------------------------------------------

-- | Rename a list of query goal terms using all modules as the visible scope.
-- Each term is renamed at 'ResolveTop' level (same as rule bodies).
-- Returns 'Left' if any rename errors occur.
renameQueryGoals :: [Module] -> [Term] -> Either [RenameError] ([Term], [RenameWarning])
renameQueryGoals mods goals =
  let declEnv = buildDeclEnv mods
      exportEnv = buildExportEnv mods
      dataConEnv = buildDataConEnv mods
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
      ((renamed, warnings), errs) =
        runPureEff . runWriter @[RenameError] . runWriter @[RenameWarning] $
          traverse (renameTerm declEnv exportEnv dataConEnv queryMod dummyLoc ResolveTop) goals
   in if null errs then Right (renamed, warnings) else Left errs
