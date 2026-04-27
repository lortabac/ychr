{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}

-- |
-- Module      : YCHR.Rename
-- Description : Resolves and qualifies symbolic names across a multi-module program.
--
-- The Renamer is a whole-program pass that replaces every surface
-- 'Unqualified' callable name with a 'Qualified' one built from its
-- declaring module. Its responsibilities are:
--
-- 1. /Global environment building/: one pass over all modules collects
--    declaration, export, data-constructor, type-declaration, and
--    type-export maps (see 'RenameCtx').
--
-- 2. /Namespace resolution/ for constraints, functions, and types. Both
--    'Unqualified' and fully 'Qualified' references are subject to the
--    same visibility rules: the target must be the current module or an
--    imported module that exports the name.
--
-- 3. /Export-list validation/: every entry in a @module M(..)@ directive
--    must correspond to a real declaration in @M@.
--
-- 4. /Ambiguity enforcement/: when multiple visible providers match an
--    unqualified name, the user is forced to qualify it.
--
-- 5. /Resolution-mode handling/: whether a compound-term functor is
--    resolved to a callable depends on where it appears (head argument
--    vs. rule body vs. guard or @is@-RHS). See 'ResolveMode'.
--
-- 6. /Special cases in 'renameTerm'/: @is@, lambdas (@fun(...) -> ...@),
--    function references (@name\/arity@), and zero-arity atom promotion
--    each have their own branch.
--
-- 7. /Data-constructor warnings/: unresolved names in expression contexts
--    emit a warning unless they match a declared data constructor.
--
-- 8. /Type-definition renaming/: type names and constructor names inside
--    'TypeDefinition' values are qualified with their declaring module.
--
-- This pass guarantees that the subsequent Desugaring phase can treat the
-- program as a flat, unambiguous collection of rules.
module YCHR.Rename (renameProgram, buildExportEnv, renameQueryGoals, RenameError (..), RenameWarning (..), RenameInputs (..), defaultRenameInputs) where

import Control.Monad (when)
import Data.Foldable (traverse_)
import Data.List (nub)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Data.Text (Text)
import Effectful (Eff, runPureEff)
import Effectful.Writer.Static.Local (Writer, runWriter, tell)
import YCHR.Diagnostic (Diagnostic, noDiag)
import YCHR.PExpr (PExpr (Atom))
import YCHR.Parsed
import YCHR.Rename.Types
import YCHR.Types

data RenameError
  = AmbiguousName Text Int [Text]
  | UnknownName Text Int
  | UnknownExport Text Text Int
  | UnknownImport Text Text Int
  | -- | An @op(...)@ entry inside an import list refers to an operator
    -- that the source module does not export. Carries the source module
    -- name and the operator name.
    UnknownOperatorImport Text Text
  | -- | A @use_module(...)@ directive appears after a non-import directive
    -- (or any rule). Carries the imported module name.
    UseModuleOutOfOrder Text
  deriving (Eq, Show)

data RenameWarning
  = UndeclaredDataConstructor Text
  | DataConstructorArityMismatch Text Int
  deriving (Eq, Show)

-- | Maps data constructor names to their declared arities (from type
-- declarations). A single name may be declared at several arities across
-- different types.
type DataConEnv = Map Text [Int]

type RenameEffs = '[Writer [Diagnostic RenameWarning], Writer [Diagnostic RenameError]]

emitError :: AnnP RenameError -> Eff RenameEffs ()
emitError e = tell @[Diagnostic RenameError] [noDiag e]

emitWarning :: AnnP RenameWarning -> Eff RenameEffs ()
emitWarning w = tell @[Diagnostic RenameWarning] [noDiag w]

-- | Global environments consulted while renaming one module. Bundled
-- into a record so recursive helpers don't have to thread six parameters.
--
-- @currentModule@ is the module currently being renamed; it provides the
-- import list against which imported-name references are validated, and
-- the name used when a reference resolves to the module itself.
data RenameCtx = RenameCtx
  { declEnv :: DeclEnv,
    exportEnv :: ExportEnv,
    dataConEnv :: DataConEnv,
    typeDeclEnv :: DeclEnv,
    typeExportEnv :: ExportEnv,
    -- | Operators exported by each module, keyed by module name. Used to
    -- validate that an @op(...)@ entry in an import list names a real
    -- exported operator.
    operatorExports :: Map Text [OpDecl],
    -- | Source location at which header parsing stopped for the current
    -- module — i.e. the location of the first non-import directive.
    -- Imports beyond this location are out of order.
    currentTrailingLoc :: Maybe SourceLoc,
    currentModule :: Module
  }

-- | Inputs to 'renameProgram' beyond the module list itself. Lets the
-- caller supply per-module operator export tables and trailing-location
-- information without hard-coding additional parameters.
data RenameInputs = RenameInputs
  { -- | Map from module name to its exported operators (used to validate
    -- @op(...)@ entries inside import lists).
    riOperatorExports :: Map Text [OpDecl],
    -- | Map from module name to the source location where its header
    -- parsing stopped. Used to detect @use_module@ directives that
    -- appear after non-import content.
    riTrailingLoc :: Map Text (Maybe SourceLoc)
  }

-- | An empty 'RenameInputs' suitable for callers that do not have header
-- information (e.g. test fixtures, query renaming).
defaultRenameInputs :: RenameInputs
defaultRenameInputs =
  RenameInputs
    { riOperatorExports = Map.empty,
      riTrailingLoc = Map.empty
    }

-- ---------------------------------------------------------------------------
-- Environment building
-- ---------------------------------------------------------------------------

-- | Build a map of data-constructor names to their declared arities,
-- restricted to constructors from types in the given visible set.
-- Constructors come from type declarations and are always 'Unqualified' at
-- this point (the parser never produces qualified constructor names).
buildDataConEnv :: Set.Set (Text, Int) -> [Module] -> DataConEnv
buildDataConEnv visibleTypeSet mods =
  Map.fromListWith
    (++)
    [ (t, [length dc.conArgs])
    | m <- mods,
      Ann td _ <- m.typeDecls,
      (unqualifiedText td.name, length td.typeVars) `Set.member` visibleTypeSet,
      dc <- td.constructors,
      Unqualified t <- [dc.conName]
    ]

-- | All declared constraints and functions across all modules, indexed by
-- @(name, arity)@. Functions and constraints share a namespace, so both
-- kinds of declaration are included.
buildDeclEnv :: [Module] -> DeclEnv
buildDeclEnv mods =
  makeDeclEnv
    [ ((d.name, d.arity), [m.name])
    | m <- mods,
      Ann d _ <- m.decls
    ]

-- | Only /exported/ constraints and functions (for cross-module resolution).
-- Modules without a @module@ directive (@exports = Nothing@) export
-- everything. Operator and type export declarations are filtered out — they
-- live in separate namespaces.
buildExportEnv :: [Module] -> ExportEnv
buildExportEnv mods =
  makeExportEnv
    [ ((d.name, d.arity), [m.name])
    | m <- mods,
      d <- case m.exports of
        Nothing -> map (.node) m.decls
        Just annExports -> filter isConstraintOrFunctionDecl annExports.node
    ]

-- | All type declarations across all modules.
buildTypeDeclEnv :: [Module] -> DeclEnv
buildTypeDeclEnv mods =
  makeDeclEnv
    [ ((unqualifiedText td.name, length td.typeVars), [m.name])
    | m <- mods,
      Ann td _ <- m.typeDecls
    ]

-- | Only /exported/ types (for cross-module resolution). Modules without an
-- export list export every type they declare.
buildTypeExportEnv :: [Module] -> ExportEnv
buildTypeExportEnv mods =
  makeExportEnv
    [ ((d.name, d.arity), [m.name])
    | m <- mods,
      d <- case m.exports of
        Nothing -> [TypeExportDecl (unqualifiedText td.name) (length td.typeVars) | Ann td _ <- m.typeDecls]
        Just annExports -> filter isTypeExportDecl annExports.node
    ]

isConstraintOrFunctionDecl :: Declaration -> Bool
isConstraintOrFunctionDecl ConstraintDecl {} = True
isConstraintOrFunctionDecl FunctionDecl {} = True
isConstraintOrFunctionDecl _ = False

isTypeExportDecl :: Declaration -> Bool
isTypeExportDecl (TypeExportDecl _ _) = True
isTypeExportDecl _ = False

-- | Extract the unqualified base text of a 'Name', dropping any module
-- prefix. Unlike 'flattenName' this does /not/ round-trip — it is used for
-- keying environments and for type declarations whose 'Name' is always
-- 'Unqualified' at this point.
unqualifiedText :: Name -> Text
unqualifiedText (Unqualified t) = t
unqualifiedText (Qualified _ t) = t

-- ---------------------------------------------------------------------------
-- Entry points
-- ---------------------------------------------------------------------------

renameProgram :: RenameInputs -> [Module] -> Either [Diagnostic RenameError] ([Module], [Diagnostic RenameWarning])
renameProgram inputs mods =
  let baseCtx =
        RenameCtx
          { declEnv = buildDeclEnv mods,
            exportEnv = buildExportEnv mods,
            dataConEnv = Map.empty,
            typeDeclEnv = buildTypeDeclEnv mods,
            typeExportEnv = buildTypeExportEnv mods,
            operatorExports = inputs.riOperatorExports,
            currentTrailingLoc = Nothing,
            currentModule = error "currentModule: not yet set"
          }
      ctxFor m =
        let ctx0 =
              baseCtx
                { currentModule = m,
                  currentTrailingLoc = Map.findWithDefault Nothing m.name inputs.riTrailingLoc
                }
         in ctx0 {dataConEnv = buildDataConEnv (visibleTypes ctx0) mods}
      ((result, warnings), errs) = runPureEff . runWriter @[Diagnostic RenameError] . runWriter @[Diagnostic RenameWarning] $ do
        validateExports mods
        traverse (\m -> renameModule (ctxFor m)) mods
   in if null errs then Right (result, warnings) else Left errs

-- | Check that every name in a module's export list is actually declared.
validateExports :: [Module] -> Eff RenameEffs ()
validateExports = traverse_ validateOne
  where
    validateOne m = case m.exports of
      Nothing -> pure ()
      Just (AnnP exports loc origin) -> traverse_ (checkExport m loc origin) exports

    checkExport m loc origin d = case d of
      ConstraintDecl {name, arity}
        | not (isDeclared m name arity) -> emitError (AnnP (UnknownExport m.name name arity) loc origin)
      FunctionDecl {name, arity}
        | not (isDeclared m name arity) -> emitError (AnnP (UnknownExport m.name name arity) loc origin)
      TypeExportDecl name arity
        | not (isTypeDeclared m name arity) -> emitError (AnnP (UnknownExport m.name name arity) loc origin)
      _ -> pure ()

    isDeclared m n a = (n, a) `elem` [(d.name, d.arity) | Ann d _ <- m.decls]
    isTypeDeclared m n a = (n, a) `elem` [(unqualifiedText td.name, length td.typeVars) | Ann td _ <- m.typeDecls]

-- ---------------------------------------------------------------------------
-- Module, rule, equation, head renaming
-- ---------------------------------------------------------------------------

renameModule :: RenameCtx -> Eff RenameEffs Module
renameModule ctx = do
  let m = ctx.currentModule
  validateImportLists ctx
  renamedRules <- traverse (renameRule ctx) m.rules
  renamedEquations <- traverse (traverse (renameEquation ctx)) m.equations
  let renamedTypeDecls = map (fmap (renameTypeDefinition ctx)) m.typeDecls
      renamedDecls = map (fmap (renameDeclaration ctx)) m.decls
  pure m {rules = renamedRules, equations = renamedEquations, typeDecls = renamedTypeDecls, decls = renamedDecls}

-- | Validate import lists. Three checks:
--
--   * @op(...)@ entries must name an operator that the source module
--     actually exports ('UnknownOperatorImport').
--   * Constraint, function, and type imports must name something the
--     source module exports ('UnknownImport').
--   * Each @use_module@ directive must appear before the first non-import
--     directive in the file ('UseModuleOutOfOrder').
validateImportLists :: RenameCtx -> Eff RenameEffs ()
validateImportLists ctx =
  traverse_ checkImport ctx.currentModule.imports
  where
    checkImport (AnnP imp loc origin) = do
      checkPlacement imp loc origin
      case imp of
        ModuleImport mn (Just decls) -> traverse_ (checkItem mn loc origin) decls
        LibraryImport mn (Just decls) -> traverse_ (checkItem mn loc origin) decls
        _ -> pure ()

    checkPlacement imp loc origin = case ctx.currentTrailingLoc of
      Just tloc
        | loc.file == tloc.file,
          locAtOrAfter loc tloc ->
            emitError (AnnP (UseModuleOutOfOrder (importedModuleName imp)) loc origin)
      _ -> pure ()

    importedModuleName (ModuleImport n _) = n
    importedModuleName (LibraryImport n _) = n

    checkItem mn loc origin (OperatorDecl op) =
      when (op `notElem` Map.findWithDefault [] mn ctx.operatorExports) $
        emitError (AnnP (UnknownOperatorImport mn op.opName) loc origin)
    checkItem mn loc origin (ConstraintDecl n a _) =
      when (mn `notElem` lookupExport (n, a) ctx.exportEnv) $
        emitError (AnnP (UnknownImport mn n a) loc origin)
    checkItem mn loc origin (FunctionDecl n a _ _ _) =
      when (mn `notElem` lookupExport (n, a) ctx.exportEnv) $
        emitError (AnnP (UnknownImport mn n a) loc origin)
    checkItem mn loc origin (TypeExportDecl n a) =
      when (mn `notElem` lookupExport (n, a) ctx.typeExportEnv) $
        emitError (AnnP (UnknownImport mn n a) loc origin)

-- | True when @a@ is at or after @b@ in source order. Both locations
-- must come from the same file (caller's responsibility).
locAtOrAfter :: SourceLoc -> SourceLoc -> Bool
locAtOrAfter a b = (a.line, a.col) >= (b.line, b.col)

renameRule :: RenameCtx -> Rule -> Eff RenameEffs Rule
renameRule ctx r = do
  h <- traverse (renameHead ctx r.head.sourceLoc r.head.parsed) r.head
  g <- traverse (traverse (renameTerm ctx r.guard.sourceLoc r.guard.parsed ResolveAll)) r.guard
  b <- traverse (traverse (renameTerm ctx r.body.sourceLoc r.body.parsed ResolveTop)) r.body
  pure r {head = h, guard = g, body = b}

renameEquation :: RenameCtx -> FunctionEquation -> Eff RenameEffs FunctionEquation
renameEquation ctx eq = do
  -- Equation args don't carry their own SourceLoc; use the guard's as a proxy.
  let loc = eq.guard.sourceLoc
      origin = eq.guard.parsed
  resolvedFunName <- resolveName ResolveTop ctx loc origin eq.funName (length eq.args)
  renamedArgs <- traverse (renameTerm ctx loc origin NoResolve) eq.args
  renamedGuard <- traverse (traverse (renameTerm ctx loc origin ResolveAll)) eq.guard
  renamedRhs <- traverse (renameTerm ctx eq.rhs.sourceLoc eq.rhs.parsed ResolveAll) eq.rhs
  pure eq {funName = resolvedFunName, args = renamedArgs, guard = renamedGuard, rhs = renamedRhs}

renameHead :: RenameCtx -> SourceLoc -> PExpr -> Head -> Eff RenameEffs Head
renameHead ctx loc origin h = case h of
  Simplification cs -> Simplification <$> traverse (renameCon ctx loc origin) cs
  Propagation cs -> Propagation <$> traverse (renameCon ctx loc origin) cs
  Simpagation k r -> Simpagation <$> traverse (renameCon ctx loc origin) k <*> traverse (renameCon ctx loc origin) r

renameCon :: RenameCtx -> SourceLoc -> PExpr -> Constraint -> Eff RenameEffs Constraint
renameCon ctx loc origin (Constraint cname cargs) = do
  renamedName <- resolveName ResolveTop ctx loc origin cname (length cargs)
  renamedArgs <- traverse (renameTerm ctx loc origin NoResolve) cargs
  pure (Constraint renamedName renamedArgs)

-- ---------------------------------------------------------------------------
-- Resolution mode and term renaming
-- ---------------------------------------------------------------------------

-- | Controls how deeply name resolution is applied to a term, and how
-- unresolved names are treated.
--
-- * 'NoResolve' — head arguments and nested data terms. Names are never
--   looked up because they represent data constructors, not callable
--   entities.
--
-- * 'ResolveTop' — rule bodies. The outermost functor must be a declared
--   constraint or function (unknown names are errors). Its arguments are
--   data terms and are renamed with 'NoResolve'.
--
-- * 'ResolveAll' — guards and @is@-RHS expressions. Every nesting level
--   is resolved, but unknown names are /tolerated/ (they may be data
--   constructors like @.@ for lists). Unresolved names trigger a
--   data-constructor warning.
data ResolveMode
  = NoResolve
  | ResolveTop
  | ResolveAll
  deriving (Eq)

-- | Whether 'resolveName' should error on unresolved names. Derived from
-- 'ResolveMode': 'ResolveTop' requires declarations, 'ResolveAll' tolerates
-- missing ones, and 'NoResolve' never calls 'resolveName'.
errorOnUnknown :: ResolveMode -> Bool
errorOnUnknown ResolveTop = True
errorOnUnknown _ = False

renameTerm :: RenameCtx -> SourceLoc -> PExpr -> ResolveMode -> Term -> Eff RenameEffs Term
renameTerm ctx loc origin mode t = case t of
  -- Special case: @is@ LHS is a pattern (no resolution), RHS is an expression.
  CompoundTerm (Unqualified "is") [lhs, rhs] | mode /= NoResolve -> do
    renamedLhs <- renameTerm ctx loc origin NoResolve lhs
    renamedRhs <- renameTerm ctx loc origin ResolveAll rhs
    pure (CompoundTerm (Unqualified "is") [renamedLhs, renamedRhs])
  -- Lambda: @fun(params) -> body@. Params are variable patterns (don't resolve),
  -- the body is always an expression.
  CompoundTerm (Unqualified "->") [CompoundTerm (Unqualified "fun") params, body] | mode /= NoResolve -> do
    renamedBody <- renameTerm ctx loc origin ResolveAll body
    pure (CompoundTerm (Unqualified "->") [CompoundTerm (Unqualified "fun") params, renamedBody])
  -- Quoting: @term(X)@ suppresses resolution of functor names inside the
  -- argument so the surface-level term structure is preserved.  Variables
  -- are still renamed (they need runtime resolution), but compound-term
  -- heads stay unqualified.
  CompoundTerm (Unqualified "term") [arg] | mode /= NoResolve -> do
    renamedArg <- renameTerm ctx loc origin NoResolve arg
    pure (CompoundTerm (Unqualified "term") [renamedArg])
  -- Function reference: @fun name/arity@. Resolve the function name,
  -- then strip the @fun@ wrapper so downstream passes see bare @name/arity@.
  CompoundTerm (Unqualified "fun") [CompoundTerm (Unqualified "/") [AtomTerm fname, IntTerm farity]] | mode /= NoResolve -> do
    resolved <- resolveName ResolveAll ctx loc origin (Unqualified fname) farity
    pure (CompoundTerm (Unqualified "/") [AtomTerm (flattenName resolved), IntTerm farity])
  CompoundTerm name args -> do
    let childMode = case mode of
          NoResolve -> NoResolve
          ResolveTop -> NoResolve
          ResolveAll -> ResolveAll
    renamedArgs <- traverse (renameTerm ctx loc origin childMode) args
    newName <- case mode of
      NoResolve -> pure name
      _ -> resolveName mode ctx loc origin name (length args)
    pure (CompoundTerm newName renamedArgs)
  -- Zero-arity atom promotion: if a bare atom matches a declared
  -- constraint or function with arity 0, promote it to a 'CompoundTerm'.
  AtomTerm n | mode /= NoResolve -> do
    resolved <- resolveName ResolveAll ctx loc origin (Unqualified n) 0
    case resolved of
      Qualified _ _ -> pure (CompoundTerm resolved [])
      Unqualified _ -> pure (AtomTerm n)
  other -> pure other

-- ---------------------------------------------------------------------------
-- Name resolution
-- ---------------------------------------------------------------------------

-- | Resolve a name to a 'Qualified' one and verify its existence.
--
-- For 'Unqualified' names: the current module's own declarations are
-- checked first ('DeclEnv'), then the exports of imported modules
-- ('ExportEnv' restricted to the import list). Exactly one match is
-- required; zero matches are handled according to the 'ResolveMode', and
-- multiple matches produce an 'AmbiguousName' error.
--
-- For already-'Qualified' names: the same visibility rules apply. A
-- reference @M:n@ is accepted only if @M@ is the current module (via
-- 'DeclEnv') or if @M@ is imported and exports @n@ (via 'ExportEnv').
-- Names qualified with @\"host\"@ are external calls and bypass validation.
resolveName :: ResolveMode -> RenameCtx -> SourceLoc -> PExpr -> Name -> Int -> Eff RenameEffs Name
resolveName mode ctx loc origin (Unqualified n) arity
  | isReserved n = pure (Unqualified n)
  | otherwise =
      case visibleProviders ctx n arity of
        [m] -> pure (Qualified m n)
        [] ->
          if errorOnUnknown mode
            then do
              emitError (AnnP (UnknownName n arity) loc origin)
              pure (Unqualified n)
            else do
              warnUnknownDataCon ctx.dataConEnv loc origin n arity
              pure (Unqualified n)
        ms -> do
          emitError (AnnP (AmbiguousName n arity ms) loc origin)
          pure (Unqualified n)
-- "host"-qualified names are external calls; skip validation.
resolveName _ _ _ _ (Qualified "host" n) _ = pure (Qualified "host" n)
resolveName mode ctx loc origin (Qualified m n) arity
  | m `elem` visibleProviders ctx n arity = pure (Qualified m n)
  | otherwise =
      if errorOnUnknown mode
        then do
          emitError (AnnP (UnknownName n arity) loc origin)
          pure (Qualified m n)
        else pure (Qualified m n)

-- | All modules that can provide @(name, arity)@ to the current module:
-- the current module itself if it declares the name, plus every imported
-- module that /exports/ it.
visibleProviders :: RenameCtx -> Text -> Int -> [Text]
visibleProviders ctx n arity =
  let ownProviders = filter (== ctx.currentModule.name) (lookupDecl (n, arity) ctx.declEnv)
      imports = [(mn, il) | AnnP (ModuleImport mn il) _ _ <- ctx.currentModule.imports]
      importProviders =
        filter
          (\mn -> any (\(imn, il) -> imn == mn && importListPermits n arity il) imports)
          (lookupExport (n, arity) ctx.exportEnv)
   in -- Deduplicate: multiple declarations with the same name/arity in
      -- one module (e.g., overloaded function signatures) are not ambiguous.
      nub (ownProviders ++ importProviders)

-- | Check whether a name/arity is permitted by an import list.
-- 'Nothing' means import everything; 'Just' restricts to listed items.
importListPermits :: Text -> Int -> Maybe [Declaration] -> Bool
importListPermits _ _ Nothing = True
importListPermits n arity (Just decls) = any match decls
  where
    match (ConstraintDecl dn da _) = dn == n && da == arity
    match (FunctionDecl dn da _ _ _) = dn == n && da == arity
    match _ = False

-- | Check whether a type name/arity is permitted by an import list.
importListPermitsType :: Text -> Int -> Maybe [Declaration] -> Bool
importListPermitsType _ _ Nothing = True
importListPermitsType n arity (Just decls) = any match decls
  where
    match (TypeExportDecl tn ta) = tn == n && ta == arity
    match _ = False

-- | All @(typeName, typeArity)@ pairs visible to the current module: types
-- declared locally plus types exported by imported modules (filtered by the
-- import list). Used to scope 'DataConEnv' so that only constructors from
-- visible types suppress the 'UndeclaredDataConstructor' warning.
visibleTypes :: RenameCtx -> Set.Set (Text, Int)
visibleTypes ctx =
  Set.fromList
    [ key
    | (key, ms) <- toListDecl ctx.typeDeclEnv,
      not (null (ownProviders ms ++ importProviders key))
    ]
  where
    ownProviders ms = filter (== ctx.currentModule.name) ms
    imports = [(mn, il) | AnnP (ModuleImport mn il) _ _ <- ctx.currentModule.imports]
    importProviders (n, arity) =
      filter
        (\mn -> any (\(imn, il) -> imn == mn && importListPermitsType n arity il) imports)
        (lookupExport (n, arity) ctx.typeExportEnv)

-- | Check an unresolved name against data-constructor declarations.
-- If found with matching arity: silent. If found with wrong arity: warning.
-- If not found at all: warning.
warnUnknownDataCon :: DataConEnv -> SourceLoc -> PExpr -> Text -> Int -> Eff RenameEffs ()
warnUnknownDataCon dataConEnv loc origin n arity =
  case Map.lookup n dataConEnv of
    Just arities
      | arity `elem` arities -> pure ()
      | otherwise -> emitWarning (AnnP (DataConstructorArityMismatch n arity) loc origin)
    Nothing -> emitWarning (AnnP (UndeclaredDataConstructor n) loc origin)

-- ---------------------------------------------------------------------------
-- Type definition renaming
-- ---------------------------------------------------------------------------

-- | Rename a type definition: qualify the type name and constructor names
-- with the declaring module, and resolve type references in constructor
-- arguments.
--
-- Pure (not in 'Eff'): type renaming never fails — unknown types simply
-- stay 'Unqualified' so the interpreter can decide what to do with them
-- (e.g. built-in @int@). If type errors are introduced later this will
-- need to move into 'Eff RenameEffs'.
renameTypeDefinition :: RenameCtx -> TypeDefinition -> TypeDefinition
renameTypeDefinition ctx td =
  TypeDefinition
    { name = Qualified ctx.currentModule.name (unqualifiedText td.name),
      typeVars = td.typeVars,
      constructors = map (renameDataConstructor ctx) td.constructors
    }

renameDataConstructor :: RenameCtx -> DataConstructor -> DataConstructor
renameDataConstructor ctx dc =
  DataConstructor
    { conName = Qualified ctx.currentModule.name (unqualifiedText dc.conName),
      conArgs = map (renameTypeExpr ctx) dc.conArgs
    }

renameDeclaration :: RenameCtx -> Declaration -> Declaration
renameDeclaration ctx d@ConstraintDecl {argTypes} =
  d {argTypes = fmap (map (renameTypeExpr ctx)) argTypes}
renameDeclaration ctx d@FunctionDecl {argTypes, returnType} =
  d {argTypes = fmap (map (renameTypeExpr ctx)) argTypes, returnType = fmap (renameTypeExpr ctx) returnType}
renameDeclaration _ d = d

renameTypeExpr :: RenameCtx -> TypeExpr -> TypeExpr
renameTypeExpr _ (TypeVar v) = TypeVar v
renameTypeExpr ctx (TypeCon n args) =
  TypeCon
    (resolveTypeName ctx (unqualifiedText n) (length args))
    (map (renameTypeExpr ctx) args)

-- | Resolve a type name against the type declaration and export
-- environments. Unknown types (e.g., the built-in @int@) are kept
-- 'Unqualified'.
resolveTypeName :: RenameCtx -> Text -> Int -> Name
resolveTypeName ctx n arity =
  let ownProviders = filter (== ctx.currentModule.name) (lookupDecl (n, arity) ctx.typeDeclEnv)
      imports = [(mn, il) | AnnP (ModuleImport mn il) _ _ <- ctx.currentModule.imports]
      importProviders =
        filter
          (\mn -> any (\(imn, il) -> imn == mn && importListPermitsType n arity il) imports)
          (lookupExport (n, arity) ctx.typeExportEnv)
      matches = ownProviders ++ importProviders
   in case matches of
        [m] -> Qualified m n
        _ -> Unqualified n

-- ---------------------------------------------------------------------------
-- Query renaming
-- ---------------------------------------------------------------------------

-- | Rename a list of query goal terms using all modules as the visible
-- scope. Each term is renamed at 'ResolveTop' level (same as rule bodies).
-- Returns 'Left' if any rename errors occur.
renameQueryGoals :: [Module] -> [Term] -> Either [Diagnostic RenameError] ([Term], [Diagnostic RenameWarning])
renameQueryGoals mods goals =
  let queryMod =
        Module
          { name = "<query>",
            imports = [noAnnP (ModuleImport m.name Nothing) | m <- mods],
            decls = [],
            typeDecls = [],
            rules = [],
            equations = [],
            exports = Nothing
          }
      ctx0 =
        RenameCtx
          { declEnv = buildDeclEnv mods,
            exportEnv = buildExportEnv mods,
            dataConEnv = Map.empty,
            typeDeclEnv = buildTypeDeclEnv mods,
            typeExportEnv = buildTypeExportEnv mods,
            operatorExports = Map.empty,
            currentTrailingLoc = Nothing,
            currentModule = queryMod
          }
      ctx = ctx0 {dataConEnv = buildDataConEnv (visibleTypes ctx0) mods}
      ((renamed, warnings), errs) =
        runPureEff . runWriter @[Diagnostic RenameError] . runWriter @[Diagnostic RenameWarning] $
          traverse (renameTerm ctx dummyLoc (Atom "") ResolveTop) goals
   in if null errs then Right (renamed, warnings) else Left errs

{- ---------------------------------------------------------------------------
Notes
-----------------------------------------------------------------------------

Why 'reservedSymbolSet' exists as a safety net in 'resolveName' even though
@is@, @->@, and @/@ are already handled by early special cases in
'renameTerm': those special cases only match specific shapes (@is/2@,
@->/2@ with a @fun(...)@ LHS, @//2@ with atom+int args). Any other shape
falls through to the default compound-term branch, where the reserved
check keeps them 'Unqualified' rather than producing a spurious
'UnknownName' error.

Why the @is@ LHS is renamed with 'NoResolve' while its RHS uses
'ResolveAll': the LHS is a pattern (typically a single variable or a data
term to unify with) and does not contain callable references, whereas the
RHS is an arbitrary expression.

Why a bare atom in expression position can emit an
'UndeclaredDataConstructor' warning: in CHR, bare atoms are used as
zero-arity data constructors, so the renamer treats them as such. If an
atom is instead declared as a zero-arity constraint or function, it is
/promoted/ to a 'CompoundTerm' before the warning path runs.

Why 'renameTypeDefinition' is pure while the rule/equation helpers live in
'Eff': type renaming currently emits no errors or warnings (unknown types
fall through as 'Unqualified'). If type checking is introduced later,
these helpers will need to move into 'Eff RenameEffs'.
--------------------------------------------------------------------------- -}
