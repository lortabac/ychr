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
module YCHR.Rename
  ( -- * Entry points
    renameProgram,
    renameQueryGoals,
    renameQueryArgs,
    buildExportEnv,

    -- * Errors and warnings
    RenameError (..),
    RenameWarning (..),

    -- * Configuration
    RenameInputs (..),
    defaultRenameInputs,
  )
where

import Control.Monad (when)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Writer.CPS (Writer, WriterT, runWriter, runWriterT, tell)
import Data.Foldable (traverse_)
import Data.List (nub)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Data.Text (Text)
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
  | -- | A qualified reference @M:n/a@ that is not in scope: either the
    -- module is not imported, the name is not exported by it, or the
    -- name is excluded by the import list. Carries the source module
    -- name, the name, and the arity.
    NotExportedByModule Text Text Int
  | -- | An @op(...)@ entry inside an import list refers to an operator
    -- that the source module does not export. Carries the source module
    -- name and the operator name.
    UnknownOperatorImport Text Text
  | -- | A @use_module(...)@ directive appears after a non-import directive
    -- (or any rule). Carries the imported module name.
    UseModuleOutOfOrder Text
  | -- | A @type(t/n, [c, ...])@ export or import entry names a constructor
    -- that is not declared on type @t@. Carries the source module name,
    -- the type name, the type arity, and the offending constructor name.
    UnknownExportedConstructor Text Text Int Text
  | -- | A qualified compound term @M:c/a@ names a data constructor that
    -- @M@ declares but does not export (per the @type(t/n, [...])@
    -- allowlist in @M@'s module header). Carries the source module
    -- name, the constructor name, and the arity.
    NonExportedConstructor Text Text Int
  | -- | A @type(t/n, [c, ...])@ entry in a @use_module@ import list
    -- names a constructor that @M@ declares on @t@ but does not export.
    -- Distinct from 'UnknownExportedConstructor' (which fires when the
    -- constructor is genuinely not declared). Carries the source module
    -- name, the type name, the type arity, and the offending
    -- constructor name.
    ConstructorNotExported Text Text Int Text
  | -- | An unqualified bare reference to a data constructor that is
    -- exported by more than one visible module. Parallel to
    -- 'AmbiguousName' (YCHR-20001) for the function/constraint
    -- namespace, but without arity: data constructors are not
    -- arity-overloadable, so the name alone identifies the clash.
    -- Carries the constructor name and the list of providers.
    AmbiguousDataConstructor Text [Text]
  deriving (Eq, Show)

data RenameWarning
  = UndeclaredDataConstructor Text
  | DataConstructorArityMismatch Text Int
  deriving (Eq, Show)

-- | Maps data constructor names to their declared arities (from type
-- declarations). A single name may be declared at several arities across
-- different types.
type DataConEnv = Map Text [Int]

-- | Maps @(constructorName, arity)@ to the list of modules that declare it.
-- Built from the same declarations as 'DataConEnv' but indexed and valued
-- so the renamer can canonicalize bare uses of declared constructors to
-- their qualified form (the runtime then sees one canonical flat atom).
type DataConProviders = Map (Text, Int) [Text]

-- | Identifier for a type declaration: declaring module + type name + arity.
-- Used as the key of constructor-visibility maps so that two distinct
-- types with the same unqualified name (in different modules) don't
-- collide.
data DeclaredType = DeclaredType
  { declaringModule :: Text,
    typeName :: Text,
    typeArity :: Int
  }
  deriving (Eq, Ord, Show)

-- | Renamer monad: two stacked 'Writer's, one for errors (inner) and
-- one for warnings (outer). Concrete type so callers don't need 'mtl'
-- classes; 'emitError' lifts past the warning layer.
type Rename = WriterT [Diagnostic RenameWarning] (Writer [Diagnostic RenameError])

emitError :: AnnP RenameError -> Rename ()
emitError e = lift (tell [noDiag e])

emitWarning :: AnnP RenameWarning -> Rename ()
emitWarning w = tell [noDiag w]

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
    dataConProviders :: DataConProviders,
    -- | All declared @(constructorName, arity)@ providers across the
    -- program, /unfiltered/ by visibility. Used to disambiguate
    -- diagnostics for qualified references: if a missing
    -- @'Qualified' m n@ matches an entry whose providers include @m@,
    -- the user named a real-but-hidden constructor and gets
    -- 'NonExportedConstructor'; otherwise they get 'NotExportedByModule'
    -- as before.
    allDataConProviders :: DataConProviders,
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
    operatorExports :: Map Text [OpDecl],
    -- | Map from module name to the source location where its header
    -- parsing stopped. Used to detect @use_module@ directives that
    -- appear after non-import content.
    trailingLoc :: Map Text (Maybe SourceLoc)
  }

-- | An empty 'RenameInputs' suitable for callers that do not have header
-- information (e.g. test fixtures, query renaming).
defaultRenameInputs :: RenameInputs
defaultRenameInputs =
  RenameInputs
    { operatorExports = Map.empty,
      trailingLoc = Map.empty
    }

-- ---------------------------------------------------------------------------
-- Environment building
-- ---------------------------------------------------------------------------

-- | Build a map of data-constructor names to their declared arities,
-- restricted to constructors visible to the current module (per the
-- supplied 'visibleDataCons' map). Constructors come from type
-- declarations and are always 'Unqualified' at this point (the parser
-- never produces qualified constructor names).
buildDataConEnv :: Map DeclaredType (Set.Set Text) -> [Module] -> DataConEnv
buildDataConEnv visible mods =
  Map.fromListWith
    (++)
    [ (t, [length dc.conArgs])
    | m <- mods,
      Ann td _ <- m.typeDecls,
      let key =
            DeclaredType m.name (unqualifiedText td.name) (length td.typeVars),
      Just visibleCons <- [Map.lookup key visible],
      dc <- td.constructors,
      Unqualified t <- [dc.conName],
      t `Set.member` visibleCons
    ]

-- | Build the @(constructorName, arity) -> [declaringModule]@ index used
-- by the renamer's data-constructor canonicalization. Same scope as
-- 'buildDataConEnv': only constructors whose declaring type is visible
-- to the current module, and only constructors permitted by the
-- visibility map's value-side allowlist.
buildDataConProviders ::
  Map DeclaredType (Set.Set Text) -> [Module] -> DataConProviders
buildDataConProviders visible mods =
  Map.fromListWith
    (++)
    [ ((t, length dc.conArgs), [m.name])
    | m <- mods,
      Ann td _ <- m.typeDecls,
      let key =
            DeclaredType m.name (unqualifiedText td.name) (length td.typeVars),
      Just visibleCons <- [Map.lookup key visible],
      dc <- td.constructors,
      Unqualified t <- [dc.conName],
      t `Set.member` visibleCons
    ]

-- | Like 'buildDataConProviders' but ignores the visibility map. The
-- result lists every declared @(constructorName, arity)@ alongside the
-- modules that declare it, regardless of export allowlists or import
-- lists. Used to distinguish "declared but hidden" from "not declared
-- at all" when emitting diagnostics for qualified references.
buildAllDataConProviders :: [Module] -> DataConProviders
buildAllDataConProviders mods =
  Map.fromListWith
    (++)
    [ ((t, length dc.conArgs), [m.name])
    | m <- mods,
      Ann td _ <- m.typeDecls,
      dc <- td.constructors,
      Unqualified t <- [dc.conName]
    ]

-- | Canonicalize a use-site data-constructor reference to its declared
-- 'Qualified' form when exactly one declaration matches @(name, arity)@.
-- Returns 'Nothing' for unknown or ambiguous names — callers fall back to
-- their existing handling (typically: leave the name 'Unqualified' and
-- emit an undeclared-data-constructor warning).
canonicalizeDataCon :: RenameCtx -> Text -> Int -> Maybe Name
canonicalizeDataCon ctx n arity = case Map.lookup (n, arity) ctx.dataConProviders of
  Just [m] -> Just (Qualified m n)
  _ -> Nothing

-- | Variant that takes a 'Name' (so compound-functor sites can call it
-- without unwrapping). 'Qualified' names pass through unchanged;
-- 'Unqualified' names are canonicalized via 'canonicalizeDataCon'.
canonicalizeData :: RenameCtx -> Name -> Int -> Name
canonicalizeData _ name@(Qualified _ _) _ = name
canonicalizeData ctx (Unqualified n) arity =
  case canonicalizeDataCon ctx n arity of
    Just qn -> qn
    Nothing -> Unqualified n

-- | Emit 'AmbiguousDataConstructor' (YCHR-20012) when the data-constructor
-- providers map lists more than one module for @(n, arity)@. Mirrors
-- the multi-provider arm of 'resolveName' (YCHR-20001) but for the
-- constructor namespace. Callers invoke this at every non-opaque use
-- site that would otherwise silently fall through 'canonicalizeData'
-- (which collapses both unknown and ambiguous into a no-op rewrite).
checkAmbiguousDataCon ::
  RenameCtx -> SourceLoc -> PExpr -> Text -> Int -> Rename ()
checkAmbiguousDataCon ctx loc origin n arity =
  case Map.lookup (n, arity) ctx.dataConProviders of
    Just ms@(_ : _ : _) ->
      emitError (AnnP (AmbiguousDataConstructor n ms) loc origin)
    _ -> pure ()

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
        Nothing ->
          [ TypeExportDecl (unqualifiedText td.name) (length td.typeVars) Nothing
          | Ann td _ <-
              m.typeDecls
          ]
        Just annExports -> filter isTypeExportDecl annExports.node
    ]

isConstraintOrFunctionDecl :: Declaration -> Bool
isConstraintOrFunctionDecl ConstraintDecl {} = True
isConstraintOrFunctionDecl FunctionDecl {} = True
isConstraintOrFunctionDecl _ = False

isTypeExportDecl :: Declaration -> Bool
isTypeExportDecl TypeExportDecl {} = True
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

-- | Rename a multi-module program: qualify every constraint, function,
-- type, and data-constructor reference against the appropriate provider
-- module, and validate export and import lists. Caller-supplied
-- 'RenameInputs' carries per-module operator-export tables and trailing
-- header locations gathered by 'YCHR.Collect'; pass 'defaultRenameInputs'
-- when those tables are unavailable (tests, query renaming).
-- Returns the renamed modules and any warnings on success, or the
-- accumulated diagnostics on failure.
renameProgram ::
  RenameInputs ->
  [Module] ->
  Either
    [Diagnostic RenameError]
    ( [Module],
      [Diagnostic RenameWarning]
    )
renameProgram inputs mods =
  let declEnv0 = buildDeclEnv mods
      exportEnv0 = buildExportEnv mods
      typeDeclEnv0 = buildTypeDeclEnv mods
      typeExportEnv0 = buildTypeExportEnv mods
      allCons = buildAllDataConProviders mods
      ctxFor m =
        let ctx0 =
              RenameCtx
                { declEnv = declEnv0,
                  exportEnv = exportEnv0,
                  dataConEnv = Map.empty,
                  dataConProviders = Map.empty,
                  allDataConProviders = allCons,
                  typeDeclEnv = typeDeclEnv0,
                  typeExportEnv = typeExportEnv0,
                  operatorExports = inputs.operatorExports,
                  currentTrailingLoc =
                    Map.findWithDefault Nothing m.name inputs.trailingLoc,
                  currentModule = m
                }
            visible = visibleDataCons mods ctx0
         in ctx0
              { dataConEnv = buildDataConEnv visible mods,
                dataConProviders = buildDataConProviders visible mods
              }
      ( (result, warnings),
        errs
        ) =
          runWriter
            ( runWriterT $ do
                validateExports mods
                traverse (\m -> renameModule mods (ctxFor m)) mods
            )
   in if null errs then Right (result, warnings) else Left errs

-- | Check that every name in a module's export list is actually declared.
validateExports :: [Module] -> Rename ()
validateExports = traverse_ validateOne
  where
    validateOne m = case m.exports of
      Nothing -> pure ()
      Just (AnnP exports loc origin) -> traverse_ (checkExport m loc origin) exports

    checkExport m loc origin d = case d of
      ConstraintDecl {name, arity}
        | not (isDeclared m name arity) ->
            emitError (AnnP (UnknownExport m.name name arity) loc origin)
      FunctionDecl {name, arity}
        | not (isDeclared m name arity) ->
            emitError (AnnP (UnknownExport m.name name arity) loc origin)
      TypeExportDecl {name, arity, conExports}
        | not (isTypeDeclared m name arity) ->
            emitError (AnnP (UnknownExport m.name name arity) loc origin)
        | otherwise ->
            checkConList m loc origin name arity conExports
      _ -> pure ()

    checkConList _ _ _ _ _ Nothing = pure ()
    checkConList m loc origin tyName tyArity (Just cs) =
      let declared = declaredConstructors m tyName tyArity
       in traverse_
            ( \c ->
                when (c `notElem` declared) $
                  emitError
                    ( AnnP
                        (UnknownExportedConstructor m.name tyName tyArity c)
                        loc
                        origin
                    )
            )
            cs

    isDeclared m n a = (n, a) `elem` [(d.name, d.arity) | Ann d _ <- m.decls]
    isTypeDeclared m n a =
      (n, a)
        `elem` [ ( unqualifiedText td.name,
                   length td.typeVars
                 )
               | Ann td _ <- m.typeDecls
               ]

    declaredConstructors m n a =
      [ unqualifiedText dc.conName
      | Ann td _ <- m.typeDecls,
        unqualifiedText td.name == n,
        length td.typeVars == a,
        dc <- td.constructors
      ]

-- ---------------------------------------------------------------------------
-- Module, rule, equation, head renaming
-- ---------------------------------------------------------------------------

renameModule :: [Module] -> RenameCtx -> Rename Module
renameModule mods ctx = do
  let m = ctx.currentModule
  validateImportLists mods ctx
  renamedRules <- traverse (renameRule ctx) m.rules
  renamedEquations <- traverse (traverse (renameEquation ctx)) m.equations
  renamedExtensions <- traverse (traverse (renameEquation ctx)) m.extensions
  renamedClassExtensions <- traverse (traverse (renameEquation ctx)) m.classExtensions
  let renamedTypeDecls = map (fmap (renameTypeDefinition ctx)) m.typeDecls
  renamedDecls <- traverse (renameAnnDecl ctx) m.decls
  renamedExtensionTypes <- traverse (renameAnnDecl ctx) m.extensionTypes
  pure
    m
      { rules = renamedRules,
        equations = renamedEquations,
        extensions = renamedExtensions,
        classExtensions = renamedClassExtensions,
        typeDecls = renamedTypeDecls,
        decls = renamedDecls,
        extensionTypes = renamedExtensionTypes
      }

-- | Validate import lists. Four checks:
--
--   * @op(...)@ entries must name an operator that the source module
--     actually exports ('UnknownOperatorImport').
--   * Constraint, function, and type imports must name something the
--     source module exports ('UnknownImport').
--   * A @type(t/n, [c, ...])@ import must list constructors that the
--     source module exports for that type ('UnknownExportedConstructor').
--   * Each @use_module@ directive must appear before the first non-import
--     directive in the file ('UseModuleOutOfOrder').
validateImportLists :: [Module] -> RenameCtx -> Rename ()
validateImportLists mods ctx =
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
    checkItem mn loc origin (ConstraintDecl n a _ _) =
      when (mn `notElem` lookupExport (n, a) ctx.exportEnv) $
        emitError (AnnP (UnknownImport mn n a) loc origin)
    checkItem mn loc origin (FunctionDecl n a _ _ _ _ _) =
      when (mn `notElem` lookupExport (n, a) ctx.exportEnv) $
        emitError (AnnP (UnknownImport mn n a) loc origin)
    checkItem _ _ _ ExtendClassTypeDecl {} = pure ()
    checkItem mn loc origin (TypeExportDecl n a cs) =
      if mn `notElem` lookupExport (n, a) ctx.typeExportEnv
        then emitError (AnnP (UnknownImport mn n a) loc origin)
        else checkImportedCons mn loc origin n a cs

    checkImportedCons _ _ _ _ _ Nothing = pure ()
    checkImportedCons mn loc origin n a (Just xs) =
      let declared = declaredConstructorsOn mn n a
          exported = filterByExporterAllowlist mn n a declared
       in traverse_
            ( \c ->
                if c `notElem` declared
                  then
                    emitError
                      (AnnP (UnknownExportedConstructor mn n a c) loc origin)
                  else
                    when (c `notElem` exported) $
                      emitError
                        (AnnP (ConstructorNotExported mn n a c) loc origin)
            )
            xs

    -- All constructors of type @n/a@ declared in module @mn@, ignoring
    -- the module's export allowlist.
    declaredConstructorsOn mn n a =
      case [m | m <- mods, m.name == mn] of
        (m : _) ->
          [ unqualifiedText dc.conName
          | Ann td _ <- m.typeDecls,
            unqualifiedText td.name == n,
            length td.typeVars == a,
            dc <- td.constructors
          ]
        [] -> []

    -- Intersect the supplied 'declared' list with @mn@'s optional
    -- @type(...)@ allowlist (or pass through unchanged if @mn@ has no
    -- export list, in which case everything declared is exported).
    filterByExporterAllowlist mn n a declared =
      case [m | m <- mods, m.name == mn] of
        (m : _) ->
          let allowed = case m.exports of
                Nothing -> Nothing
                Just (AnnP exports _ _) ->
                  case [acs | TypeExportDecl tn ta acs <- exports, tn == n, ta == a] of
                    (acs : _) -> acs
                    [] -> Just []
           in case allowed of
                Nothing -> declared
                Just xs -> filter (`elem` xs) declared
        [] -> []

-- | True when @a@ is at or after @b@ in source order. Both locations
-- must come from the same file (caller's responsibility).
locAtOrAfter :: SourceLoc -> SourceLoc -> Bool
locAtOrAfter a b = (a.line, a.col) >= (b.line, b.col)

renameRule :: RenameCtx -> Rule -> Rename Rule
renameRule ctx r = do
  h <- traverse (renameHead ctx r.head.sourceLoc r.head.parsed) r.head
  g <-
    traverse
      (traverse (renameTerm ctx r.guard.sourceLoc r.guard.parsed ResolveAll))
      r.guard
  b <-
    traverse
      (traverse (renameTerm ctx r.body.sourceLoc r.body.parsed ResolveTop))
      r.body
  pure r {head = h, guard = g, body = b}

renameEquation :: RenameCtx -> FunctionEquation -> Rename FunctionEquation
renameEquation ctx eq = do
  -- Equation args don't carry their own SourceLoc; use the guard's as a proxy.
  let loc = eq.guard.sourceLoc
      origin = eq.guard.parsed
  resolvedFunName <- resolveName ResolveTop ctx loc origin eq.funName (length eq.args)
  renamedArgs <- traverse (renameTerm ctx loc origin NoResolve) eq.args
  renamedGuard <- traverse (traverse (renameTerm ctx loc origin ResolveAll)) eq.guard
  renamedRhs <-
    traverse
      (traverse (renameTerm ctx eq.rhs.sourceLoc eq.rhs.parsed ResolveAll))
      eq.rhs
  pure
    eq
      { funName = resolvedFunName,
        args = renamedArgs,
        guard = renamedGuard,
        rhs = renamedRhs
      }

renameHead :: RenameCtx -> SourceLoc -> PExpr -> Head -> Rename Head
renameHead ctx loc origin h = case h of
  Simplification cs -> Simplification <$> traverse (renameCon ctx loc origin) cs
  Propagation cs -> Propagation <$> traverse (renameCon ctx loc origin) cs
  Simpagation k r ->
    Simpagation
      <$> traverse (renameCon ctx loc origin) k
      <*> traverse (renameCon ctx loc origin) r

renameCon :: RenameCtx -> SourceLoc -> PExpr -> Constraint -> Rename Constraint
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
--
-- * 'NoResolveQuoted' — inside a @term(...)@ body. Same name policy as
--   'NoResolve' (functors stay unqualified, declared data constructors
--   still get canonicalized to @Mod:name@), but the undeclared-
--   constructor warning is suppressed because the body is intentionally
--   opaque (see the language reference §The @term/1@ quoting form).
data ResolveMode
  = NoResolve
  | NoResolveQuoted
  | ResolveTop
  | ResolveAll
  deriving (Eq)

-- | Whether 'resolveName' should error on unresolved names. Derived from
-- 'ResolveMode': 'ResolveTop' requires declarations, 'ResolveAll' tolerates
-- missing ones, and 'NoResolve' never calls 'resolveName'.
errorOnUnknown :: ResolveMode -> Bool
errorOnUnknown ResolveTop = True
errorOnUnknown _ = False

-- | Whether the current position evaluates expressions (so the syntactic
-- special cases for @is@, lambdas, and @fun name/arity@ apply). Returns
-- 'False' for both pattern positions ('NoResolve') and quoted bodies
-- ('NoResolveQuoted'), where these forms must remain literal compound
-- terms instead of being interpreted.
isResolving :: ResolveMode -> Bool
isResolving ResolveTop = True
isResolving ResolveAll = True
isResolving _ = False

-- | Rename a lambda body, walking through any top-level comma sequencer
-- without treating @,@ itself as a data constructor. Each comma-separated
-- item is renamed in 'ResolveAll' mode like an ordinary lambda body.
renameLambdaBody :: RenameCtx -> SourceLoc -> PExpr -> Term -> Rename Term
renameLambdaBody ctx loc origin t = case t of
  CompoundTerm (Unqualified ",") [l, r] -> do
    l' <- renameLambdaBody ctx loc origin l
    r' <- renameLambdaBody ctx loc origin r
    pure (CompoundTerm (Unqualified ",") [l', r'])
  _ -> renameTerm ctx loc origin ResolveAll t

renameTerm :: RenameCtx -> SourceLoc -> PExpr -> ResolveMode -> Term -> Rename Term
renameTerm ctx loc origin mode t = case t of
  -- Special case: @is@ LHS is a pattern (no resolution), RHS is an expression.
  CompoundTerm (Unqualified "is") [lhs, rhs] | isResolving mode -> do
    renamedLhs <- renameTerm ctx loc origin NoResolve lhs
    renamedRhs <- renameTerm ctx loc origin ResolveAll rhs
    pure (CompoundTerm (Unqualified "is") [renamedLhs, renamedRhs])
  -- Special case: @=@ is symmetric unification; both operands are
  -- evaluated expressions (PROJECT.md). Without this, the parent
  -- 'ResolveTop' would demote the operands to 'NoResolve', the lambda
  -- arm's 'isResolving' guard would fail, and 'fun'/'->' would leak
  -- out as spurious YCHR-20101 warnings.
  CompoundTerm (Unqualified "=") [lhs, rhs] | isResolving mode -> do
    renamedLhs <- renameTerm ctx loc origin ResolveAll lhs
    renamedRhs <- renameTerm ctx loc origin ResolveAll rhs
    pure (CompoundTerm (Unqualified "=") [renamedLhs, renamedRhs])
  -- Lambda: @fun(params) -> body@. Params are variable patterns (don't resolve),
  -- the body is always an expression. The body may use comma sequencing
  -- (@A, B, C@) at its top level; walk through any such top-level commas
  -- without treating them as a data constructor, mirroring the parser's
  -- comma flattening for top-level function-equation RHS.
  CompoundTerm
    (Unqualified "->")
    [ CompoundTerm (Unqualified "fun") params,
      body
      ] | isResolving mode -> do
      renamedBody <- renameLambdaBody ctx loc origin body
      pure
        ( CompoundTerm
            (Unqualified "->")
            [ CompoundTerm (Unqualified "fun") params,
              renamedBody
            ]
        )
  -- Quoting: @term(X)@ keeps its argument opaque. Functor names inside
  -- stay unqualified, declared data constructors are silently
  -- canonicalized, and undeclared-data-constructor warnings are
  -- suppressed because the body is intentionally not subject to those
  -- checks (see docs/reference/language.md §The @term/1@ quoting form).
  -- Fires in any surrounding mode so a nested @term(...)@ behind a
  -- 'NoResolve' parent (e.g. a body-position constraint argument) is
  -- also covered.
  CompoundTerm (Unqualified "term") [arg] -> do
    renamedArg <- renameTerm ctx loc origin NoResolveQuoted arg
    pure (CompoundTerm (Unqualified "term") [renamedArg])
  -- Function reference: @fun name/arity@. Resolve the function name,
  -- then strip the @fun@ wrapper so downstream passes see bare @name/arity@.
  CompoundTerm
    (Unqualified "fun")
    [ CompoundTerm
        (Unqualified "/")
        [ AtomTerm fname,
          IntTerm farity
          ]
      ] | isResolving mode -> do
      resolved <-
        resolveName ResolveTop ctx loc origin (Unqualified fname) (fromInteger farity)
      pure
        ( CompoundTerm
            (Unqualified "/")
            [AtomTerm (flattenName resolved), IntTerm farity]
        )
  CompoundTerm name args -> do
    let childMode = case mode of
          NoResolve -> NoResolve
          NoResolveQuoted -> NoResolveQuoted
          ResolveTop -> NoResolve
          ResolveAll -> ResolveAll
    renamedArgs <- traverse (renameTerm ctx loc origin childMode) args
    newName <- case mode of
      NoResolve -> do
        case name of
          -- Skip the unknown-data-constructor warning when the bare
          -- name matches a visible function or constraint declaration:
          -- 'Resolve.termToExpr' will later canonicalize it to a
          -- 'CallExpr' for tell-side argument evaluation, so it is not
          -- a misspelled data constructor. The data-constructor
          -- ambiguity check is gated by the same condition: if the
          -- name resolves unambiguously in the function/constraint
          -- namespace, that resolution wins and any data-constructor
          -- ambiguity in the same name is moot for this use.
          Unqualified n
            | null (visibleProviders ctx n (length args)) -> do
                warnUnknownDataCon ctx.dataConEnv loc origin n (length args)
                checkAmbiguousDataCon ctx loc origin n (length args)
            | otherwise -> pure ()
          -- Qualified references in pattern position (head args,
          -- body-tell args) get the same visibility check as in
          -- resolving positions; the parser can't tell a constructor,
          -- a function/constraint, or a type-tag apart at the term
          -- level, so any of those visibility leg passes.
          Qualified m n -> validateQualified ctx loc origin m n (length args)
        pure (canonicalizeData ctx name (length args))
      NoResolveQuoted ->
        -- Inside a 'term/1' quote the body is fully opaque: no
        -- visibility checks fire and qualified atoms are kept
        -- as-written. This is the supported escape hatch for
        -- constructing arbitrary qualified atoms as data (e.g. type
        -- tags inside the typechecker's CHR program).
        pure (canonicalizeData ctx name (length args))
      _ -> do
        resolved <- resolveName mode ctx loc origin name (length args)
        case resolved of
          Unqualified n -> do
            -- Gate on 'null visibleProviders' so we don't pile a
            -- YCHR-20012 on top of the YCHR-20001 that 'resolveName'
            -- has already emitted when both namespaces are ambiguous.
            when (null (visibleProviders ctx n (length args))) $
              checkAmbiguousDataCon ctx loc origin n (length args)
            pure (canonicalizeData ctx resolved (length args))
          Qualified _ _ -> pure resolved
    pure (CompoundTerm newName renamedArgs)
  -- Zero-arity atom promotion: if a bare atom matches a declared
  -- constraint, function, or data constructor with arity 0, promote
  -- it to a qualified 'CompoundTerm'. Data-constructor canonicalization
  -- applies in @NoResolve@ mode too (head patterns) so that bare and
  -- qualified uses end up at the same runtime atom.
  AtomTerm n -> do
    resolved <- case mode of
      NoResolve -> do
        warnUnknownDataCon ctx.dataConEnv loc origin n 0
        pure (Unqualified n)
      NoResolveQuoted ->
        pure (Unqualified n)
      _ -> resolveName ResolveAll ctx loc origin (Unqualified n) 0
    case resolved of
      Qualified _ _ -> pure (CompoundTerm resolved [])
      Unqualified _ -> do
        -- Skip the ambiguity check in the @term/1@ opaque-quote
        -- mode, and skip it when the function/constraint namespace
        -- already has something to say about the name (either it
        -- resolves there, or 'resolveName' has already emitted
        -- YCHR-20001 for an ambiguity there).
        case mode of
          NoResolveQuoted -> pure ()
          _ ->
            when (null (visibleProviders ctx n 0)) $
              checkAmbiguousDataCon ctx loc origin n 0
        case canonicalizeDataCon ctx n 0 of
          Just qn -> pure (CompoundTerm qn [])
          Nothing -> pure (AtomTerm n)
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
resolveName ::
  ResolveMode ->
  RenameCtx ->
  SourceLoc ->
  PExpr ->
  Name ->
  Int ->
  Rename Name
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
resolveName _ ctx loc origin name@(Qualified m n) arity = do
  validateQualified ctx loc origin m n arity
  pure name

-- | Verify that a qualified reference @M:n/a@ is in scope as a
-- /value-level/ identifier: function, constraint, or data
-- constructor. Types are intentionally not accepted — they live in a
-- separate namespace and cannot appear in value positions. Users who
-- need a qualified atom as opaque data (e.g. the typechecker's
-- type-name tags) must wrap it with @term/1@, which switches the
-- renamer into 'NoResolveQuoted' mode and skips this check entirely.
-- The @host@ pseudo-module is exempt (host calls are external).
--
-- For a miss, the diagnostic is constructor-flavored
-- ('NonExportedConstructor', YCHR-20010) iff @M@ declares
-- @(n, arity)@ as a constructor anywhere — i.e. the user named a
-- real but hidden ctor. Otherwise we emit the existing generic
-- 'NotExportedByModule' (YCHR-20009). Callers return the
-- 'Qualified' name unchanged so traversal can continue.
validateQualified ::
  RenameCtx -> SourceLoc -> PExpr -> Text -> Text -> Int -> Rename ()
validateQualified ctx loc origin m n arity
  | m == "host" = pure ()
  | m `elem` visibleProviders ctx n arity = pure ()
  | m `elem` Map.findWithDefault [] (n, arity) ctx.dataConProviders = pure ()
  | m `elem` Map.findWithDefault [] (n, arity) ctx.allDataConProviders =
      emitError (AnnP (NonExportedConstructor m n arity) loc origin)
  | otherwise =
      emitError (AnnP (NotExportedByModule m n arity) loc origin)

-- | All modules that can provide @(name, arity)@ to the current module:
-- the current module itself if it declares the name, plus every imported
-- module that /exports/ it.
visibleProviders :: RenameCtx -> Text -> Int -> [Text]
visibleProviders ctx n arity =
  let ownProviders =
        filter
          (== ctx.currentModule.name)
          (lookupDecl (n, arity) ctx.declEnv)
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
    match (ConstraintDecl dn da _ _) = dn == n && da == arity
    match (FunctionDecl dn da _ _ _ _ _) = dn == n && da == arity
    match _ = False

-- | Check whether a type name/arity is permitted by an import list.
importListPermitsType :: Text -> Int -> Maybe [Declaration] -> Bool
importListPermitsType _ _ Nothing = True
importListPermitsType n arity (Just decls) = any match decls
  where
    match (TypeExportDecl tn ta _) = tn == n && ta == arity
    match _ = False

-- | The set of constructor names a single import-list entry permits for
-- type @n/a@. The fallback is the supplied @allCons@ — used when no
-- constructor clause is present (i.e. the import is @type(n/a)@ rather
-- than @type(n/a, [...])@).
importListPermitsCons ::
  Text -> Int -> Set.Set Text -> Maybe [Declaration] -> Set.Set Text
importListPermitsCons _ _ allCons Nothing = allCons
importListPermitsCons n arity allCons (Just decls) =
  case [cs | TypeExportDecl tn ta cs <- decls, tn == n, ta == arity] of
    (Nothing : _) -> allCons
    (Just xs : _) -> Set.fromList xs
    [] -> Set.empty

-- | For each type visible to the current module, the set of constructor
-- names also visible. Locally declared types contribute every declared
-- constructor; imported types contribute @exporterAllowlist ∩
-- importerAllowlist@ where each side defaults to "all constructors" when
-- its @type(...)@ clause has no constructor list. A type with an empty
-- constructor set still appears in the map: the type itself remains
-- visible (type-level visibility is governed independently by
-- 'resolveTypeName'), only its constructors are hidden.
visibleDataCons :: [Module] -> RenameCtx -> Map DeclaredType (Set.Set Text)
visibleDataCons mods ctx =
  Map.fromList
    [ entry
    | m <- mods,
      Ann td _ <- m.typeDecls,
      Just entry <- [entryFor m td]
    ]
  where
    imports =
      [(mn, il) | AnnP (ModuleImport mn il) _ _ <- ctx.currentModule.imports]

    entryFor m td =
      let n = unqualifiedText td.name
          a = length td.typeVars
          key = DeclaredType m.name n a
          allCons =
            Set.fromList [unqualifiedText dc.conName | dc <- td.constructors]
       in if m.name == ctx.currentModule.name
            then Just (key, allCons)
            else case ( exporterAllowance m n a allCons,
                        importerAllowance m.name n a allCons
                      ) of
              (Just expSet, Just impSet) ->
                Just (key, Set.intersection expSet impSet)
              _ -> Nothing

    exporterAllowance m n a allCons = case m.exports of
      Nothing -> Just allCons
      Just (AnnP exports _ _) ->
        case [cs | TypeExportDecl tn ta cs <- exports, tn == n, ta == a] of
          (Nothing : _) -> Just allCons
          (Just xs : _) -> Just (Set.fromList xs)
          [] -> Nothing

    importerAllowance mn n a allCons =
      let relevant = [il | (imn, il) <- imports, imn == mn]
       in if null relevant
            then Nothing
            else
              Just
                ( Set.unions
                    [importListPermitsCons n a allCons il | il <- relevant]
                )

-- | Check an unresolved name against data-constructor declarations.
-- If found with matching arity: silent. If found with wrong arity: warning.
-- If not found at all: warning.
warnUnknownDataCon :: DataConEnv -> SourceLoc -> PExpr -> Text -> Int -> Rename ()
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
-- need to move into 'Rename'.
renameTypeDefinition :: RenameCtx -> TypeDefinition -> TypeDefinition
renameTypeDefinition ctx td =
  TypeDefinition
    { name = Qualified ctx.currentModule.name (unqualifiedText td.name),
      typeVars = td.typeVars,
      constructors = map (renameDataConstructor ctx) td.constructors,
      loc = td.loc
    }

renameDataConstructor :: RenameCtx -> DataConstructor -> DataConstructor
renameDataConstructor ctx dc =
  DataConstructor
    { conName = Qualified ctx.currentModule.name (unqualifiedText dc.conName),
      conArgs = map (renameTypeExpr ctx) dc.conArgs
    }

renameAnnDecl :: RenameCtx -> Ann Declaration -> Rename (Ann Declaration)
renameAnnDecl ctx (Ann d loc) = do
  d' <- renameDeclaration ctx loc d
  pure (Ann d' loc)

renameDeclaration ::
  RenameCtx -> SourceLoc -> Declaration -> Rename Declaration
renameDeclaration ctx loc (ConstraintDecl n a argTypes requiring) = do
  requiring' <- traverse (traverse (renameBoundSig ctx loc)) requiring
  pure
    ConstraintDecl
      { name = n,
        arity = a,
        argTypes = fmap (map (renameTypeExpr ctx)) argTypes,
        requiring = requiring'
      }
renameDeclaration
  ctx
  loc
  (FunctionDecl n a argTypes returnType isOpen kind requiring) = do
    requiring' <- traverse (traverse (renameBoundSig ctx loc)) requiring
    pure
      FunctionDecl
        { name = n,
          arity = a,
          argTypes = fmap (map (renameTypeExpr ctx)) argTypes,
          returnType = fmap (renameTypeExpr ctx) returnType,
          isOpen = isOpen,
          kind = kind,
          requiring = requiring'
        }
renameDeclaration ctx loc d@ExtendClassTypeDecl {name, arity, argTypes, returnType} = do
  resolved <- resolveName ResolveTop ctx loc (Atom name) (Unqualified name) arity
  pure
    d
      { argTypes = fmap (map (renameTypeExpr ctx)) argTypes,
        returnType = fmap (renameTypeExpr ctx) returnType,
        target = Just resolved
      }
renameDeclaration _ _ d = pure d

-- | Rename a 'BoundSig' inside a @requiring@ clause: resolve the bound
-- function's name to a 'Qualified' form (so the resolver can look it up
-- by qualified name) and rename type-expression references in the
-- argument and return types. Unresolvable bound names are deferred to
-- the resolver, which emits the dedicated 'unknown_bound_function'
-- diagnostic (YCHR-16009) with the requiring-clause context. We do not
-- reuse 'resolveName' here because 'ResolveTop' would emit the generic
-- 'UnknownName' (YCHR-20002) on a miss and 'ResolveAll' would trigger
-- spurious 'warnUnknownDataCon' warnings — a bound reference never
-- names a data constructor.
renameBoundSig :: RenameCtx -> SourceLoc -> BoundSig -> Rename BoundSig
renameBoundSig ctx _ bs = do
  resolved <- resolveBoundName
  pure
    BoundSig
      { name = resolved,
        arity = bs.arity,
        argTypes = map (renameTypeExpr ctx) bs.argTypes,
        returnType = renameTypeExpr ctx bs.returnType,
        loc = bs.loc
      }
  where
    boundSigName b = case b.name of
      Unqualified t -> t
      Qualified _ t -> t
    origin = Atom (boundSigName bs)
    resolveBoundName = case bs.name of
      Qualified m n -> do
        validateQualified ctx bs.loc origin m n bs.arity
        pure (Qualified m n)
      Unqualified n
        | isReserved n -> pure (Unqualified n)
        | otherwise ->
            case visibleProviders ctx n bs.arity of
              [m] -> pure (Qualified m n)
              [] -> pure (Unqualified n)
              ms -> do
                emitError (AnnP (AmbiguousName n bs.arity ms) bs.loc origin)
                pure (Unqualified n)

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
  let ownProviders =
        filter
          (== ctx.currentModule.name)
          (lookupDecl (n, arity) ctx.typeDeclEnv)
      imports = [(mn, il) | AnnP (ModuleImport mn il) _ _ <- ctx.currentModule.imports]
      importProviders =
        filter
          ( \mn ->
              any
                (\(imn, il) -> imn == mn && importListPermitsType n arity il)
                imports
          )
          (lookupExport (n, arity) ctx.typeExportEnv)
      matches = ownProviders ++ importProviders
   in case matches of
        [m] -> Qualified m n
        _ -> Unqualified n

-- ---------------------------------------------------------------------------
-- Query renaming
-- ---------------------------------------------------------------------------

-- | Like 'renameQueryGoals' but uses 'NoResolve' mode — appropriate
-- for the argument terms of a single goal constraint, where each
-- term is data (constructors / atoms / variables) rather than a
-- callable. Canonicalizes bare data-constructor references the same
-- way the renamer does for head-pattern arguments.
renameQueryArgs ::
  [Module] ->
  [Term] ->
  Either
    [Diagnostic RenameError]
    ( [Term],
      [Diagnostic RenameWarning]
    )
renameQueryArgs mods args = renameQueryTerms mods NoResolve args

-- | Rename a list of query goal terms using all modules as the visible
-- scope. Each term is renamed at 'ResolveTop' level (same as rule bodies).
-- Returns 'Left' if any rename errors occur.
renameQueryGoals ::
  [Module] ->
  [Term] ->
  Either
    [Diagnostic RenameError]
    ( [Term],
      [Diagnostic RenameWarning]
    )
renameQueryGoals mods goals = renameQueryTerms mods ResolveTop goals

renameQueryTerms ::
  [Module] ->
  ResolveMode ->
  [Term] ->
  Either [Diagnostic RenameError] ([Term], [Diagnostic RenameWarning])
renameQueryTerms mods mode terms =
  let queryMod =
        Module
          { name = "<query>",
            nameLoc = dummyLoc,
            imports = [noAnnP (ModuleImport m.name Nothing) | m <- mods],
            decls = [],
            extensionTypes = [],
            typeDecls = [],
            rules = [],
            equations = [],
            extensions = [],
            classExtensions = [],
            exports = Nothing
          }
      ctx0 =
        RenameCtx
          { declEnv = buildDeclEnv mods,
            exportEnv = buildExportEnv mods,
            dataConEnv = Map.empty,
            dataConProviders = Map.empty,
            allDataConProviders = buildAllDataConProviders mods,
            typeDeclEnv = buildTypeDeclEnv mods,
            typeExportEnv = buildTypeExportEnv mods,
            operatorExports = Map.empty,
            currentTrailingLoc = Nothing,
            currentModule = queryMod
          }
      visible = visibleDataCons mods ctx0
      ctx =
        ctx0
          { dataConEnv = buildDataConEnv visible mods,
            dataConProviders = buildDataConProviders visible mods
          }
      ((renamed, warnings), errs) =
        runWriter
          ( runWriterT $
              traverse (renameTerm ctx dummyLoc (Atom "") mode) terms
          )
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
these helpers will need to move into 'Rename'.
--------------------------------------------------------------------------- -}
