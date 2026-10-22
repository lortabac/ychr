{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

-- |
-- Module      : YCHR.Internal.Rename
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
-- 6. /Special cases in 'renameTerm'/: @is@, disjunction (@;@), lambdas
--    (@fun(...) -> ...@), function references (@name\/arity@),
--    @quote\/1@, and zero-arity atom promotion each have their own
--    branch.
--
-- 7. /Data-constructor warnings/: unresolved names in expression contexts
--    emit a warning unless they match a declared data constructor.
--
-- 8. /Type-definition renaming/: type names and constructor names inside
--    'TypeDefinition' values are qualified with their declaring module.
--
-- This pass guarantees that the subsequent Desugaring phase can treat the
-- program as a flat, unambiguous collection of rules.
module YCHR.Internal.Rename
  ( -- * Entry points
    renameProgram,
    QueryRenameEnv,
    buildQueryRenameEnv,
    renameQueryGoalsWith,
    renameQueryArgsWith,
    expandQueryGoalWith,
    buildExportEnv,

    -- * Errors and warnings
    RenameError (..),
    HeadPart (..),
    RenameWarning (..),

    -- * Configuration
    RenameInputs (..),
    defaultRenameInputs,
  )
where

import Control.Monad (foldM, foldM_, unless, when)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.State.Strict (StateT, evalStateT, get, modify', put)
import Control.Monad.Trans.Writer.CPS (Writer, WriterT, runWriter, runWriterT, tell)
import Data.Foldable (traverse_)
import Data.List (nub)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe (fromMaybe)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as Text
import YCHR.Internal.Collected (CollectedImport (..), CollectedModule (..))
import YCHR.Internal.Diagnostic (Diagnostic (..), noDiag)
import YCHR.Internal.PExpr (PExpr (Atom, Compound))
import YCHR.Internal.PExpr qualified as PExpr
import YCHR.Internal.Parsed
import YCHR.Internal.Pretty (termToPExpr)
import YCHR.Internal.Rename.Macro
  ( HeadConjunctResult (..),
    PrimitiveError (..),
    PrimitiveOperand,
    flattenConj,
    goalsToChain,
    headConjunct,
    importListPermitsMacro,
    instantiateClause,
    isPrimitiveName,
    isVariant,
    macroDepthLimit,
    macroExpansionBudget,
    primitivesIn,
    qualifiedRefsIn,
    renderExpansionChain,
    selectClause,
    termsSize,
    varCounts,
  )
import YCHR.Internal.Rename.Types
import YCHR.Internal.Resolved (maxTellArity)
import YCHR.Internal.Types

-- | Errors raised while resolving and qualifying surface names. Most
-- constructors carry the offending surface name (with its arity where
-- relevant) and/or the modules involved; the three nullary ones carry no
-- payload.
data RenameError
  = -- | An unqualified name that several visible modules provide at the
    -- same arity (YCHR-20001). Carries the name, arity, and providers;
    -- qualifying the reference resolves it.
    AmbiguousName Text Int [Text]
  | -- | An unqualified name that no visible declaration provides, in a
    -- position that requires a callable (YCHR-20002). Carries the name
    -- and arity.
    UnknownName Text Int
  | -- | A name in a module's own export list that the module does not
    -- declare (YCHR-20003). Carries the module, name, and arity.
    UnknownExport Text Text Int
  | -- | A name in a @use_module@ import list that the source module does
    -- not export (YCHR-20005). Carries the source module, name, and arity.
    UnknownImport Text Text Int
  | -- | A qualified reference @M:n/a@ where @M@ /is/ imported by the
    -- current module but does not export @(n, arity)@ (or the name is
    -- excluded by a restricted import list). Carries the source module
    -- name, the name, and the arity. See 'ModuleNotImported' and
    -- 'UnknownModule' for the not-imported / non-existent cases.
    NotExportedByModule Text Text Int
  | -- | A qualified reference @M:n/a@ where module @M@ exists in the
    -- program but the current module never imports it (qualification
    -- does not bypass the import requirement). Carries the source
    -- module name, the name, and the arity.
    ModuleNotImported Text Text Int
  | -- | A qualified reference @M:n/a@ where no module named @M@ exists
    -- anywhere in the program. Carries the unknown module name.
    UnknownModule Text
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
  | -- | A bare reference to a name that is visible both as a data
    -- constructor and as a function. The two namespaces would
    -- otherwise be told apart by syntactic position — pattern
    -- positions take the constructor, evaluating positions take the
    -- function — which makes the same text mean different things in
    -- different parts of one rule. Arity is not part of the
    -- comparison: constructors are name-only in the type system, and
    -- the reader cannot use arity to tell which is meant.
    --
    -- Qualifying the reference resolves it, since @a:foo@ and
    -- @b:foo@ name exactly one thing each. The same clash /inside/ one
    -- module has no such escape and is rejected at the declaration
    -- instead ('YCHR.Internal.Resolve.ConstructorFunctionCollision',
    -- YCHR-16020).
    --
    -- Carries the name, the modules declaring it as a constructor, and
    -- the modules declaring it as a function.
    ConstructorFunctionAmbiguity Text [Text] [Text]
  | -- | A @:- chr_type@ / @:- opaque_type@ declaration whose name is a
    -- reserved type name: a base type (@int@, @float@, @string@,
    -- @any@) or function-type syntax (@fun@, @->@). Declaring one
    -- would turn every use of the name in the module into a nominal
    -- user type. Carries the type name and arity.
    ReservedTypeName Text Int
  | -- | The same @(name, arity)@ is declared by two type declarations
    -- in one module. The renamer resolves type names by single
    -- provider, so every use would degrade to an unresolved name.
    -- Carries the type name and arity.
    DuplicateTypeDeclaration Text Int
  | -- | A type declaration collides with a type of the same name and
    -- arity visible through an import. Carries the type name, the
    -- arity, and the providing module.
    TypeShadowsImport Text Int Text
  | -- | A @use_module@ directive targeting the prelude carries an import
    -- list. The prelude is imported implicitly and in full by every
    -- module, so an import list on it has no effect; rather than
    -- silently ignoring it, reject it. The unrestricted form
    -- (@:- use_module(library(prelude)).@) is still accepted, and
    -- redundant.
    PreludeImportList
  | -- | A rule body uses the disjunction operator @;@ in a module that
    -- does not import @library(search)@. @;@ lowers to a
    -- @search:alt\/1@ choice point, so the module that writes one has
    -- to import the module that declares it — qualification is not an
    -- escape here, because the reference is generated rather than
    -- written.
    DisjunctionWithoutSearch
  | -- | The disjunction operator @;@ appears where a body goal cannot:
    -- a guard, an @is@ right-hand side, or a function body. @;@ is a
    -- choice between /goals/, and only a rule body has goals in it.
    -- Inside @quote\/1@ it stays ordinary data and is not affected.
    DisjunctionNotInRuleBody
  | -- | A @:- macro@ use's name is not recognized because it appears
    -- outside a goal position: a guard, an @is@ right-hand side, a
    -- lambda body, a function equation (which has no goal positions
    -- at all), or a @fun name\/arity@ function reference. The
    -- exceptions are @quote\/1@ and rule-head\/equation /arguments/,
    -- both opaque data, where the same compound is an ordinary term.
    -- Carries the macro's qualified name and arity.
    MacroOutsideGoalPosition QualifiedName Int
  | -- | A macro use was reached again while it was still being
    -- expanded, with the same macro and identical arguments up to
    -- renaming of variables — the expansion can never finish. Carries
    -- the qualified macro name and arity; the macro-expansion chain on
    -- the diagnostic itself names every macro in the cycle.
    MacroCycle QualifiedName Int
  | -- | A rule-head expansion produced something other than a
    -- conjunction of constraints — a disjunction, a simpagation
    -- @\\@, a bare variable or literal, or any other non-constraint
    -- shape. Carries the macro whose expansion produced it.
    MacroInvalidInHead QualifiedName Int
  | -- | Two definitions of the same macro @name\/arity@ in one module:
    -- two one-line definitions, two @:- macro Name\/N@ declarations, a
    -- one-line definition and a declaration, or further clauses for a
    -- macro defined by the one-line form. Carries the name and arity.
    DuplicateMacro Text Int
  | -- | A @:- macro@ definition shares its @name\/arity@ with a
    -- @:- chr_constraint@ or @:- function@ declared in the same
    -- module. Carries the macro's qualified name and arity.
    MacroNameCollision QualifiedName Int
  | -- | The built-in @tell\/N@ appears outside a goal position: a guard,
    -- an @is@ right-hand side, a lambda body or a function equation.
    -- @tell@ tells a constraint, and only a rule body or a query has
    -- goals. Inside @quote\/1@ and in head\/equation arguments it stays
    -- ordinary data, as a macro name does. Carries the arity used.
    TellOutsideGoalPosition Int
  | -- | @tell@ used as a goal with no argument (a bare @tell@) or with
    -- more than 'maxTellArity' of them. Carries the number of
    -- arguments.
    UnsupportedTellArity Int
  | -- | A @tell\/N@ whose goal is written literally as a body control
    -- form — a conjunction, a disjunction, @true@, @=@, @is@ or another
    -- @tell@ — rather than a constraint. Each is a goal the body can
    -- state directly, and none is a constraint @tell@ could reach.
    -- Carries the form's name and arity.
    TellControlGoal Text Int
  | -- | A macro body refers to @M:x\/a@, where @M@ is the macro's own
    -- declaring module, and @M@ does not declare and export
    -- @x\/a@ (as a constraint, function, macro, or data constructor).
    -- Without this check every use of the macro would fail the same
    -- way, at the use site instead of the definition. Carries the
    -- macro's qualified name and arity, and the undeclared reference's
    -- name and arity.
    MacroBodyNotExported QualifiedName Int Text Int
  | -- | No clause of the macro matches the use. Carries the qualified
    -- macro name and the use's arguments, as written.
    NoMatchingMacroClause QualifiedName [Term]
  | -- | A chain of nested macro expansions exceeds 'macroDepthLimit'.
    -- Carries the qualified name and arity of the macro whose use went
    -- past the limit.
    MacroExpansionTooDeep QualifiedName Int
  | -- | A part of a rule head that the rule's form requires is empty
    -- after macro expansion. Carries the part.
    MacroEmptyHead HeadPart
  | -- | An operand of a construction primitive breaks its rules.
    -- Carries the operand (which names its primitive) and the term it
    -- received.
    MalformedMacroPrimitive PrimitiveOperand Term
  | -- | One top-level macro use caused more than
    -- 'macroExpansionBudget' expansions in total. Carries the
    -- qualified name and arity of the macro whose expansion went over.
    MacroExpansionTooLarge QualifiedName Int
  | -- | A construction primitive remains after expansion: it was not
    -- written in a macro body (it is in ordinary code, in a macro head
    -- pattern, or arrived through a macro argument), or a constraint or
    -- function declaration uses one of the two reserved names. Carries
    -- the primitive's name and arity.
    MacroPrimitiveOutsideMacro Text Int
  | -- | A name that matches only a macro of the other kind: a goal macro
    -- used as a directive, or a declaration macro in a goal position.
    -- Name, arity, and the kind of the macro found.
    MacroKindMismatch QualifiedName Int MacroKind
  | -- | A rule head consists of aggregates only. An aggregate reads the
    -- store, so a rule with no regular head conjunct has no combination
    -- of heads to fire on. Checked after macro expansion, so a macro
    -- that expands to nothing but aggregates still reports.
    AggregateOnlyHead
  | -- | The aggregate core form or a selection form is used outside a
    -- rule head: in a body, a query or a guard. Carries the functor's
    -- name and the arity used.
    AggregateOutsideHead Text Int
  | -- | An aggregate's arguments are malformed: the wrong number of
    -- them, or a goal conjunct that is neither a constraint, a nested
    -- aggregate nor a @?@ guard. Carries the aggregate's functor name,
    -- the arity the form requires, and the arity used.
    MalformedAggregateGoal Text Int Int
  | -- | A @?\/1@ guard outside an aggregate goal. It is recognized
    -- structurally inside one, and has no meaning anywhere else.
    GuardOutsideAggregateGoal
  deriving (Eq, Show)

-- | A part of a rule head, for 'MacroEmptyHead'.
data HeadPart
  = -- | The whole head of a simplification or propagation rule.
    WholeHead
  | -- | The kept part of a simpagation rule (before @\\@).
    KeptPart
  | -- | The removed part of a simpagation rule (after @\\@).
    RemovedPart
  deriving (Eq, Show)

-- | Non-fatal warnings about data-constructor references the renamer could
-- not fully validate.
data RenameWarning
  = -- | A functor used in a data position that matches no declared data
    -- constructor (YCHR-20101). Carries the name.
    UndeclaredDataConstructor Text
  | -- | A declared data constructor used with the wrong number of
    -- arguments (YCHR-20102). Carries the name and the arity used.
    DataConstructorArityMismatch Text Int
  | -- | A head variable of a macro clause that occurs only once in the
    -- clause, in the head and not in the body: the corresponding
    -- argument is dropped. Variables whose name starts with @_@ are
    -- exempt. Carries the macro's qualified name and the variable.
    UnusedMacroParameter QualifiedName Text
  deriving (Eq, Show)

-- | Maps data constructor names to their declared arities (from type
-- declarations). A single name may be declared at several arities across
-- different types.
type DataConEnv = Map Text [Int]

-- | Maps @(constructorName, arity)@ to the list of modules that declare it.
-- Built from the same declarations as 'DataConEnv' but indexed and valued
-- so the renamer can canonicalize bare uses of declared constructors to
-- their qualified form (the runtime then sees one canonical flat atom).
type DataConProviders = Map UnqualifiedIdentifier [Text]

-- | A type declaration: declaring module, type name and arity. Key of
-- the constructor-visibility maps, so two types with the same name in
-- different modules don't collide.
data DeclaredType = DeclaredType
  { declaringModule :: Text,
    name :: Text,
    arity :: Int
  }
  deriving (Eq, Ord, Show)

-- | Renamer monad: the macro-expansion state ('MacroState') over two
-- stacked 'Writer's, one for errors (inner) and one for warnings
-- (middle). Concrete type so callers don't need 'mtl' classes;
-- 'emitError' lifts past the state and warning layers.
type Rename =
  StateT
    MacroState
    (WriterT [Diagnostic RenameWarning] (Writer [Diagnostic RenameError]))

-- | The state macro expansion threads through one renaming run.
data MacroState = MacroState
  { -- | The next seed 'freshMacroSeed' hands out.
    nextSeed :: Int,
    -- | Expansions the current top-level macro use may still cause
    -- (see 'macroExpansionBudget'). Reset at every top-level use.
    remaining :: Int,
    -- | Set once the current top-level use failed with
    -- 'MacroExpansionTooDeep' or 'MacroExpansionTooLarge', or with an
    -- expansion error in a nested use: the rest of its expansion is
    -- abandoned without further diagnostics, so a macro that branches
    -- as it recurses reports the problem once.
    abandoned :: Bool
  }

-- | The state a renaming run starts with.
initialMacroState :: MacroState
initialMacroState =
  MacroState {nextSeed = 0, remaining = macroExpansionBudget, abandoned = False}

-- | A seed, distinct on every call within one renaming run, that
-- 'YCHR.Internal.Rename.Macro.instantiateClause' uses to freshen a
-- macro body's non-parameter variables. Don't key it on the use's
-- 'SourceLoc': all goals of one rule section share one 'SourceLoc'
-- (see 'YCHR.Internal.Parsed.Rule'), so two uses there would alias
-- their fresh variables.
freshMacroSeed :: Rename Int
freshMacroSeed = do
  st <- get
  put st {nextSeed = st.nextSeed + 1}
  pure st.nextSeed

-- | Emit an error with no macro-expansion context. Used by checks that
-- never run on macro-expanded code (export/import-list and type-decl
-- validation); every other site goes through 'emitErrorIn' so its
-- diagnostic carries whatever macro chain is active.
emitError :: AnnP RenameError -> Rename ()
emitError e = lift (lift (tell [noDiag e]))

-- | Emit an error, attaching the current macro-expansion chain
-- (rendered, innermost first) from 'RenameCtx.macroChain'. Used at
-- every site reachable while renaming a rule head, body, guard, or
-- equation — i.e. everywhere macro-expanded code could be in scope.
emitErrorIn :: RenameCtx -> AnnP RenameError -> Rename ()
emitErrorIn ctx e =
  lift (lift (tell [(noDiag e) {context = renderMacroChain ctx}]))

-- | Emit a warning, attaching the current macro-expansion chain. See
-- 'emitErrorIn'.
emitWarningIn :: RenameCtx -> AnnP RenameWarning -> Rename ()
emitWarningIn ctx w =
  lift (tell [(noDiag w) {context = renderMacroChain ctx}])

-- | One use in the chain of macro expansions currently in progress.
data MacroUse = MacroUse
  { -- | The module that defines the macro.
    definingModule :: Text,
    name :: Text,
    arity :: Int,
    -- | The use's arguments, as written, for the repeat check.
    arguments :: [Term],
    -- | 'termsSize' of 'arguments', compared before 'isVariant'.
    argumentsSize :: Int,
    -- | Where the use is (for a nested use, the outermost use site).
    site :: SourceLoc,
    -- | The number of uses in the chain, this one included.
    depth :: Int
  }

-- | The @(definingModule, name, arity)@ identity of a chain entry.
macroUseKey :: MacroUse -> QualifiedIdentifier
macroUseKey u = QualifiedIdentifier u.definingModule u.name u.arity

-- | The chain shown on a diagnostic: goal-macro uses first, then the
-- declaration macros that generated the rule or equation. Innermost
-- first.
renderMacroChain :: RenameCtx -> [Text]
renderMacroChain ctx =
  renderExpansionChain (map useStep ctx.macroChain ++ ctx.declChain)
  where
    useStep u =
      ExpansionStep
        { macroModule = u.definingModule,
          macroName = u.name,
          macroArity = u.arity,
          site = u.site
        }

-- | Global environments consulted while renaming one module. Bundled
-- into a record so recursive helpers don't have to thread every
-- environment as a separate parameter.
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
    -- 'NonExportedConstructor'; otherwise 'NotExportedByModule'.
    allDataConProviders :: DataConProviders,
    -- | Functions visible to the current module, keyed by base name
    -- with no arity and with constraints excluded. Paired with
    -- 'dataConEnv' (also name-keyed) to decide whether a bare name is
    -- ambiguous across the two namespaces; see
    -- 'checkConstructorFunctionAmbiguity'.
    visibleFunNames :: Map Text [Text],
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
    -- | Every module name present in the program. Used to distinguish a
    -- qualified reference to a real-but-unimported module
    -- ('ModuleNotImported') from one to a non-existent module
    -- ('UnknownModule').
    allModuleNames :: [Text],
    currentModule :: CollectedModule,
    -- | @currentModule@'s imports without their annotations. Computed
    -- once per module, since the visibility checks run once per name.
    moduleImports :: [CollectedImport],
    -- | Where each @(name, arity)@ macro is /declared/, mirroring
    -- 'declEnv' for the macro namespace. Built from every module's
    -- @macros@ field.
    macroDeclEnv :: DeclEnv,
    -- | Where each @(name, arity)@ macro is /exported/, mirroring
    -- 'exportEnv' for the macro namespace.
    macroExportEnv :: ExportEnv,
    -- | Every macro's own definition, keyed by its declaring module,
    -- name, and arity. Looked up once a use has been resolved to a
    -- provider module (by 'visibleMacroProviders' or a qualified
    -- reference) to get at the actual 'MacroDef' to instantiate.
    macroDefTable :: Map QualifiedIdentifier MacroDef,
    -- | The chain of macro uses currently being expanded, innermost
    -- (most recently entered) first. Used for the repeat check
    -- ('MacroCycle'), the depth limit ('MacroExpansionTooDeep') and,
    -- rendered by 'renderMacroChain', as the context on every
    -- diagnostic raised while expanding. Empty outside any expansion.
    macroChain :: [MacroUse],
    -- | Declaration macros that generated the current rule or equation
    -- ('Rule.expansion'). Shown after 'macroChain'.
    declChain :: [ExpansionStep]
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
buildDataConEnv :: Map DeclaredType (Set.Set Text) -> [CollectedModule] -> DataConEnv
buildDataConEnv visible mods =
  Map.fromListWith
    (++)
    [ (t, [length dc.conArgs])
    | m <- mods,
      Ann td _ <- m.typeDecls,
      let key =
            DeclaredType m.name (unqualifiedText td.name) (length td.typeVars),
      Just visibleCons <- [Map.lookup key visible],
      dc <- typeConstructors td,
      Unqualified t <- [dc.conName],
      t `Set.member` visibleCons
    ]

-- | Build the @(constructorName, arity) -> [declaringModule]@ index used
-- by the renamer's data-constructor canonicalization. Same scope as
-- 'buildDataConEnv': only constructors whose declaring type is visible
-- to the current module, and only constructors permitted by the
-- visibility map's value-side allowlist.
buildDataConProviders ::
  Map DeclaredType (Set.Set Text) -> [CollectedModule] -> DataConProviders
buildDataConProviders visible mods =
  Map.fromListWith
    (++)
    [ (UnqualifiedIdentifier t (length dc.conArgs), [m.name])
    | m <- mods,
      Ann td _ <- m.typeDecls,
      let key =
            DeclaredType m.name (unqualifiedText td.name) (length td.typeVars),
      Just visibleCons <- [Map.lookup key visible],
      dc <- typeConstructors td,
      Unqualified t <- [dc.conName],
      t `Set.member` visibleCons
    ]

-- | Like 'buildDataConProviders' but ignores the visibility map. The
-- result lists every declared @(constructorName, arity)@ alongside the
-- modules that declare it, regardless of export allowlists or import
-- lists. Used to distinguish "declared but hidden" from "not declared
-- at all" when emitting diagnostics for qualified references.
buildAllDataConProviders :: [CollectedModule] -> DataConProviders
buildAllDataConProviders mods =
  Map.fromListWith
    (++)
    [ (UnqualifiedIdentifier t (length dc.conArgs), [m.name])
    | m <- mods,
      Ann td _ <- m.typeDecls,
      dc <- typeConstructors td,
      Unqualified t <- [dc.conName]
    ]

-- | Canonicalize a use-site data-constructor reference to its declared
-- 'Qualified' form when exactly one declaration matches @(name, arity)@.
-- Returns 'Nothing' for unknown or ambiguous names — callers fall back to
-- their existing handling (typically: leave the name 'Unqualified' and
-- emit an undeclared-data-constructor warning).
canonicalizeDataCon :: RenameCtx -> Text -> Int -> Maybe Name
canonicalizeDataCon ctx n arity =
  case Map.lookup (UnqualifiedIdentifier n arity) ctx.dataConProviders of
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
  case Map.lookup (UnqualifiedIdentifier n arity) ctx.dataConProviders of
    Just ms@(_ : _ : _) ->
      emitErrorIn ctx (AnnP (AmbiguousDataConstructor n ms) loc origin)
    _ -> pure ()

-- | Emit 'ConstructorFunctionAmbiguity' (YCHR-20020) when a bare name
-- is visible both as a data constructor and as a function. Called at
-- every leg of 'renameTerm' that has to decide which namespace an
-- unqualified name belongs to.
--
-- Both sides are compared without arity, so @float/0@ the constructor
-- clashes with @float/1@ the function.
--
-- Cases deliberately excluded:
--
--   * reserved symbols (@true@, @is@, @fun@, ...), which never reach
--     either namespace;
--   * a clash where the current module supplies /both/ sides. No
--     qualified form separates those, so \"qualify it\" would be wrong
--     advice; the resolver rejects the declaration itself instead
--     ('YCHR.Internal.Resolve.ConstructorFunctionCollision'). Any
--     further provider of either side is subsumed by that error.
--   * @fun name/arity@ references, which reach 'renameTerm' through
--     their own leg and never get here. That leg is not a decision
--     point: the syntax names the callable namespace outright, so
--     @fun leaf/1@ is a function reference no matter what
--     constructors are in scope.
--
-- The /constraint/ namespace is outside this check because it raises
-- no ambiguity to resolve: 'Resolve.termToExpr' never turns a
-- compound into a constraint call, so a constraint name and a
-- constructor name never contend for the same reading. A constraint
-- may share a name with a data constructor. Hence this check reads
-- only 'FunctionDecl' (see 'buildVisibleFunctionNames').
checkConstructorFunctionAmbiguity ::
  RenameCtx -> SourceLoc -> PExpr -> Text -> Rename ()
checkConstructorFunctionAmbiguity ctx loc origin n
  | isReserved n = pure ()
  | otherwise =
      let conMods = conProvidersAnyArity ctx n
          funMods = Map.findWithDefault [] n ctx.visibleFunNames
          self = ctx.currentModule.name
          declaresBoth = self `elem` conMods && self `elem` funMods
          err = ConstructorFunctionAmbiguity n conMods funMods
       in when (not (null conMods) && not (null funMods) && not declaresBoth) $
            emitErrorIn ctx (AnnP err loc origin)

-- | Every module that makes @n@ visible as a data constructor, at any
-- arity. 'dataConEnv' supplies the arities the name is declared at and
-- 'dataConProviders' the modules for each, both already filtered to
-- what the current module can see.
conProvidersAnyArity :: RenameCtx -> Text -> [Text]
conProvidersAnyArity ctx n =
  nub
    [ m
    | arity <- Map.findWithDefault [] n ctx.dataConEnv,
      m <- Map.findWithDefault [] (UnqualifiedIdentifier n arity) ctx.dataConProviders
    ]

-- | All declared constraints and functions across all modules, indexed by
-- @(name, arity)@. Functions and constraints share a namespace, so both
-- kinds of declaration are included.
buildDeclEnv :: [CollectedModule] -> DeclEnv
buildDeclEnv mods =
  makeDeclEnv
    [ (k, [m.name])
    | m <- mods,
      Ann d _ <- m.decls,
      Just k <- [declNameArity d]
    ]

-- | Only /exported/ constraints and functions (for cross-module resolution).
-- Modules without a @module@ directive (@exports = Nothing@) export
-- everything. Operator and type export declarations are filtered out — they
-- live in separate namespaces.
buildExportEnv :: [CollectedModule] -> ExportEnv
buildExportEnv mods =
  makeExportEnv
    [ (k, [m.name])
    | m <- mods,
      d <- case m.exports of
        Nothing -> map (.node) m.decls
        Just annExports -> filter isConstraintOrFunctionDecl annExports.node,
      Just k <- [declNameArity d]
    ]

-- | All type declarations across all modules.
buildTypeDeclEnv :: [CollectedModule] -> DeclEnv
buildTypeDeclEnv mods =
  makeDeclEnv
    [ (UnqualifiedIdentifier (unqualifiedText td.name) (length td.typeVars), [m.name])
    | m <- mods,
      Ann td _ <- m.typeDecls
    ]

-- | Only /exported/ types (for cross-module resolution). Modules without an
-- export list export every type they declare.
buildTypeExportEnv :: [CollectedModule] -> ExportEnv
buildTypeExportEnv mods =
  makeExportEnv
    [ (key, [m.name])
    | m <- mods,
      key <- case m.exports of
        Nothing ->
          [ UnqualifiedIdentifier (unqualifiedText td.name) (length td.typeVars)
          | Ann td _ <-
              m.typeDecls
          ]
        Just annExports ->
          [UnqualifiedIdentifier td.name td.arity | TypeExportDecl td <- annExports.node]
    ]

-- | Where each @(name, arity)@ macro is declared, mirroring
-- 'buildDeclEnv' for the macro namespace: macros are a separate
-- namespace from constraints and functions (see
-- 'MacroNameCollision'), so this is kept apart from 'DeclEnv' rather
-- than folded into it.
buildMacroDeclEnv :: [CollectedModule] -> DeclEnv
buildMacroDeclEnv mods =
  makeDeclEnv
    [ (UnqualifiedIdentifier d.node.name d.node.arity, [m.name])
    | m <- mods,
      d <- m.macros
    ]

-- | Where each @(name, arity)@ macro is exported. A module with no
-- export list exports every macro it defines; otherwise only the
-- @macro(name\/arity)@ entries in its export list count. Mirrors
-- 'buildExportEnv' for the macro namespace.
buildMacroExportEnv :: [CollectedModule] -> ExportEnv
buildMacroExportEnv mods =
  makeExportEnv
    [ (key, [m.name])
    | m <- mods,
      key <- case m.exports of
        Nothing -> [UnqualifiedIdentifier d.node.name d.node.arity | d <- m.macros]
        Just annExports ->
          [ UnqualifiedIdentifier meb.name meb.arity
          | MacroExportDecl meb <- annExports.node,
            any (\d -> d.node.name == meb.name && d.node.arity == meb.arity) m.macros
          ]
    ]

-- | Every macro's own definition, keyed by its declaring module, name,
-- and arity. A module's /own/ macros only — the table is consulted
-- after 'visibleMacroProviders' (or a qualified reference) has already
-- named the provider module, so no visibility filtering happens here.
-- If a module defines a key twice ('DuplicateMacro'), the first
-- definition wins.
buildMacroDefTable :: [CollectedModule] -> Map QualifiedIdentifier MacroDef
buildMacroDefTable mods =
  Map.fromListWith
    (\_new old -> old)
    [ (QualifiedIdentifier m.name d.node.name d.node.arity, d.node)
    | m <- mods,
      d <- m.macros
    ]

-- | The @(name, arity)@ a declaration is referenced by. Operator
-- declarations name an operator rather than a symbol in the
-- constraint/function namespace, so they contribute nothing.
declNameArity :: Declaration -> Maybe UnqualifiedIdentifier
declNameArity (ConstraintDecl cd) = Just (UnqualifiedIdentifier cd.name cd.arity)
declNameArity (FunctionDecl fd) = Just (UnqualifiedIdentifier fd.name fd.arity)
declNameArity (ExtendClassTypeDecl ed) = Just (UnqualifiedIdentifier ed.name ed.arity)
declNameArity (TypeExportDecl td) = Just (UnqualifiedIdentifier td.name td.arity)
declNameArity (OperatorDecl {}) = Nothing
-- Macros are tracked through their own table ('YCHR.Internal.Rename.Macro'),
-- not through 'DeclEnv'\/'ExportEnv': they are a separate namespace from
-- constraints and functions, so a 'MacroExportDecl' export/import item
-- contributes nothing here.
declNameArity (MacroExportDecl {}) = Nothing

isConstraintOrFunctionDecl :: Declaration -> Bool
isConstraintOrFunctionDecl ConstraintDecl {} = True
isConstraintOrFunctionDecl FunctionDecl {} = True
isConstraintOrFunctionDecl _ = False

-- ---------------------------------------------------------------------------
-- Entry points
-- ---------------------------------------------------------------------------

-- | Rename a multi-module program: qualify every constraint, function,
-- type, and data-constructor reference against the appropriate provider
-- module, and validate export and import lists. Caller-supplied
-- 'RenameInputs' carries per-module operator-export tables and trailing
-- header locations gathered by 'YCHR.Internal.Collect'; pass 'defaultRenameInputs'
-- when those tables are unavailable (tests, query renaming).
-- Returns the renamed modules and any warnings on success, or the
-- accumulated diagnostics on failure.
renameProgram ::
  RenameInputs ->
  [CollectedModule] ->
  Either
    [Diagnostic RenameError]
    ( [CollectedModule],
      [Diagnostic RenameWarning]
    )
renameProgram inputs mods =
  let declEnv0 = buildDeclEnv mods
      exportEnv0 = buildExportEnv mods
      typeDeclEnv0 = buildTypeDeclEnv mods
      typeExportEnv0 = buildTypeExportEnv mods
      allCons = buildAllDataConProviders mods
      macroDeclEnv0 = buildMacroDeclEnv mods
      macroExportEnv0 = buildMacroExportEnv mods
      macroDefTable0 = buildMacroDefTable mods
      ctxFor m =
        let ctx0 =
              RenameCtx
                { declEnv = declEnv0,
                  exportEnv = exportEnv0,
                  dataConEnv = Map.empty,
                  dataConProviders = Map.empty,
                  allDataConProviders = allCons,
                  visibleFunNames = buildVisibleFunctionNames mods m,
                  typeDeclEnv = typeDeclEnv0,
                  typeExportEnv = typeExportEnv0,
                  operatorExports = inputs.operatorExports,
                  currentTrailingLoc =
                    Map.findWithDefault Nothing m.name inputs.trailingLoc,
                  allModuleNames = map (.name) mods,
                  currentModule = m,
                  moduleImports = [imp | AnnP imp _ _ <- m.imports],
                  macroDeclEnv = macroDeclEnv0,
                  macroExportEnv = macroExportEnv0,
                  macroDefTable = macroDefTable0,
                  macroChain = [],
                  declChain = []
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
            ( runWriterT $
                evalStateT
                  ( do
                      validateExports mods
                      traverse (\m -> renameModule mods (ctxFor m)) mods
                  )
                  initialMacroState
            )
   in if null errs then Right (result, warnings) else Left errs

-- | Check that every name in a module's export list is actually declared.
validateExports :: [CollectedModule] -> Rename ()
validateExports = traverse_ validateOne
  where
    validateOne m = case m.exports of
      Nothing -> pure ()
      Just (AnnP exports loc origin) -> traverse_ (checkExport m loc origin) exports

    checkExport m loc origin d = case d of
      ConstraintDecl ConstraintDeclBody {name, arity}
        | not (isDeclared m name arity) ->
            emitError (AnnP (UnknownExport m.name name arity) loc origin)
      FunctionDecl FunctionDeclBody {name, arity}
        | not (isDeclared m name arity) ->
            emitError (AnnP (UnknownExport m.name name arity) loc origin)
      TypeExportDecl TypeExportDeclBody {name, arity, conExports}
        | not (isTypeDeclared m name arity) ->
            emitError (AnnP (UnknownExport m.name name arity) loc origin)
        | otherwise ->
            checkConList m loc origin name arity conExports
      MacroExportDecl MacroExportDeclBody {name, arity}
        | not (isMacroDeclared m name arity) ->
            emitError (AnnP (UnknownExport m.name name arity) loc origin)
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

    isDeclared m n a =
      UnqualifiedIdentifier n a
        `elem` [k | Ann d _ <- m.decls, Just k <- [declNameArity d]]
    isTypeDeclared m n a =
      UnqualifiedIdentifier n a
        `elem` [ UnqualifiedIdentifier (unqualifiedText td.name) (length td.typeVars)
               | Ann td _ <- m.typeDecls
               ]
    isMacroDeclared m n a =
      UnqualifiedIdentifier n a
        `elem` [UnqualifiedIdentifier d.node.name d.node.arity | d <- m.macros]

    declaredConstructors m n a =
      [ unqualifiedText dc.conName
      | Ann td _ <- m.typeDecls,
        unqualifiedText td.name == n,
        length td.typeVars == a,
        dc <- typeConstructors td
      ]

-- ---------------------------------------------------------------------------
-- Module, rule, equation, head renaming
-- ---------------------------------------------------------------------------

renameModule :: [CollectedModule] -> RenameCtx -> Rename CollectedModule
renameModule mods ctx = do
  let m = ctx.currentModule
  validateImportLists mods ctx
  validateTypeDecls ctx
  checkMacroDefinitions ctx
  renamedRules <- traverse (renameRule ctx) m.rules
  renamedEquations <- traverse (traverse (renameEquation ctx)) m.equations
  renamedExtensions <- traverse (traverse (renameEquation ctx)) m.extensions
  renamedClassExtensions <- traverse (traverse (renameEquation ctx)) m.classExtensions
  let renamedTypeDecls = map (fmap (renameTypeDefinition ctx)) m.typeDecls
  renamedDecls <- traverse (renameAnnDecl ctx) m.decls
  renamedExtensionTypes <- traverse (renameAnnDecl ctx) m.extensionTypes
  -- Explicit construction (not @m { ... }@ record update): because
  -- 'CollectedModule' and 'Module' share field names, a record update of
  -- the variable @m@ is ambiguous (GHC cannot tell which record type is
  -- being updated). Naming the constructor resolves it unambiguously.
  pure
    CollectedModule
      { name = m.name,
        nameLoc = m.nameLoc,
        imports = m.imports,
        rules = renamedRules,
        equations = renamedEquations,
        extensions = renamedExtensions,
        classExtensions = renamedClassExtensions,
        inlines = m.inlines,
        constraintUses = m.constraintUses,
        macros = m.macros,
        typeDecls = renamedTypeDecls,
        decls = renamedDecls,
        extensionTypes = renamedExtensionTypes,
        exports = m.exports
      }

-- | Validate import lists. Five checks:
--
--   * A @use_module@ targeting the prelude must not carry an import
--     list, since the prelude is imported implicitly and in full
--     ('PreludeImportList').
--   * @op(...)@ entries must name an operator that the source module
--     actually exports ('UnknownOperatorImport').
--   * Constraint, function, type and macro imports must name something
--     the source module exports ('UnknownImport').
--   * A @type(t/n, [c, ...])@ import must list constructors that the
--     source module exports for that type ('UnknownExportedConstructor').
--   * Each @use_module@ directive must appear before the first non-import
--     directive in the file ('UseModuleOutOfOrder').
validateImportLists :: [CollectedModule] -> RenameCtx -> Rename ()
validateImportLists mods ctx =
  traverse_ checkImport ctx.currentModule.imports
  where
    -- The prelude import list is rejected wholesale rather than
    -- item-by-item: reporting each item as an unknown import on top of
    -- the real diagnostic would be pure noise. The synthetic prelude
    -- imports added by the pipeline carry no item list, so they never
    -- reach this arm.
    checkImport (AnnP imp loc origin) = do
      checkPlacement imp loc origin
      case imp.importItems of
        Just _
          | imp.importModule == "prelude" ->
              emitError (AnnP PreludeImportList loc origin)
        Just decls -> traverse_ (checkItem imp.importModule loc origin) decls
        Nothing -> pure ()

    checkPlacement imp loc origin = case ctx.currentTrailingLoc of
      Just tloc
        | loc.file == tloc.file,
          locAtOrAfter loc tloc ->
            emitError (AnnP (UseModuleOutOfOrder imp.importModule) loc origin)
      _ -> pure ()

    checkItem mn loc origin (OperatorDecl op) =
      when (op `notElem` Map.findWithDefault [] mn ctx.operatorExports) $
        emitError (AnnP (UnknownOperatorImport mn op.opName) loc origin)
    checkItem mn loc origin (ConstraintDecl ConstraintDeclBody {name = n, arity = a}) =
      when (mn `notElem` lookupExport (UnqualifiedIdentifier n a) ctx.exportEnv) $
        emitError (AnnP (UnknownImport mn n a) loc origin)
    checkItem mn loc origin (FunctionDecl FunctionDeclBody {name = n, arity = a}) =
      when (mn `notElem` lookupExport (UnqualifiedIdentifier n a) ctx.exportEnv) $
        emitError (AnnP (UnknownImport mn n a) loc origin)
    checkItem _ _ _ ExtendClassTypeDecl {} = pure ()
    checkItem mn loc origin (TypeExportDecl (TypeExportDeclBody n a cs)) =
      if mn `notElem` lookupExport (UnqualifiedIdentifier n a) ctx.typeExportEnv
        then emitError (AnnP (UnknownImport mn n a) loc origin)
        else checkImportedCons mn loc origin n a cs
    checkItem mn loc origin (MacroExportDecl MacroExportDeclBody {name = n, arity = a}) =
      when (mn `notElem` lookupExport (UnqualifiedIdentifier n a) ctx.macroExportEnv) $
        emitError (AnnP (UnknownImport mn n a) loc origin)

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
            dc <- typeConstructors td
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
                  case [ acs
                       | TypeExportDecl (TypeExportDeclBody tn ta acs) <- exports,
                         tn == n,
                         ta == a
                       ] of
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

-- | Definition-time checks on a module's @:- macro@ definitions,
-- mirroring 'validateImportLists' and 'validateTypeDecls': run once
-- per module, before any use site is renamed. The checks:
--
--   * 'DuplicateMacro' — a second definition of the same @name\/arity@
--     in this module (see its constructor for the forms).
--   * 'MacroNameCollision' — a macro sharing @name\/arity@ with a
--     @:- chr_constraint@ or @:- function@ of the same module.
--   * 'MacroBodyNotExported' — a self-qualified reference @M:x@ (@M@
--     being this module) in a clause body that @M@ does not both
--     declare and export, as a constraint, function, macro, or data
--     constructor.
--   * 'MacroPrimitiveOutsideMacro' — a construction primitive in a
--     clause's head patterns, which are never evaluated; or a
--     constraint or function declared with a primitive's reserved name.
--
-- Plus the 'UnusedMacroParameter' warning for a head variable that
-- occurs only once in its clause and whose name does not start with
-- @_@.
checkMacroDefinitions :: RenameCtx -> Rename ()
checkMacroDefinitions ctx = do
  _ <- foldM checkDuplicate Set.empty m.macros
  traverse_ checkCollision m.macros
  traverse_ checkClauses m.macros
  traverse_ checkReservedDecl m.decls
  where
    m = ctx.currentModule
    self = m.name
    declKeys = Set.fromList [k | Ann d _ <- m.decls, Just k <- [declNameArity d]]

    checkDuplicate seen annDef =
      let key = UnqualifiedIdentifier annDef.node.name annDef.node.arity
       in if Set.member key seen
            then do
              emitErrorIn
                ctx
                ( AnnP
                    (DuplicateMacro key.localName key.arity)
                    annDef.sourceLoc
                    annDef.parsed
                )
              pure seen
            else pure (Set.insert key seen)

    -- Declaration macros are only directives, so they may share names
    -- with constraints and functions.
    checkCollision annDef =
      let key = UnqualifiedIdentifier annDef.node.name annDef.node.arity
          err = MacroNameCollision (QualifiedName self key.localName) key.arity
       in when (annDef.node.kind == GoalMacro && Set.member key declKeys) $
            emitErrorIn ctx (AnnP err annDef.sourceLoc annDef.parsed)

    checkClauses annDef = traverse_ (checkClause annDef.node) annDef.node.clauses

    checkClause d (AnnP clause loc origin) = do
      let headCounts = Map.unionsWith (+) (map varCounts clause.params)
          bodyCounts = Map.unionsWith (+) (map varCounts clause.body)
          unused =
            [ v
            | (v, 1) <- Map.toList headCounts,
              not (Map.member v bodyCounts),
              not ("_" `Text.isPrefixOf` v)
            ]
          macroName = QualifiedName self d.name
          warnUnused v =
            emitWarningIn ctx (AnnP (UnusedMacroParameter macroName v) loc origin)
          checkRef (UnqualifiedIdentifier rn ra) =
            unless (selfDeclaresAndExports rn ra) $
              let err = MacroBodyNotExported macroName d.arity rn ra
               in emitErrorIn ctx (AnnP err loc origin)
          primitiveInHead p = primitiveOutsideMacro ctx loc origin p.name p.arity
      traverse_ warnUnused unused
      traverse_ checkRef (concatMap (qualifiedRefsIn self) clause.body)
      traverse_ primitiveInHead (concatMap primitivesIn clause.params)

    checkReservedDecl (Ann d loc) = case declNameArity d of
      Just (UnqualifiedIdentifier n a)
        | isConstraintOrFunctionDecl d,
          isPrimitiveName (Unqualified n) a ->
            let origin =
                  Compound "/" [Ann (Atom n) loc, Ann (PExpr.Int (toInteger a)) loc]
             in emitErrorIn ctx (AnnP (MacroPrimitiveOutsideMacro n a) loc origin)
      _ -> pure ()

    selfDeclaresAndExports n a =
      let key = UnqualifiedIdentifier n a
       in self `elem` lookupExport key ctx.exportEnv
            || self `elem` lookupExport key ctx.macroExportEnv
            || self `elem` Map.findWithDefault [] key ctx.dataConProviders

renameRule :: RenameCtx -> Rule -> Rename Rule
renameRule ctx0 r = do
  let ctx = ctx0 {declChain = r.expansion}
  h <- traverse (renameHead ctx r.head.sourceLoc r.head.parsed) r.head
  g <-
    traverse
      (traverse (renameTerm ctx r.guard.sourceLoc r.guard.parsed ResolveAll))
      r.guard
  b <-
    traverse
      ( fmap (orTrue . concat)
          . traverse (renameBodyGoal ctx r.body.sourceLoc r.body.parsed)
      )
      r.body
  -- 'h' is the whole head, so its node is the post-expansion head: an
  -- aggregate-only rule is exactly one whose kept and removed lists are
  -- both empty.
  let hd = h.node
      nHeads = case hd of
        Simplification cs _ -> length cs
        Propagation cs _ -> length cs
        Simpagation ks rs _ -> length ks + length rs
  checkAggregateOnlyHead ctx r.head.sourceLoc r.head.parsed nHeads (aggregateCount hd)
  pure r {head = h, guard = g, body = b}
  where
    aggregateCount hd = case hd of
      Simplification _ as -> length as
      Propagation _ as -> length as
      Simpagation _ _ as -> length as

-- | A rule body or query whose goals all expanded to nothing means
-- @true@ (see the Zero goals section of the macro reference).
orTrue :: [Term] -> [Term]
orTrue [] = [CompoundTerm (Unqualified "true") []]
orTrue ts = ts

renameEquation :: RenameCtx -> FunctionEquation -> Rename FunctionEquation
renameEquation ctx0 eq = do
  let ctx = ctx0 {declChain = eq.expansion}
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
  -- The parsed head carries no aggregates: the parser sees only the
  -- terms the source wrote, and an aggregate is a macro expansion (or a
  -- direct use of the reserved functors) that only this pass
  -- recognizes. The aggregates the parser could not see are therefore
  -- dropped here and rebuilt by 'renameCon'.
  Simplification cs _ -> do
    (ks, aggs) <- part WholeHead cs
    pure (Simplification ks aggs)
  Propagation cs _ -> do
    (ks, aggs) <- part WholeHead cs
    pure (Propagation ks aggs)
  Simpagation k r _ -> do
    (ks, kaggs) <- part KeptPart k
    (rs, raggs) <- part RemovedPart r
    pure (Simpagation ks rs (kaggs ++ raggs))
  where
    -- Every part of a head is required by its rule's form. A part that
    -- had conjuncts in the source but none after expansion (and lost
    -- none to an error already reported) is 'MacroEmptyHead': turning
    -- the rule into another kind of rule silently would change its
    -- semantics.
    --
    -- A macro in an aggregate's goal expands in place too, so the
    -- expansion is spliced before this runs and a head part may hold
    -- aggregates that came out of a macro body.
    part label cs = do
      items <- concat <$> traverse (renameCon ctx loc origin) cs
      let kept = [c | HeadOk c <- items]
          aggs = [a | HeadAggregate a <- items]
      when (null items && not (null cs)) $
        emitErrorIn ctx (AnnP (MacroEmptyHead label) loc origin)
      pure (kept, aggs)

-- | A rule must have at least one regular head conjunct: an aggregate
-- reads the store and contributes no constraint of its own, so a rule
-- of aggregates only would have no combination of heads to fire on and
-- no combination to record in the propagation history.
--
-- Checked per rule rather than per head part, after macro expansion, so
-- it also catches a macro that expanded to aggregates only. A rule with
-- no head conjuncts at all is not this error: it is the parser's
-- business, and it cannot carry an aggregate either.
checkAggregateOnlyHead :: RenameCtx -> SourceLoc -> PExpr -> Int -> Int -> Rename ()
checkAggregateOnlyHead ctx loc origin nHeads nAggs =
  when (nAggs > 0 && nHeads == 0) $
    emitErrorIn ctx (AnnP AggregateOnlyHead loc origin)

-- | One conjunct produced by renaming a head conjunct: a renamed
-- constraint, a renamed aggregate, or a placeholder for one dropped
-- after its error was reported (so an empty part is not reported a
-- second time as 'MacroEmptyHead').
data HeadItem = HeadOk Constraint | HeadAggregate Aggregate | HeadDropped

-- | Rename one head conjunct. A macro use expands to zero or more
-- constraint conjuncts (and, inside a macro body, aggregates), spliced
-- into the head at the position of the use ('expandHeadUse'); an
-- ordinary constraint renames to exactly one; the aggregate core form
-- and the selection forms rename to an 'Aggregate'.
renameCon :: RenameCtx -> SourceLoc -> PExpr -> Constraint -> Rename [HeadItem]
renameCon ctx loc origin (Constraint cname cargs)
  | Just k <- aggregateKindOf cname (length cargs) =
      -- Checked before 'classifyGoalName': a user may define a macro or
      -- function called @aggregate/4@, but the reserved aggregate
      -- functors always mean the aggregate form. The call site is the
      -- same shape, so the two cannot be told apart by name alone.
      (: []) . HeadAggregate <$> renameAggregate ctx loc origin k cargs
  | isPrimitiveName cname (length cargs) = do
      primitiveOutsideMacro ctx loc origin cname (length cargs)
      pure [HeadDropped]
  | otherwise = case classifyGoalName ctx cname (length cargs) of
      AmbiguousGoalName ms -> do
        let err = AmbiguousName (unqualifiedText cname) (length cargs) ms
        emitErrorIn ctx (AnnP err loc origin)
        pure [HeadDropped]
      IsMacro providerMod -> expandHeadUse ctx loc origin providerMod cname cargs
      IsDeclMacro providerMod -> do
        kindMismatch ctx loc origin providerMod cname (length cargs)
        pure [HeadDropped]
      -- A reserved name (@tell@, @quote@, @is@, …) never names a
      -- constraint. 'resolveName' passes reserved names through
      -- unqualified for the forms that use them, which in a head would
      -- reach Resolve as an internal error; report the unknown constraint
      -- here instead. A declaration of the name is Resolve's
      -- 'YCHR.Internal.Resolve.ReservedName' to report, so that case is
      -- left to it. The arguments are still renamed for their own
      -- diagnostics.
      NotAMacro
        | Unqualified n <- cname,
          isReserved n,
          null (visibleProviders ctx n (length cargs)) -> do
            traverse_ (renameTerm ctx loc origin NoResolve) cargs
            emitErrorIn ctx (AnnP (UnknownName n (length cargs)) loc origin)
            pure [HeadDropped]
      NotAMacro -> do
        renamedName <- resolveName ResolveTop ctx loc origin cname (length cargs)
        renamedArgs <- traverse (renameTerm ctx loc origin NoResolve) cargs
        pure [HeadOk (Constraint renamedName renamedArgs)]

-- | Report a construction primitive left after expansion.
primitiveOutsideMacro :: RenameCtx -> SourceLoc -> PExpr -> Name -> Int -> Rename ()
primitiveOutsideMacro ctx loc origin name arity =
  let err = MacroPrimitiveOutsideMacro (unqualifiedText name) arity
   in emitErrorIn ctx (AnnP err loc origin)

-- | Report a declaration macro used in a goal position.
kindMismatch :: RenameCtx -> SourceLoc -> PExpr -> Text -> Name -> Int -> Rename ()
kindMismatch ctx loc origin providerMod name arity =
  let qn = QualifiedName providerMod (unqualifiedText name)
   in emitErrorIn ctx (AnnP (MacroKindMismatch qn arity DeclMacro) loc origin)

-- | The 'AggregateKind' a head conjunct names, if it names one. Only an
-- unqualified name matches: a qualified @M:aggregate@ is an ordinary
-- constraint, so a user module can shadow an aggregate name locally.
aggregateKindOf :: Name -> Int -> Maybe AggregateKind
aggregateKindOf (Qualified _ _) _ = Nothing
aggregateKindOf (Unqualified n) arity = case (n, arity) of
  ("aggregate", 4) -> Just AggPlain
  ("argmin", 2) -> Just AggArgmin
  ("argmax", 2) -> Just AggArgmax
  ("takemin", 2) -> Just AggTakemin
  ("takemax", 2) -> Just AggTakemax
  _ -> Nothing

-- | Rename one aggregate. The arguments are renamed like head or body
-- terms, except the goal, whose conjuncts are classified structurally
-- ('?\/1' guards and nested aggregates) and whose constraints are
-- resolved like head constraints, since the rule observes the store
-- through them.
--
-- A malformed argument list (an aggregate at the wrong arity, or a goal
-- conjunct that is neither a constraint, a nested aggregate nor a @?@
-- guard) is reported and the aggregate dropped, so the rule keeps
-- compiling without it.
renameAggregate ::
  RenameCtx -> SourceLoc -> PExpr -> AggregateKind -> [Term] -> Rename Aggregate
renameAggregate ctx loc origin k cargs = do
  (mAgg, mElement, goalTerm, mResult) <- argTerms
  agg' <- traverse (renameTerm ctx loc origin ResolveAll) mAgg
  -- The element / selection key is a pattern over each match, so it is
  -- renamed without resolving names: a bare name in it is a user-written
  -- atom, and a variable of it that the goal does not bind is reported
  -- later, by the compiler (YCHR-40002).
  element' <- traverse (renameTerm ctx loc origin NoResolve) mElement
  result' <- traverse (renameTerm ctx loc origin NoResolve) mResult
  goal' <-
    concat
      <$> traverse
        (renameConjunct ctx loc origin (aggregateName k) (requiredArity k))
        (flattenConj goalTerm)
  pure
    Aggregate
      { kind = k,
        agg = agg',
        element = fromMaybe (CompoundTerm (Unqualified "") []) element',
        goal = goal',
        result = fromMaybe Wildcard result'
      }
  where
    argTerms = case cargs of
      -- aggregate(Agg, Element, Goal, Result)
      [a, e, g, r] | k == AggPlain -> pure (Just a, Just e, g, Just r)
      -- argmin(X, Goal) and friends: X is the selection key, which takes
      -- the place of the element. The Result is unused.
      [x, g] | k /= AggPlain -> pure (Nothing, Just x, g, Nothing)
      _ -> badArity

    badArity = do
      emitErrorIn
        ctx
        ( AnnP
            (MalformedAggregateGoal (aggregateName k) (requiredArity k) (length cargs))
            loc
            origin
        )
      pure (Nothing, Nothing, CompoundTerm (Unqualified "") [], Nothing)

-- | How many arguments an aggregate form takes, for diagnostics.
requiredArity :: AggregateKind -> Int
requiredArity AggPlain = 4
requiredArity _ = 2

-- | Rename one conjunct of an aggregate goal. The enclosing aggregate's
-- functor name and required arity are carried for diagnostics.
renameConjunct ::
  RenameCtx ->
  SourceLoc ->
  PExpr ->
  Text ->
  Int ->
  Term ->
  Rename [AggregateConjunct]
renameConjunct ctx loc origin outerName outerArity t = case t of
  CompoundTerm n args | isGuardFunctor n (length args) -> do
    let g = case args of
          [g0] -> g0
          -- Unreachable: 'isGuardFunctor' pins the arity at 1. Kept
          -- total rather than partial to avoid an irrefutable pattern.
          _ -> CompoundTerm (Unqualified "") []
    g' <- renameTerm ctx loc origin ResolveAll g
    pure [AggGuard g']
  CompoundTerm n args
    | Just k <- aggregateKindOf n (length args) ->
        (: []) . AggNested <$> renameAggregate ctx loc origin k args
    | isPrimitiveName n (length args) -> do
        primitiveOutsideMacro ctx loc origin n (length args)
        pure []
    -- A macro use inside an aggregate goal is a goal position like any
    -- other: it expands in place, and each goal of the expansion is a
    -- conjunct again (a constraint, a nested aggregate or a guard).
    | otherwise -> case classifyGoalName ctx n (length args) of
        IsMacro providerMod ->
          expandMacroUse ctx loc origin providerMod n args >>= \case
            Nothing -> pure []
            Just (ctx', goals) ->
              concat
                <$> traverse
                  (renameConjunct ctx' loc origin outerName outerArity)
                  (concatMap flattenConj goals)
        IsDeclMacro providerMod -> do
          kindMismatch ctx loc origin providerMod n (length args)
          pure []
        AmbiguousGoalName ms -> do
          let err = AmbiguousName (unqualifiedText n) (length args) ms
          emitErrorIn ctx (AnnP err loc origin)
          pure []
        -- A reserved name passes through 'resolveName' unqualified for the
        -- forms that use it, which would reach Resolve as an internal
        -- error; report the unknown constraint here, as 'renameCon' does
        -- for a head.
        NotAMacro
          | Unqualified base <- n,
            isReserved base,
            null (visibleProviders ctx base (length args)) -> do
              traverse_ (renameTerm ctx loc origin NoResolve) args
              emitErrorIn ctx (AnnP (UnknownName base (length args)) loc origin)
              pure []
        NotAMacro -> do
          renamedName <- resolveName ResolveTop ctx loc origin n (length args)
          renamedArgs <- traverse (renameTerm ctx loc origin NoResolve) args
          pure [AggConstraint (Constraint renamedName renamedArgs)]
  _ -> do
    -- The offending conjunct is not a constraint, an aggregate or a
    -- guard. Report it against the enclosing aggregate at the arity it
    -- was written with, which is the arity the user can see.
    emitErrorIn
      ctx
      (AnnP (MalformedAggregateGoal outerName outerArity outerArity) loc origin)
    pure []

-- | Whether a name and arity are the @?\/1@ aggregate-goal guard.
--
-- Recognition is structural, by name and arity, so both the operator
-- spelling @? G@ and the quoted functor @'?'(G)@ work, with or without
-- the operator declared. Only an unqualified name matches, so
-- @M:'?'(G)@ stays an ordinary constraint.
isGuardFunctor :: Name -> Int -> Bool
isGuardFunctor (Unqualified n) arity = n == "?" && arity == 1
isGuardFunctor (Qualified _ _) _ = False

-- | The reserved functor name of an aggregate kind, for diagnostics.
aggregateName :: AggregateKind -> Text
aggregateName AggPlain = "aggregate"
aggregateName AggArgmin = "argmin"
aggregateName AggArgmax = "argmax"
aggregateName AggTakemin = "takemin"
aggregateName AggTakemax = "takemax"

-- | Expand a macro use found in head position ('expandMacroUse'), and
-- classify each resulting goal with 'headConjunct': a constraint-shaped
-- goal is renamed (recursively — the replacement may itself use a
-- macro, in head position again); anything else is
-- 'MacroInvalidInHead'. A use that fails to expand is dropped, after
-- its error.
expandHeadUse ::
  RenameCtx -> SourceLoc -> PExpr -> Text -> Name -> [Term] -> Rename [HeadItem]
expandHeadUse ctx loc origin providerMod name args =
  expandMacroUse ctx loc origin providerMod name args >>= \case
    Nothing -> pure [HeadDropped]
    Just (ctx', goals) -> concat <$> traverse (expandedHeadGoal ctx') goals
  where
    expandedHeadGoal ctx' goal = case headConjunct goal of
      HeadConjunctOk c -> renameCon ctx' loc origin c
      HeadConjunctInvalid _ -> do
        let qn = QualifiedName providerMod (unqualifiedText name)
        emitErrorIn ctx' (AnnP (MacroInvalidInHead qn (length args)) loc origin)
        pure [HeadDropped]

-- | Expand one macro use, from any goal position: the shared core of
-- 'expandHeadUse', 'expandBodyUse' and 'expandQueryGoalWith'. Returns
-- the context to rename the replacement in (with this use pushed on
-- 'RenameCtx.macroChain') and the replacement goals, or 'Nothing' after
-- reporting why the use cannot be expanded:
--
--   * 'MacroExpansionTooDeep' — the chain is already 'macroDepthLimit'
--     uses deep;
--   * 'MacroExpansionTooLarge' — the top-level use this one belongs to
--     has already caused 'macroExpansionBudget' expansions.
--
-- After either of those two, and after any of the errors below in a
-- nested use, the rest of the top-level use's expansion is abandoned
-- silently ('MacroState.abandoned'), so the error is reported once.
-- Then:
--
--   * 'MacroCycle' — the same macro is being expanded higher up the
--     chain with variant arguments ('isVariant');
--   * 'NoMatchingMacroClause' — no clause's head matches the
--     arguments;
--   * 'MalformedMacroPrimitive' — a construction primitive in the
--     selected clause's body got a bad operand (reported with this use
--     in the chain).
expandMacroUse ::
  RenameCtx ->
  SourceLoc ->
  PExpr ->
  Text ->
  Name ->
  [Term] ->
  Rename (Maybe (RenameCtx, [Term]))
expandMacroUse ctx loc origin providerMod name args = do
  -- A use outside any expansion starts a fresh budget.
  when (null ctx.macroChain) $
    modify' (\st -> st {remaining = macroExpansionBudget, abandoned = False})
  st <- get
  case Map.lookup key ctx.macroDefTable of
    -- Defensive: 'classifyGoalName' only names real providers.
    Nothing -> pure Nothing
    Just def
      | st.abandoned -> pure Nothing
      | depth > macroDepthLimit -> abandon (MacroExpansionTooDeep qn arity)
      | st.remaining <= 0 -> abandon (MacroExpansionTooLarge qn arity)
      | any repeats ctx.macroChain -> failNested ctx (MacroCycle qn arity)
      | otherwise -> case selectClause def.clauses args of
          Nothing -> failNested ctx (NoMatchingMacroClause qn args)
          Just (binds, clause) -> do
            modify' (\s' -> s' {remaining = s'.remaining - 1})
            seed <- freshMacroSeed
            let ctx' = ctx {macroChain = use : ctx.macroChain}
            case instantiateClause seed binds clause of
              Left pe ->
                failNested ctx' (MalformedMacroPrimitive pe.operand pe.received)
              Right goals -> pure (Just (ctx', goals))
  where
    n = unqualifiedText name
    arity = length args
    key = QualifiedIdentifier providerMod n arity
    qn = QualifiedName providerMod n
    size = termsSize args
    depth = case ctx.macroChain of
      (u : _) -> u.depth + 1
      [] -> 1
    use =
      MacroUse
        { definingModule = providerMod,
          name = n,
          arity = arity,
          arguments = args,
          argumentsSize = size,
          site = loc,
          depth = depth
        }
    repeats u =
      macroUseKey u == key
        && u.argumentsSize == size
        && isVariant u.arguments args
    failWith c err = do
      emitErrorIn c (AnnP err loc origin)
      pure Nothing
    abandon err = do
      modify' (\s' -> s' {abandoned = True})
      failWith ctx err
    -- An expansion error in a nested use abandons the rest of the
    -- top-level use too: a macro that branches as it recurses would
    -- otherwise report the same error once per branch.
    failNested c err = do
      unless (null ctx.macroChain) $ modify' (\s' -> s' {abandoned = True})
      failWith c err

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
-- * 'NoResolveQuoted' — inside a @quote(...)@ body. Same name policy as
--   'NoResolve' (functors stay unqualified, declared data constructors
--   still get canonicalized to @Mod:name@), but the undeclared-
--   constructor warning is suppressed because the body is intentionally
--   opaque (see the language reference §The @quote/1@ quoting form).
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

-- | Rename one branch of a disjunction. A branch is a body
-- conjunction, so walk the top-level commas and rename each item the
-- way a rule-body item is renamed (including macro expansion — a
-- disjunct is a goal position too). Mirrors 'renameLambdaBody'; unlike
-- it, a leaf's macro expansion can produce several goals, spliced back
-- in via 'goalsToChain' since this function's own return type is one
-- 'Term'.
renameBodySeq :: RenameCtx -> SourceLoc -> PExpr -> Term -> Rename Term
renameBodySeq ctx loc origin t = case t of
  CompoundTerm (Unqualified ",") [l, r] -> do
    l' <- renameBodySeq ctx loc origin l
    r' <- renameBodySeq ctx loc origin r
    pure (CompoundTerm (Unqualified ",") [l', r'])
  _ -> goalsToChain <$> renameBodyGoal ctx loc origin t

-- | Rename one goal of a rule body or a top-level query: the
-- principal goal position. A macro use expands (recursively — the
-- replacement's own goals are each re-classified the same way, so a
-- macro whose body uses another macro keeps expanding) into zero or
-- more goals; an ordinary goal renames to exactly one, via
-- 'renameTerm'.
renameBodyGoal :: RenameCtx -> SourceLoc -> PExpr -> Term -> Rename [Term]
renameBodyGoal ctx loc origin t = case t of
  CompoundTerm name args
    | Just _ <- aggregateKindOf name (length args) -> do
        -- An aggregate reads the store to decide whether a rule applies,
        -- which is a head position. Refusing it here keeps the failure
        -- from surfacing as "unknown constraint aggregate/4".
        let err = AggregateOutsideHead (unqualifiedText name) (length args)
        emitErrorIn ctx (AnnP err loc origin)
        pure []
    | isGuardFunctor name (length args) -> do
        emitErrorIn ctx (AnnP GuardOutsideAggregateGoal loc origin)
        pure []
    | isPrimitiveName name (length args) ->
        (: []) <$> renameTerm ctx loc origin ResolveTop t
  CompoundTerm (Unqualified "tell") args
    | null args || length args > maxTellArity -> do
        emitErrorIn ctx (AnnP (UnsupportedTellArity (length args)) loc origin)
        pure []
  CompoundTerm (Unqualified "tell") (CompoundTerm (Unqualified n) gargs : _)
    | n `Set.member` tellControlForms -> do
        emitErrorIn ctx (AnnP (TellControlGoal n (length gargs)) loc origin)
        pure []
  CompoundTerm (Unqualified "tell") (CompoundTerm name gargs : extras)
    | isLiteralTellGoal ctx name ->
        renameBodyGoal ctx loc origin (CompoundTerm name (gargs ++ extras))
  CompoundTerm (Unqualified "tell") args ->
    (: []) . CompoundTerm (Unqualified "tell")
      <$> traverse (renameTerm ctx loc origin NoResolve) args
  CompoundTerm name args -> case classifyGoalName ctx name (length args) of
    AmbiguousGoalName ms -> do
      let err = AmbiguousName (unqualifiedText name) (length args) ms
      emitErrorIn ctx (AnnP err loc origin)
      pure []
    IsMacro providerMod -> expandBodyUse ctx loc origin providerMod name args
    IsDeclMacro providerMod -> do
      kindMismatch ctx loc origin providerMod name (length args)
      pure []
    NotAMacro -> (: []) <$> renameTerm ctx loc origin ResolveTop t
  _ -> (: []) <$> renameTerm ctx loc origin ResolveTop t

-- | The body control forms a literal @tell\/N@ goal may not be: each is
-- a goal in its own right, not a constraint (see 'TellControlGoal').
tellControlForms :: Set.Set Text
tellControlForms = Set.fromList [",", ";", "true", "=", "is", "tell"]

-- | Whether the goal argument of a @tell\/N@ goal is written as a
-- literal constraint term — a compound or atom whose head is neither a
-- reserved form (@quote@, @fun@, @'$call'@, …) nor a host call nor a
-- function. Such a @tell(foo(X), Y)@ is the plain goal @foo(X, Y)@, so
-- 'renameBodyGoal' rewrites it to that and it is resolved, checked and
-- compiled like one. Anything else is evaluated and told through the
-- runtime's tellables table.
--
-- The function test is by base name, as 'checkConstructorFunctionAmbiguity'
-- does it, so a head that names a function at /some/ arity stays
-- dynamic. That is the conservative direction: the dynamic path
-- reaches the same constraints, only later.
isLiteralTellGoal :: RenameCtx -> Name -> Bool
isLiteralTellGoal ctx name = case name of
  Unqualified n ->
    not (isReserved n) && not (Map.member n ctx.visibleFunNames)
  Qualified "host" _ -> False
  Qualified m n ->
    m `notElem` Map.findWithDefault [] n ctx.visibleFunNames

-- | Expand a macro use found in body\/query-goal position
-- ('expandMacroUse'), and recurse into 'renameBodyGoal' on each
-- resulting goal so a nested macro use (in a further body position)
-- keeps expanding. A use that fails to expand is dropped, after its
-- error.
expandBodyUse ::
  RenameCtx -> SourceLoc -> PExpr -> Text -> Name -> [Term] -> Rename [Term]
expandBodyUse ctx loc origin providerMod name args =
  expandMacroUse ctx loc origin providerMod name args >>= \case
    Nothing -> pure []
    Just (ctx', goals) ->
      concat <$> traverse (renameBodyGoal ctx' loc origin) goals

-- | @;@ lowers to a tell of @search:alt\/1@, a name the module never
-- writes itself. Require the import that makes it visible, so a module
-- does not silently depend on some /other/ module having imported
-- @library(search)@.
requireSearchImport :: RenameCtx -> SourceLoc -> PExpr -> Rename ()
requireSearchImport ctx loc origin =
  when
    ( ctx.currentModule.name /= searchModuleName
        && searchModuleName `notElem` importedModuleNames ctx
    )
    (emitErrorIn ctx (AnnP DisjunctionWithoutSearch loc origin))

-- | The module that declares the choice-point constraint @;@ compiles
-- to. Matches 'YCHR.Internal.Runtime.Goal.altName'.
searchModuleName :: Text
searchModuleName = "search"

renameTerm ::
  RenameCtx -> SourceLoc -> PExpr -> ResolveMode -> Term -> Rename Term
renameTerm ctx loc origin mode t = case t of
  -- @?/1@ is recognized structurally inside an aggregate goal, and has
  -- no meaning anywhere else: a rule guard uses @|@, a body uses @;@.
  -- Reported even in pattern and quoted positions, where the functor
  -- would otherwise survive as an undeclared-constructor warning.
  CompoundTerm name args | isGuardFunctor name (length args) -> do
    emitErrorIn ctx (AnnP GuardOutsideAggregateGoal loc origin)
    pure t
  -- A construction primitive is evaluated only where it is written in a
  -- macro body, during expansion; one that is still here, in any
  -- position (@quote\/1@ and patterns included), was not.
  CompoundTerm name args
    | isPrimitiveName name (length args) -> do
        primitiveOutsideMacro ctx loc origin name (length args)
        pure t
  -- Special case: @is@ LHS is a pattern (no resolution), RHS is an expression.
  CompoundTerm (Unqualified "is") [lhs, rhs] | isResolving mode -> do
    renamedLhs <- renameTerm ctx loc origin NoResolve lhs
    renamedRhs <- renameTerm ctx loc origin ResolveAll rhs
    pure (CompoundTerm (Unqualified "is") [renamedLhs, renamedRhs])
  -- Disjunction: @(A ; B)@ in a rule body. Both operands are body
  -- conjunctions rather than data, so each is renamed the way a body
  -- item is — 'renameBodySeq' walks the top-level commas the way
  -- 'renameLambdaBody' does for a lambda. Falling through to the
  -- generic compound arm would rename them 'NoResolve' and quietly
  -- turn every goal in the branch into a data term.
  --
  -- 'ResolveAll' is every other evaluating position (a guard, an @is@
  -- right-hand side, a function body), none of which has goals in it.
  -- @;@ is reserved, so without this arm it would fall through to the
  -- generic case and become a silent @';'\/2@ data compound.
  CompoundTerm (Unqualified ";") [l, r]
    | mode == ResolveTop -> do
        requireSearchImport ctx loc origin
        l' <- renameBodySeq ctx loc origin l
        r' <- renameBodySeq ctx loc origin r
        pure (CompoundTerm (Unqualified ";") [l', r'])
    | mode == ResolveAll -> do
        emitErrorIn ctx (AnnP DisjunctionNotInRuleBody loc origin)
        pure t
  -- @tell\/N@ is a goal, and goal positions are handled upstream by
  -- 'renameBodyGoal'; every other evaluating position is an error. The
  -- coverage is 'MacroOutsideGoalPosition''s: quoted and pattern
  -- arguments are data, and stay ordinary @tell@ compounds.
  CompoundTerm (Unqualified "tell") args
    | mode == ResolveAll -> do
        emitErrorIn ctx (AnnP (TellOutsideGoalPosition (length args)) loc origin)
        pure t
  -- Lambda: @fun(params) -> body end@, i.e. @'->'(fun(params), body)@.
  -- A lambda is a value, not data, so this arm fires in every
  -- non-quoted position, patterns included; otherwise a lambda passed
  -- as a constraint argument would get a YCHR-20101 warning for
  -- @fun@\/@->@. The body is always renamed 'ResolveAll', and
  -- 'renameLambdaBody' walks its top-level commas. @quote/1@ opts out.
  CompoundTerm
    (Unqualified "->")
    [ CompoundTerm (Unqualified "fun") params,
      body
      ] | mode /= NoResolveQuoted -> do
      renamedBody <- renameLambdaBody ctx loc origin body
      pure
        ( CompoundTerm
            (Unqualified "->")
            [ CompoundTerm (Unqualified "fun") params,
              renamedBody
            ]
        )
  -- Quoting: @quote(X)@ keeps its argument opaque. Functor names inside
  -- stay unqualified, declared data constructors are silently
  -- canonicalized, and undeclared-data-constructor warnings are
  -- suppressed because the body is intentionally not subject to those
  -- checks (see docs/reference/language.md §The @quote/1@ quoting form).
  -- Fires in any surrounding mode so a nested @quote(...)@ behind a
  -- 'NoResolve' parent (e.g. a body-position constraint argument) is
  -- also covered.
  CompoundTerm (Unqualified "quote") [arg] -> do
    renamedArg <- renameTerm ctx loc origin NoResolveQuoted arg
    pure (CompoundTerm (Unqualified "quote") [renamedArg])
  -- Function reference: @fun name/arity@, i.e. @fun('/'(name, arity))@.
  -- Like a lambda it is a value, not data, so it fires in every
  -- non-quoted position. The name is resolved in 'ResolveTop' mode
  -- (unknown names are errors) and the @fun@ wrapper is stripped, so
  -- later passes see bare @name/arity@. @quote/1@ opts out.
  --
  -- A macro name here is an error ('MacroOutsideGoalPosition'), with
  -- the same guard as the ordinary case just below.
  CompoundTerm
    (Unqualified "fun")
    [ CompoundTerm
        (Unqualified "/")
        [ CompoundTerm (Unqualified fname) [],
          IntTerm farity
          ]
      ]
      | mode /= NoResolveQuoted,
        Just providerMod <-
          isVisibleMacro ctx (Unqualified fname) (fromInteger farity) -> do
          let arity = fromInteger farity
              err = MacroOutsideGoalPosition (QualifiedName providerMod fname) arity
          emitErrorIn ctx (AnnP err loc origin)
          pure t
  CompoundTerm
    (Unqualified "fun")
    [ CompoundTerm
        (Unqualified "/")
        [ CompoundTerm (Unqualified fname) [],
          IntTerm farity
          ]
      ] | mode /= NoResolveQuoted -> do
      resolved <-
        resolveName ResolveTop ctx loc origin (Unqualified fname) (fromInteger farity)
      pure
        ( CompoundTerm
            (Unqualified "/")
            [CompoundTerm (Unqualified (flattenName resolved)) [], IntTerm farity]
        )
  -- 0-arity unqualified compounds (the AST form of bare atoms after
  -- the parser's @Atom t@ rewrite): always lenient under resolution.
  -- A bare atom in body or guard position has the same surface meaning
  -- as a 0-arity data-constructor use, so we force 'ResolveAll' here
  -- (warn but don't error on undeclared) regardless of the surrounding
  -- 'ResolveTop'. Then fall back to data-constructor canonicalization.
  -- A bare 0-arity macro name used in an evaluating position: not a
  -- goal position (that is handled upstream, by 'renameBodyGoal'
  -- before it ever calls 'renameTerm' in 'ResolveTop' mode), so this
  -- can only be reached in 'ResolveAll'.
  CompoundTerm (Unqualified n) []
    | mode == ResolveAll,
      Just providerMod <- isVisibleMacro ctx (Unqualified n) 0 -> do
        let err = MacroOutsideGoalPosition (QualifiedName providerMod n) 0
        emitErrorIn ctx (AnnP err loc origin)
        pure t
  CompoundTerm (Unqualified n) [] -> do
    when (mode /= NoResolveQuoted) $
      checkConstructorFunctionAmbiguity ctx loc origin n
    resolved <- case mode of
      NoResolve -> do
        warnUnknownDataCon ctx loc origin n 0
        case visibleProviders ctx n 0 of
          ms@(_ : _ : _) ->
            emitErrorIn ctx (AnnP (AmbiguousName n 0 ms) loc origin)
          _ -> pure ()
        pure (Unqualified n)
      NoResolveQuoted ->
        pure (Unqualified n)
      _ -> resolveName ResolveAll ctx loc origin (Unqualified n) 0
    case resolved of
      Qualified _ _ -> pure (CompoundTerm resolved [])
      Unqualified _ -> do
        case mode of
          NoResolveQuoted -> pure ()
          _ ->
            when (null (visibleProviders ctx n 0)) $
              checkAmbiguousDataCon ctx loc origin n 0
        case canonicalizeDataCon ctx n 0 of
          Just qn -> pure (CompoundTerm qn [])
          Nothing -> pure (CompoundTerm (Unqualified n) [])
  -- Same "elsewhere" check as the 0-arity case above, for a macro
  -- name used at a nonzero arity in an evaluating position.
  CompoundTerm name args
    | mode == ResolveAll,
      Just providerMod <- isVisibleMacro ctx name (length args) -> do
        let qn = QualifiedName providerMod (unqualifiedText name)
            err = MacroOutsideGoalPosition qn (length args)
        emitErrorIn ctx (AnnP err loc origin)
        pure t
  CompoundTerm name args -> do
    let childMode = case mode of
          NoResolve -> NoResolve
          NoResolveQuoted -> NoResolveQuoted
          ResolveTop -> NoResolve
          ResolveAll -> ResolveAll
    -- Which namespace a bare compound head belongs to is decided
    -- below, differently per mode. Ask first whether the name even
    -- has an unambiguous answer.
    case name of
      Unqualified n | mode /= NoResolveQuoted -> do
        checkConstructorFunctionAmbiguity ctx loc origin n
      _ -> pure ()
    renamedArgs <- traverse (renameTerm ctx loc origin childMode) args
    newName <- case mode of
      NoResolve -> do
        case name of
          -- Three legs by what the function/constraint namespace says:
          --   []      — no visible callable; this is a pattern-style
          --             use of an unqualified name. Run the data-
          --             constructor checks ('warnUnknownDataCon' for
          --             the bare 'is this declared anywhere' question,
          --             'checkAmbiguousDataCon' for the cross-module
          --             data-constructor ambiguity question).
          --   [_]     — exactly one callable; 'Resolve.termToExpr' will
          --             canonicalize this to a 'CallExpr' for tell-side
          --             argument evaluation, so it is not a misspelled
          --             data constructor. Any data-constructor ambiguity
          --             with the same name is moot for this use.
          --   _:_:_   — multiple callables and 'Resolve.termToExpr' has
          --             no way to pick one (the multi-provider entry
          --             silently falls through to 'CtorExpr', see
          --             'Resolve.hs' on the @CompoundTerm Unqualified@
          --             arm). Mirror the multi-provider arm of
          --             'resolveName' (which 'ResolveTop'/'ResolveAll'
          --             positions already go through) so that pattern-
          --             position uses get the same 'AmbiguousName'
          --             diagnostic instead of a silent downstream
          --             failure.
          Unqualified n ->
            case visibleProviders ctx n (length args) of
              [] -> do
                warnUnknownDataCon ctx loc origin n (length args)
                checkAmbiguousDataCon ctx loc origin n (length args)
              [_] -> pure ()
              ms ->
                emitErrorIn ctx (AnnP (AmbiguousName n (length args) ms) loc origin)
          -- Qualified references in pattern position (head args,
          -- body-tell args) get the same visibility check as in
          -- resolving positions; the parser can't tell a constructor,
          -- a function/constraint, or a type-tag apart at the term
          -- level, so any of those visibility leg passes.
          Qualified m n -> validateQualified ctx loc origin m n (length args)
        pure (canonicalizeData ctx name (length args))
      NoResolveQuoted ->
        -- Inside a 'quote/1' quote the body is fully opaque: no
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
              emitErrorIn ctx (AnnP (UnknownName n arity) loc origin)
              pure (Unqualified n)
            else do
              warnUnknownDataCon ctx loc origin n arity
              pure (Unqualified n)
        ms -> do
          emitErrorIn ctx (AnnP (AmbiguousName n arity ms) loc origin)
          pure (Unqualified n)
resolveName _ ctx loc origin name@(Qualified m n) arity = do
  validateQualified ctx loc origin m n arity
  pure name

-- | Verify that a qualified reference @M:n/a@ is in scope as a
-- /value-level/ identifier: function, constraint, or data
-- constructor. Types are intentionally not accepted — they live in a
-- separate namespace and cannot appear in value positions. Users who
-- need a qualified atom as opaque data (e.g. the typechecker's
-- type-name tags) must wrap it with @quote/1@, which switches the
-- renamer into 'NoResolveQuoted' mode and skips this check entirely.
-- The @host@ pseudo-module is exempt (host calls are external).
--
-- For a miss, the diagnostic pinpoints the actual cause, first match
-- wins:
--
--   * 'UnknownModule' (YCHR-20015) iff no module named @M@ exists;
--   * 'ModuleNotImported' (YCHR-20014) iff @M@ exists but the current
--     module never imports it (qualification does not bypass the
--     import requirement). The current module itself is exempt: it
--     never imports itself, yet its own declarations are in scope;
--   * constructor-flavored ('NonExportedConstructor', YCHR-20010) iff
--     @M@ declares @(n, arity)@ as a constructor anywhere — the user
--     named a real but hidden ctor;
--   * 'NotExportedByModule' (YCHR-20009) otherwise — @M@ is imported
--     but does not export @(n, arity)@ (or a restricted import list
--     excludes it).
--
-- Callers return the 'Qualified' name unchanged so traversal can continue.
validateQualified ::
  RenameCtx -> SourceLoc -> PExpr -> Text -> Text -> Int -> Rename ()
validateQualified ctx loc origin m n arity
  | m == "host" = pure ()
  | m `elem` visibleProviders ctx n arity = pure ()
  | m `notElem` ctx.allModuleNames =
      emitErrorIn ctx (AnnP (UnknownModule m) loc origin)
  | m /= ctx.currentModule.name && m `notElem` importedModuleNames ctx =
      emitErrorIn ctx (AnnP (ModuleNotImported m n arity) loc origin)
  | m `elem` Map.findWithDefault [] key ctx.dataConProviders = pure ()
  | m `elem` Map.findWithDefault [] key ctx.allDataConProviders =
      emitErrorIn ctx (AnnP (NonExportedConstructor m n arity) loc origin)
  | otherwise =
      emitErrorIn ctx (AnnP (NotExportedByModule m n arity) loc origin)
  where
    key = UnqualifiedIdentifier n arity

-- | Every module the current module imports. Used to decide whether a
-- qualified reference's target module is in scope at all (distinct from
-- whether it exports the referenced name).
importedModuleNames :: RenameCtx -> [Text]
importedModuleNames ctx = map (.importModule) ctx.moduleImports

-- | All modules that can provide @(name, arity)@ to the current module:
-- the current module itself if it declares the name, plus every imported
-- module that /exports/ it.
visibleProviders :: RenameCtx -> Text -> Int -> [Text]
visibleProviders ctx n arity =
  let ownProviders =
        filter
          (== ctx.currentModule.name)
          (lookupDecl (UnqualifiedIdentifier n arity) ctx.declEnv)
      importProviders =
        filter
          ( \mn ->
              any
                ( \imp ->
                    imp.importModule == mn
                      && importListPermits n arity imp.importItems
                )
                ctx.moduleImports
          )
          (lookupExport (UnqualifiedIdentifier n arity) ctx.exportEnv)
   in -- Deduplicate: multiple declarations with the same name/arity in
      -- one module (e.g., overloaded function signatures) are not ambiguous.
      nub (ownProviders ++ importProviders)

-- | Every module that makes @(n, arity)@ visible as a macro to the
-- current module: the module itself if it defines the macro, plus
-- every imported module that exports it and whose import list
-- permits it. Exact mirror of 'visibleProviders' for the macro
-- namespace.
visibleMacroProviders :: RenameCtx -> MacroKind -> Text -> Int -> [Text]
visibleMacroProviders ctx kind n arity =
  let ownProviders =
        filter
          (== ctx.currentModule.name)
          (lookupDecl (UnqualifiedIdentifier n arity) ctx.macroDeclEnv)
      importProviders =
        filter
          ( \mn ->
              any
                ( \imp ->
                    imp.importModule == mn
                      && importListPermitsMacro n arity imp.importItems
                )
                ctx.moduleImports
          )
          (lookupExport (UnqualifiedIdentifier n arity) ctx.macroExportEnv)
   in filter (isKind kind n arity) (nub (ownProviders ++ importProviders))
  where
    -- Filter by kind: a goal macro and a declaration macro with the same
    -- key never clash.
    isKind k nm a mn = case Map.lookup (QualifiedIdentifier mn nm a) ctx.macroDefTable of
      Just d -> d.kind == k
      Nothing -> False

-- | The classification of an unqualified or qualified name at a /goal
-- position/ (a rule head conjunct, a rule-body or query goal): either
-- not a macro at all (resolve it normally), a
-- macro provided by exactly one module (expand it), or ambiguous
-- because more than one visible provider answers to the name —
-- whether several ordinary providers, several macro providers, or one
-- of each. See 'isVisibleMacro' for the simpler check used outside
-- goal positions, which does not need to weigh macro providers against
-- ordinary ones.
data GoalNameClass
  = NotAMacro
  | AmbiguousGoalName [Text]
  | IsMacro Text
  | -- | The name matches nothing visible in a goal position, but does
    -- match a declaration macro of the given module
    -- ('MacroKindMismatch').
    IsDeclMacro Text

-- | Classify a goal-position name. Only called for 'ResolveTop'
-- positions.
classifyGoalName :: RenameCtx -> Name -> Int -> GoalNameClass
classifyGoalName ctx (Unqualified n) arity =
  let ords = visibleProviders ctx n arity
      macs = visibleMacroProviders ctx GoalMacro n arity
   in case (ords, macs) of
        ([], [])
          | (d : _) <- visibleMacroProviders ctx DeclMacro n arity -> IsDeclMacro d
          | otherwise -> NotAMacro
        ([], [m]) -> IsMacro m
        ([_], []) -> NotAMacro
        _ -> AmbiguousGoalName (nub (ords ++ macs))
classifyGoalName ctx (Qualified m n) arity
  | m `elem` visibleMacroProviders ctx GoalMacro n arity = IsMacro m
  | m `notElem` visibleProviders ctx n arity,
    m `elem` visibleMacroProviders ctx DeclMacro n arity =
      IsDeclMacro m
  | otherwise = NotAMacro

-- | Whether @(n, arity)@ is visible as a macro at all, regardless of
-- any competing ordinary (constraint\/function) binding. Used outside
-- goal positions — guards, @is@ right-hand sides, lambda bodies,
-- function equations, @fun name\/arity@ references — where a macro
-- name is simply not applicable (spec: "Elsewhere a macro name is an
-- error"), so there is nothing to disambiguate against an ordinary
-- binding the way 'classifyGoalName' does.
isVisibleMacro :: RenameCtx -> Name -> Int -> Maybe Text
isVisibleMacro ctx (Unqualified n) arity =
  case visibleMacroProviders ctx GoalMacro n arity of
    (m : _) -> Just m
    [] -> Nothing
isVisibleMacro ctx (Qualified m n) arity
  | m `elem` visibleMacroProviders ctx GoalMacro n arity = Just m
  | otherwise = Nothing

-- | The modules that make each /function/ name visible to @self@,
-- keyed by base name with the arity dropped.
--
-- Same visibility legs as 'visibleProviders' — the module's own
-- declarations, plus imported modules that export the name and whose
-- import list permits it — but restricted to 'FunctionDecl' and
-- collapsed to a name-only key. Both restrictions matter for its one
-- caller, 'checkConstructorFunctionAmbiguity': a constructor and a
-- function collide by name whatever their arities, and constraints
-- are out of scope because 'Resolve.termToExpr' never resolves a
-- compound to a constraint call, so a constraint name never competes
-- with a constructor inside an expression.
--
-- Mirrors 'YCHR.Internal.Resolve.buildFunctionVisibility', which
-- answers the same visibility question for 'Resolve.termToExpr' but
-- keyed by @(name, arity)@ and valued with 'QualifiedName's.
buildVisibleFunctionNames :: [CollectedModule] -> CollectedModule -> Map Text [Text]
buildVisibleFunctionNames mods self =
  Map.fromListWith
    (\a b -> nub (a ++ b))
    [ (fd.name, [provider.name])
    | provider <- mods,
      Ann d _ <- provider.decls,
      FunctionDecl fd <- [d],
      visibleTo provider fd
    ]
  where
    imports = [imp | AnnP imp _ _ <- self.imports]

    visibleTo provider fd
      | provider.name == self.name = True
      | otherwise = importPermits provider fd && exportPermits provider fd

    importPermits provider fd =
      any
        ( \imp ->
            imp.importModule == provider.name
              && importListPermits fd.name fd.arity imp.importItems
        )
        imports

    exportPermits provider fd = case provider.exports of
      Nothing -> True
      Just annExports -> importListPermits fd.name fd.arity (Just annExports.node)

-- | Check whether a name/arity is permitted by an import list.
-- 'Nothing' means import everything; 'Just' restricts to listed items.
importListPermits :: Text -> Int -> Maybe [Declaration] -> Bool
importListPermits _ _ Nothing = True
importListPermits n arity (Just decls) = any match decls
  where
    match (ConstraintDecl ConstraintDeclBody {name = dn, arity = da}) =
      dn == n && da == arity
    match (FunctionDecl FunctionDeclBody {name = dn, arity = da}) = dn == n && da == arity
    match _ = False

-- | Check whether a type name/arity is permitted by an import list.
importListPermitsType :: Text -> Int -> Maybe [Declaration] -> Bool
importListPermitsType _ _ Nothing = True
importListPermitsType n arity (Just decls) = any match decls
  where
    match (TypeExportDecl TypeExportDeclBody {name = tn, arity = ta}) =
      tn == n && ta == arity
    match _ = False

-- | The set of constructor names a single import-list entry permits for
-- type @n/a@. The fallback is the supplied @allCons@ — used when no
-- constructor clause is present (i.e. the import is @type(n/a)@ rather
-- than @type(n/a, [...])@).
importListPermitsCons ::
  Text -> Int -> Set.Set Text -> Maybe [Declaration] -> Set.Set Text
importListPermitsCons _ _ allCons Nothing = allCons
importListPermitsCons n arity allCons (Just decls) =
  case matching of
    (Nothing : _) -> allCons
    (Just xs : _) -> Set.fromList xs
    [] -> Set.empty
  where
    matching =
      [cs | TypeExportDecl (TypeExportDeclBody tn ta cs) <- decls, tn == n, ta == arity]

-- | For each type visible to the current module, the set of constructor
-- names also visible. Locally declared types contribute every declared
-- constructor; imported types contribute @exporterAllowlist ∩
-- importerAllowlist@ where each side defaults to "all constructors" when
-- its @type(...)@ clause has no constructor list. A type with an empty
-- constructor set still appears in the map: the type itself remains
-- visible (type-level visibility is governed independently by
-- 'resolveTypeName'), only its constructors are hidden.
visibleDataCons :: [CollectedModule] -> RenameCtx -> Map DeclaredType (Set.Set Text)
visibleDataCons mods ctx =
  Map.fromList
    [ entry
    | m <- mods,
      Ann td _ <- m.typeDecls,
      Just entry <- [entryFor m td]
    ]
  where
    entryFor m td =
      let n = unqualifiedText td.name
          a = length td.typeVars
          key = DeclaredType m.name n a
          allCons =
            Set.fromList [unqualifiedText dc.conName | dc <- typeConstructors td]
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
        case [ cs
             | TypeExportDecl (TypeExportDeclBody tn ta cs) <- exports,
               tn == n,
               ta == a
             ] of
          (Nothing : _) -> Just allCons
          (Just xs : _) -> Just (Set.fromList xs)
          [] -> Nothing

    importerAllowance mn n a allCons =
      let relevant = [imp.importItems | imp <- ctx.moduleImports, imp.importModule == mn]
       in if null relevant
            then Nothing
            else
              Just
                ( Set.unions
                    [importListPermitsCons n a allCons il | il <- relevant]
                )

-- | Check an unresolved name against data-constructor declarations.
-- If found with matching arity: silent. If found with wrong arity: warning.
-- If not found at all: warning. A type-constructor name used in term
-- position (e.g. @set@ for an opaque type, or @list@ for an algebraic
-- one) is not a declared data constructor, so it falls through to the
-- 'UndeclaredDataConstructor' warning like any other unknown functor.
warnUnknownDataCon :: RenameCtx -> SourceLoc -> PExpr -> Text -> Int -> Rename ()
warnUnknownDataCon ctx loc origin n arity =
  case Map.lookup n ctx.dataConEnv of
    Just arities
      | arity `elem` arities -> pure ()
      | otherwise ->
          emitWarningIn ctx (AnnP (DataConstructorArityMismatch n arity) loc origin)
    Nothing -> emitWarningIn ctx (AnnP (UndeclaredDataConstructor n) loc origin)

-- ---------------------------------------------------------------------------
-- Type definition renaming
-- ---------------------------------------------------------------------------

-- | Rename a type definition: qualify the type name and constructor names
-- with the declaring module, and resolve type references in constructor
-- arguments.
--
-- Pure (not in 'Rename'): type renaming reports nothing. Unknown types
-- (e.g. the built-in @int@) stay 'Unqualified'.
renameTypeDefinition :: RenameCtx -> TypeDefinition -> TypeDefinition
renameTypeDefinition ctx td =
  TypeDefinition
    { name = Qualified ctx.currentModule.name (unqualifiedText td.name),
      typeVars = td.typeVars,
      kind = case td.kind of
        Opaque -> Opaque
        Algebraic cs -> Algebraic (map (renameDataConstructor ctx) cs),
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
renameDeclaration ctx loc (ConstraintDecl cd) = do
  requiring' <- traverse (traverse (renameBoundSig ctx loc)) cd.requiring
  pure
    ( ConstraintDecl
        ConstraintDeclBody
          { name = cd.name,
            arity = cd.arity,
            argTypes = fmap (map (renameTypeExpr ctx)) cd.argTypes,
            requiring = requiring'
          }
    )
renameDeclaration ctx loc (FunctionDecl fd) = do
  requiring' <- traverse (traverse (renameBoundSig ctx loc)) fd.requiring
  pure
    ( FunctionDecl
        FunctionDeclBody
          { name = fd.name,
            arity = fd.arity,
            argTypes = fmap (map (renameTypeExpr ctx)) fd.argTypes,
            returnType = fmap (renameTypeExpr ctx) fd.returnType,
            isOpen = fd.isOpen,
            kind = fd.kind,
            requiring = requiring',
            refining = fmap (renameTypeExpr ctx) fd.refining
          }
    )
renameDeclaration ctx loc (ExtendClassTypeDecl ed) = do
  resolved <- resolveName ResolveTop ctx loc (Atom ed.name) (Unqualified ed.name) ed.arity
  pure
    ( ExtendClassTypeDecl
        ExtendClassTypeDeclBody
          { name = ed.name,
            arity = ed.arity,
            argTypes = fmap (map (renameTypeExpr ctx)) ed.argTypes,
            returnType = fmap (renameTypeExpr ctx) ed.returnType,
            target = Just resolved
          }
    )
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
                emitErrorIn ctx (AnnP (AmbiguousName n bs.arity ms) bs.loc origin)
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
          (lookupDecl (UnqualifiedIdentifier n arity) ctx.typeDeclEnv)
      matches = ownProviders ++ typeImportProviders ctx n arity
   in case matches of
        [m] -> Qualified m n
        _ -> Unqualified n

-- | Import-visible providers of type @(n, arity)@: modules the current
-- module imports whose import list permits the type and which export
-- it.
typeImportProviders :: RenameCtx -> Text -> Int -> [Text]
typeImportProviders ctx n arity =
  filter
    ( \mn ->
        any
          ( \imp ->
              imp.importModule == mn
                && importListPermitsType n arity imp.importItems
          )
          ctx.moduleImports
    )
    (lookupExport (UnqualifiedIdentifier n arity) ctx.typeExportEnv)

-- | Type names the grammar wires in: the base types plus the
-- function-type syntax. Declaring any of them as a user type would
-- silently rewrite every use in the module to a nominal user type.
reservedTypeNames :: Set.Set Text
reservedTypeNames = Set.fromList ["int", "float", "string", "any", "fun", "->"]

-- | Reject type declarations whose name collides with a reserved type
-- name, an earlier declaration in the same module, or a type visible
-- through an import (spec §Type Definitions: the declared name "must
-- not collide with a base/reserved type name or another visible
-- type"). Without the check every use of a colliding name would
-- degrade with no diagnostic: 'resolveTypeName' falls back to
-- 'Unqualified' whenever the providers are not unique.
validateTypeDecls :: RenameCtx -> Rename ()
validateTypeDecls ctx = foldM_ step Set.empty ctx.currentModule.typeDecls
  where
    step seen (Ann td _) = do
      let n = unqualifiedText td.name
          arity = length td.typeVars
          origin = Atom n
      when (n `Set.member` reservedTypeNames) $
        emitError (AnnP (ReservedTypeName n arity) td.loc origin)
      when (UnqualifiedIdentifier n arity `Set.member` seen) $
        emitError (AnnP (DuplicateTypeDeclaration n arity) td.loc origin)
      -- Module identity is name-based, so a module that shadows a
      -- same-named library (e.g. a module `strings` importing
      -- `library(strings)`) is indistinguishable from itself here;
      -- skip providers carrying the current module's own name.
      case filter (/= ctx.currentModule.name) (typeImportProviders ctx n arity) of
        (pm : _) -> emitError (AnnP (TypeShadowsImport n arity pm) td.loc origin)
        [] -> pure ()
      pure (Set.insert (UnqualifiedIdentifier n arity) seen)

-- ---------------------------------------------------------------------------
-- Query renaming
-- ---------------------------------------------------------------------------

-- | The renaming environment for query terms: the whole-program
-- name environment as seen from a synthetic @\<query\>@ module that
-- imports every loaded module.
--
-- Building it walks every module (declarations, exports, type
-- declarations, data constructors), so it is built once per compiled
-- program and carried on
-- 'YCHR.Internal.Compile.Pipeline.CompiledProgram' rather than
-- rebuilt per query. Opaque on purpose: the wrapped 'RenameCtx' is an
-- implementation detail of this module.
newtype QueryRenameEnv = QueryRenameEnv RenameCtx

-- | Build the query-time renaming environment for a program's modules.
buildQueryRenameEnv :: [CollectedModule] -> QueryRenameEnv
buildQueryRenameEnv mods =
  let queryMod =
        CollectedModule
          { name = "<query>",
            nameLoc = dummyLoc,
            imports = [noAnnP (CollectedImport m.name Nothing) | m <- mods],
            decls = [],
            extensionTypes = [],
            typeDecls = [],
            rules = [],
            equations = [],
            extensions = [],
            classExtensions = [],
            inlines = [],
            constraintUses = [],
            macros = [],
            exports = Nothing
          }
      ctx0 =
        RenameCtx
          { declEnv = buildDeclEnv mods,
            exportEnv = buildExportEnv mods,
            dataConEnv = Map.empty,
            dataConProviders = Map.empty,
            allDataConProviders = buildAllDataConProviders mods,
            visibleFunNames = buildVisibleFunctionNames mods queryMod,
            typeDeclEnv = buildTypeDeclEnv mods,
            typeExportEnv = buildTypeExportEnv mods,
            operatorExports = Map.empty,
            currentTrailingLoc = Nothing,
            allModuleNames = map (.name) mods,
            currentModule = queryMod,
            moduleImports = [CollectedImport m.name Nothing | m <- mods],
            macroDeclEnv = buildMacroDeclEnv mods,
            macroExportEnv = buildMacroExportEnv mods,
            macroDefTable = buildMacroDefTable mods,
            macroChain = [],
            declChain = []
          }
      visible = visibleDataCons mods ctx0
   in QueryRenameEnv
        ctx0
          { dataConEnv = buildDataConEnv visible mods,
            dataConProviders = buildDataConProviders visible mods
          }

-- | Like 'renameQueryGoalsWith' but uses 'NoResolve' mode — appropriate
-- for the argument terms of a single goal constraint, where each
-- term is data (constructors / atoms / variables) rather than a
-- callable. Canonicalizes bare data-constructor references the same
-- way the renamer does for head-pattern arguments.
renameQueryArgsWith ::
  QueryRenameEnv ->
  [Term] ->
  Either
    [Diagnostic RenameError]
    ( [Term],
      [Diagnostic RenameWarning]
    )
renameQueryArgsWith env args = renameQueryTerms env NoResolve args

-- | Rename a list of query goal terms using all modules as the visible
-- scope. Each term is renamed at 'ResolveTop' level (same as rule bodies).
-- Returns 'Left' if any rename errors occur.
renameQueryGoalsWith ::
  QueryRenameEnv ->
  [Term] ->
  Either
    [Diagnostic RenameError]
    ( [Term],
      [Diagnostic RenameWarning]
    )
renameQueryGoalsWith env goals = renameQueryTerms env ResolveTop goals

-- | Location reported for every diagnostic raised while renaming a query
-- goal or argument. Queries have no file of their own, so they are
-- anchored at @\<query\>@ rather than the renamer's @\<generated\>@
-- placeholder.
queryTermLoc :: SourceLoc
queryTermLoc = SourceLoc "<query>" 1 1

renameQueryTerms ::
  QueryRenameEnv ->
  ResolveMode ->
  [Term] ->
  Either [Diagnostic RenameError] ([Term], [Diagnostic RenameWarning])
renameQueryTerms (QueryRenameEnv ctx) mode terms =
  let renameOne t = case mode of
        -- Query goals are a goal position: a macro use expands, same
        -- as a rule-body goal.
        ResolveTop -> renameBodyGoal ctx queryTermLoc (termToPExpr t) t
        _ -> (: []) <$> renameTerm ctx queryTermLoc (termToPExpr t) mode t
      -- A query whose goals all expand to nothing is @true@.
      finish = case mode of
        ResolveTop | not (null terms) -> orTrue
        _ -> id
      ((renamedLists, warnings), errs) =
        runWriter (runWriterT (evalStateT (traverse renameOne terms) initialMacroState))
   in if null errs then Right (finish (concat renamedLists), warnings) else Left errs

-- | Expand a single goal constraint if its name names a macro,
-- repeating until the head is no longer a macro (so a macro that
-- expands to exactly one further macro use keeps unfolding). Returns
-- the flattened list of resulting goal terms, unrenamed otherwise — a
-- plain, non-macro constraint comes back as its own singleton list,
-- completely unchanged.
--
-- Used by the single-goal entry points ('YCHR.Run.prepareGoalTerm' and
-- callers), which parse a goal as one 'Constraint' and rename only its
-- arguments (never going through 'renameQueryGoalsWith', the
-- conjunction path above). A macro that expands to more than one goal
-- cannot be represented as a single 'Constraint'; the caller is
-- expected to reject that case (see
-- 'YCHR.Internal.Compile.Pipeline.GoalRejection').
expandQueryGoalWith ::
  QueryRenameEnv ->
  Constraint ->
  Either [Diagnostic RenameError] [Term]
expandQueryGoalWith (QueryRenameEnv ctx0) (Constraint cname0 cargs0) =
  let ((result, _warnings), errs) =
        runWriter (runWriterT (evalStateT (go ctx0 cname0 cargs0) initialMacroState))
   in if null errs then Right result else Left errs
  where
    -- Structural expansion only: no 'renameTerm', and no diagnostics
    -- beyond the macro ones below. The caller renames the single goal
    -- that comes back itself (name via its own export lookup,
    -- arguments via 'renameQueryArgsWith'), so a goal untouched by
    -- macros is renamed once, not twice.
    go :: RenameCtx -> Name -> [Term] -> Rename [Term]
    go ctx cname cargs
      | isPrimitiveName cname (length cargs) = do
          primitiveOutsideMacro ctx queryTermLoc (Atom "") cname (length cargs)
          pure []
      | otherwise = case classifyGoalName ctx cname (length cargs) of
          AmbiguousGoalName ms -> do
            let err = AmbiguousName (unqualifiedText cname) (length cargs) ms
            emitErrorIn ctx (AnnP err queryTermLoc (Atom ""))
            pure []
          IsMacro providerMod ->
            expandMacroUse ctx queryTermLoc (Atom "") providerMod cname cargs >>= \case
              Nothing -> pure []
              Just (ctx', goals) -> concat <$> traverse (expandGoalTerm ctx') goals
          IsDeclMacro providerMod -> do
            kindMismatch ctx queryTermLoc (Atom "") providerMod cname (length cargs)
            pure []
          NotAMacro -> pure [CompoundTerm cname cargs]
    expandGoalTerm ctx t = case t of
      CompoundTerm nm as -> go ctx nm as
      _ -> pure [t]

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
'UndeclaredDataConstructor' warning: at the AST level there is no
separate atom form — the parser already represents bare names as
@CompoundTerm (Unqualified n) []@, so the renamer treats them
uniformly as zero-arity data constructors. If the name is instead
declared as a zero-arity constraint or function, the dedicated 0-arity
arm in 'renameTerm' canonicalizes it to the qualified form before the
warning path runs.
--------------------------------------------------------------------------- -}
