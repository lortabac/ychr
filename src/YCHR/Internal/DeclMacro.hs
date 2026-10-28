{-# LANGUAGE OverloadedStrings #-}

-- |
-- Module      : YCHR.Internal.DeclMacro
-- Description : Declaration-macro expansion (@:- macro_decls@).
--
-- A declaration macro expands to top-level clauses. It's used as a
-- directive: @:- Name(Args).@
--
-- Expansion works on the raw p-expr terms, before conversion to the
-- AST. Everything after that only sees the expanded clauses. This works
-- because an expansion can't add imports or macros
-- ('MacroDeclsForbiddenClause'), so we know every module's imports and
-- macros up front.
--
-- Matching, instantiation, primitives and limits are shared with goal
-- macros ("YCHR.Internal.Rename.Macro"). Generated clauses are turned
-- back into p-exprs ('termToPExpr') and get the location of the
-- outermost use.
--
-- See [the macro reference](../../../docs/reference/macros.md).
module YCHR.Internal.DeclMacro
  ( -- * Errors
    DeclMacroError (..),

    -- * Visibility
    MacroScope,
    scopeFromModule,
    scopeFromTerms,
    scopeName,
    DeclMacroEnv,
    buildDeclMacroEnv,

    -- * Expansion
    ExpandedModule (..),
    expandAndConvert,
  )
where

import Control.Monad (unless)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.State.Strict (StateT, evalStateT, gets, modify')
import Control.Monad.Trans.Writer.CPS (Writer, runWriter, tell)
import Data.List (nub)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import YCHR.Internal.Collected (CollectedImport (..), collectedImport)
import YCHR.Internal.Diagnostic (Diagnostic (..))
import YCHR.Internal.PExpr (PExpr (..))
import YCHR.Internal.Parsed
import YCHR.Internal.Parser
  ( ChainedError (..),
    ParseValidationError (..),
    SourceItem (..),
    convertSourceItems,
    convertTerm,
    isBuiltinDirective,
    scanModuleTerms,
  )
import YCHR.Internal.Pretty (termToPExpr)
import YCHR.Internal.Rename (RenameError (..), useFailureError)
import YCHR.Internal.Rename.Macro
  ( MacroState (..),
    MacroUse (..),
    UseResult (..),
    expandStep,
    freshBudget,
    initialMacroState,
    instantiateBody,
    newMacroUse,
    renderExpansionChain,
  )
import YCHR.Internal.Rename.Types (importListPermits, macroEntry)
import YCHR.Internal.Types
  ( QualifiedIdentifier (..),
    QualifiedName (..),
    UnqualifiedIdentifier (..),
  )

-- ---------------------------------------------------------------------------
-- Errors
-- ---------------------------------------------------------------------------

-- | Declaration-macro errors.
data DeclMacroError
  = -- | Forbidden clause in an expansion (or in a body as written). The
    -- text is the form: @module@, @use_module@, @macro@, @macro_decls@
    -- or @--->@.
    MacroDeclsForbiddenClause Text
  | -- | Directive that isn't built in and isn't a visible macro. Name
    -- and arity.
    UnknownDirective Text Int
  | -- | A renamer error hit during expansion (cycle, no matching
    -- clause, limits, bad primitive, kind mismatch, bad qualified
    -- name). Keeps the renamer's code.
    DeclMacroRenameError RenameError
  | -- | A generated clause is malformed. Comes from conversion, with
    -- the expansion chain.
    DeclMacroParseError ParseValidationError
  deriving (Eq, Show)

-- ---------------------------------------------------------------------------
-- Visibility
-- ---------------------------------------------------------------------------

-- | What expansion needs about a module: name, imports, exports and
-- macros (both kinds).
data MacroScope = MacroScope
  { name :: Text,
    imports :: [CollectedImport],
    exports :: Maybe [Declaration],
    macros :: [AnnP MacroDef]
  }

-- | Scope of a converted module (a library). Adds the implicit prelude
-- import.
scopeFromModule :: Module -> MacroScope
scopeFromModule m =
  MacroScope
    { name = m.name,
      imports =
        [CollectedImport "prelude" Nothing | m.name /= "prelude"]
          ++ [collectedImport i | AnnP i _ _ <- m.imports],
      exports = (.node) <$> m.exports,
      macros = m.macros
    }

-- | Scope of a module still in term form. The first argument is the
-- name to use if there's no @:- module@.
scopeFromTerms :: Text -> [Ann PExpr] -> MacroScope
scopeFromTerms defaultName terms = scopeFromModule (scanModuleTerms defaultName terms)

-- | Module name of a scope. A function, not an exported field, so
-- importing it doesn't clash with 'Module''s @name@ / @imports@.
scopeName :: MacroScope -> Text
scopeName s = s.name

-- | Macros of all modules, indexed for lookup.
data DeclMacroEnv = DeclMacroEnv
  { scopes :: Map Text MacroScope,
    -- | Definitions by module, name and arity. First one wins; the
    -- renamer reports duplicates.
    definitions :: Map QualifiedIdentifier MacroDef,
    -- | Exported macros: all of them if there's no export list, else
    -- the @macro(Name\/Arity)@ items.
    exported :: Set QualifiedIdentifier
  }

-- | Index all scopes.
buildDeclMacroEnv :: [MacroScope] -> DeclMacroEnv
buildDeclMacroEnv allScopes =
  DeclMacroEnv
    { scopes = Map.fromList [(s.name, s) | s <- allScopes],
      definitions =
        Map.fromListWith
          (\_new old -> old)
          [ (QualifiedIdentifier s.name d.node.name d.node.arity, d.node)
          | s <- allScopes,
            d <- s.macros
          ],
      exported =
        Set.fromList
          [ QualifiedIdentifier s.name k.localName k.arity
          | s <- allScopes,
            k <- exportedMacros s
          ]
    }
  where
    exportedMacros s =
      let own = [UnqualifiedIdentifier d.node.name d.node.arity | d <- s.macros]
       in case s.exports of
            Nothing -> own
            Just items ->
              [ k
              | MacroExportDecl meb <- items,
                let k = UnqualifiedIdentifier meb.name meb.arity,
                k `elem` own
              ]

-- | Modules that make macro @n\/a@ of the given kind visible: the
-- module itself, plus imports that export it. Same as the renamer's
-- @visibleMacroProviders@.
providers :: DeclMacroEnv -> MacroScope -> MacroKind -> UnqualifiedIdentifier -> [Text]
providers env scope kind (UnqualifiedIdentifier n a) =
  filter
    ofKind
    ( nub
        ( [scope.name | Map.member (QualifiedIdentifier scope.name n a) env.definitions]
            ++ [ mn
               | CollectedImport mn il <- scope.imports,
                 Set.member (QualifiedIdentifier mn n a) env.exported,
                 importListPermits macroEntry (UnqualifiedIdentifier n a) il
               ]
        )
    )
  where
    ofKind mn = case Map.lookup (QualifiedIdentifier mn n a) env.definitions of
      Just d -> d.kind == kind
      Nothing -> False

-- ---------------------------------------------------------------------------
-- Expansion
-- ---------------------------------------------------------------------------

-- | Where an expansion happens: the macro tables, the module, where the
-- outermost directive is, and the chain of uses in progress (empty at
-- top level).
data ExpandCtx = ExpandCtx
  { env :: DeclMacroEnv,
    scope :: MacroScope,
    loc :: SourceLoc,
    chain :: [MacroUse]
  }

type Expand = StateT MacroState (Writer [Diagnostic DeclMacroError])

-- | A module after expansion and conversion.
data ExpandedModule = ExpandedModule
  { converted :: Module,
    -- | Conversion errors in clauses the user wrote.
    parseErrors :: [AnnP ParseValidationError],
    -- | Expansion errors, definition checks, and conversion errors in
    -- generated clauses (with their chain).
    expansionErrors :: [Diagnostic DeclMacroError],
    -- | The clauses the module's uses spliced, in program order. Only
    -- generated items (a non-empty 'expansion'); user-written clauses
    -- are not here. For @--dump-splices@.
    splices :: [SourceItem]
  }

-- | Expand all uses in a module, then convert it.
expandAndConvert :: DeclMacroEnv -> MacroScope -> [Ann PExpr] -> ExpandedModule
expandAndConvert env scope terms =
  let defErrs = checkDefinitions scope
      (items, expErrs) =
        runWriter (evalStateT (expandModule env scope terms) initialMacroState)
      (m, convErrs) = runWriter (convertSourceItems scope.name items)
   in ExpandedModule
        { converted = m,
          parseErrors = [e | ChainedError e [] <- convErrs],
          expansionErrors =
            defErrs
              ++ expErrs
              ++ [ Diagnostic
                     Nothing
                     (DeclMacroParseError <$> e)
                     (renderExpansionChain chain)
                 | ChainedError e chain@(_ : _) <- convErrs
                 ],
          splices = [si | si <- items, not (null si.expansion)]
        }

-- | Expand a module's top-level terms. Each top-level use gets a fresh
-- budget. A failed use adds no clauses, so its partial output doesn't
-- cause more errors.
expandModule :: DeclMacroEnv -> MacroScope -> [Ann PExpr] -> Expand [SourceItem]
expandModule env scope terms = concat <$> traverse top terms
  where
    top t = case t.node of
      Compound ":-" [body]
        | not (isBuiltinDirective body.node) -> do
            modify' freshBudget
            items <- directive (ExpandCtx env scope t.sourceLoc []) body
            isAbandoned <- gets (.abandoned)
            pure (if isAbandoned then [] else items)
      _ -> pure [SourceItem t []]

-- | Expand a non-built-in directive @:- T@, at top level (empty
-- chain) or nested.
directive :: ExpandCtx -> Ann PExpr -> Expand [SourceItem]
directive ctx body = do
  isAbandoned <- gets (.abandoned)
  if isAbandoned
    then pure []
    else case directiveUse body.node of
      -- Variable, number, string or bad qualified name: not a clause.
      Nothing -> failIn (DeclMacroParseError MalformedTopLevel)
      Just use
        -- Already reported as a duplicate; don't pile a mismatch on it.
        | use.qualifier `elem` [Nothing, Just ctx.scope.name],
          let k = UnqualifiedIdentifier use.name (length use.args),
          k `Set.member` mixedKeys ctx.scope ->
            pure []
        | otherwise -> case resolveUse ctx.env ctx.scope use of
            Left err -> failIn err
            Right prov ->
              expandUse ctx body (QualifiedName prov use.name) (map convertTerm use.args)
  where
    -- A failed nested use kills the whole top-level use.
    failIn err = do
      unless (null ctx.chain) $ modify' (\st -> st {abandoned = True})
      emit ctx body.node err
      pure []

-- | A directive's term split into qualifier, name and arguments.
data DirectiveUse = DirectiveUse
  { qualifier :: Maybe Text,
    name :: Text,
    args :: [Ann PExpr]
  }

-- | Split a directive's term into qualifier, name and arguments.
directiveUse :: PExpr -> Maybe DirectiveUse
directiveUse p = case p of
  Compound ":" [Ann (Atom m) _, Ann (Atom n) _] -> Just (DirectiveUse (Just m) n [])
  Compound ":" [Ann (Atom m) _, Ann (Compound n as) _] ->
    Just (DirectiveUse (Just m) n as)
  Compound ":" _ -> Nothing
  Atom n -> Just (DirectiveUse Nothing n [])
  Compound n as -> Just (DirectiveUse Nothing n as)
  _ -> Nothing

-- | Find the module that provides the macro a use names.
resolveUse :: DeclMacroEnv -> MacroScope -> DirectiveUse -> Either DeclMacroError Text
resolveUse env scope use = case use.qualifier of
  Nothing -> case providers env scope DeclMacro key of
    [m] -> Right m
    []
      | (g : _) <- providers env scope GoalMacro key -> kindMismatch g
      | otherwise -> Left (UnknownDirective n a)
    ms -> Left (DeclMacroRenameError (AmbiguousName n a ms))
  Just m
    | m `elem` providers env scope DeclMacro key -> Right m
    | m `elem` providers env scope GoalMacro key -> kindMismatch m
    -- Own module, but no such macro.
    | m == scope.name -> Left (UnknownDirective n a)
    | not (Map.member m env.scopes) -> Left (DeclMacroRenameError (UnknownModule m))
    | m `notElem` map (.importModule) scope.imports ->
        Left (DeclMacroRenameError (ModuleNotImported m n a))
    -- Exported, but the import list leaves it out.
    | Set.member (QualifiedIdentifier m n a) env.exported ->
        Left (DeclMacroRenameError (ExcludedByImportList m n a))
    | otherwise -> Left (DeclMacroRenameError (NotExportedByModule m n a))
  where
    n = use.name
    a = length use.args
    key = UnqualifiedIdentifier n a
    kindMismatch m =
      Left (DeclMacroRenameError (MacroKindMismatch (QualifiedName m n) a GoalMacro))

-- | Expand a use of macro @qn@: pick a clause, instantiate it, splice
-- the elements (expanding nested uses). The checks are the renamer's
-- ('expandStep').
expandUse :: ExpandCtx -> Ann PExpr -> QualifiedName -> [Term] -> Expand [SourceItem]
expandUse ctx body qn useArgs =
  case Map.lookup key ctx.env.definitions of
    Nothing -> pure [] -- defensive: 'resolveUse' only names real providers
    Just def -> do
      r <- expandStep (instantiateBody "_decl_") ctx.chain use def
      case r of
        UseSkipped -> pure []
        UseFailed c f -> do
          let err = DeclMacroRenameError (useFailureError qn useArgs f)
          emit ctx {chain = c} body.node err
          pure []
        UseExpanded elems ->
          concat <$> traverse (element ctx {chain = use : ctx.chain}) elems
  where
    key = QualifiedIdentifier qn.moduleName qn.baseName (length useArgs)
    use = newMacroUse qn useArgs ctx.loc ctx.chain

-- | Splice one body element: report a forbidden clause, expand a nested
-- use, or keep the clause (with its chain). The chain is never empty
-- here. A forbidden clause kills the top-level use, like a failed
-- nested use does.
element :: ExpandCtx -> Term -> Expand [SourceItem]
element ctx t = do
  isAbandoned <- gets (.abandoned)
  if isAbandoned
    then pure []
    else case forbiddenForm t of
      Just form -> do
        modify' (\st -> st {abandoned = True})
        emit ctx (termToPExpr t) (MacroDeclsForbiddenClause form)
        pure []
      Nothing -> case relocate ctx.loc (termToPExpr t) of
        Ann (Compound ":-" [body]) _
          | not (isBuiltinDirective body.node) -> directive ctx body
        p -> pure [SourceItem p (map (.step) ctx.chain)]

-- | The forbidden form of a clause, if any: @:- module@,
-- @:- use_module@, @:- macro@, @:- macro_decls@, or @Head ---> Body@.
forbiddenForm :: Term -> Maybe Text
forbiddenForm t = case t of
  CompoundTerm (Unqualified ":-") [CompoundTerm (Unqualified f) args]
    | (f, length args) `elem` forbiddenDirectives -> Just f
  CompoundTerm (Unqualified "--->") [_, _] -> Just "--->"
  _ -> Nothing
  where
    forbiddenDirectives =
      [ ("module", 1),
        ("module", 2),
        ("use_module", 1),
        ("use_module", 2),
        ("macro", 1),
        ("macro_decls", 1)
      ]

-- | Definition checks:
--
-- * forbidden clauses visible in a body as written (ones built with
--   @'$compound'@ are caught when expanding);
-- * a goal macro and a declaration macro with the same key in one
--   module. The renamer would report it too, but it never runs when
--   this phase fails, and uses of the key would get a confusing kind
--   mismatch.
checkDefinitions :: MacroScope -> [Diagnostic DeclMacroError]
checkDefinitions scope =
  [ Diagnostic Nothing (AnnP (MacroDeclsForbiddenClause form) c.sourceLoc c.parsed) []
  | d <- scope.macros,
    d.node.kind == DeclMacro,
    c <- d.node.clauses,
    e <- c.node.body,
    Just form <- [forbiddenForm e]
  ]
    ++ [ Diagnostic Nothing (AnnP err d.sourceLoc d.parsed) []
       | k <- Set.toList (mixedKeys scope),
         let err = DeclMacroRenameError (DuplicateMacro k.localName k.arity)
             sameKey d' = UnqualifiedIdentifier d'.node.name d'.node.arity == k,
         -- Report the second definition, as the renamer would.
         d <- take 1 (drop 1 (filter sameKey scope.macros))
       ]

-- | Keys a module defines as both a goal macro and a declaration macro.
mixedKeys :: MacroScope -> Set UnqualifiedIdentifier
mixedKeys scope =
  Set.intersection (keysOf GoalMacro) (keysOf DeclMacro)
  where
    keysOf k =
      Set.fromList
        [ UnqualifiedIdentifier d.node.name d.node.arity
        | d <- scope.macros,
          d.node.kind == k
        ]

-- | Report an error at the outermost directive, with the chain.
emit :: ExpandCtx -> PExpr -> DeclMacroError -> Expand ()
emit ctx origin err =
  lift (tell [Diagnostic Nothing (AnnP err ctx.loc origin) chainLines])
  where
    chainLines = renderExpansionChain (map (.step) ctx.chain)

-- | Give every node of a term the same location.
relocate :: SourceLoc -> PExpr -> Ann PExpr
relocate loc p = Ann (go p) loc
  where
    go (Compound f as) = Compound f [relocate loc a.node | a <- as]
    go x = x
