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

import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.State.Strict (StateT, evalStateT, get, gets, modify')
import Control.Monad.Trans.Writer.CPS (Writer, runWriter, tell)
import Data.List (nub)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import YCHR.Internal.Diagnostic (Diagnostic (..))
import YCHR.Internal.PExpr (PExpr (..))
import YCHR.Internal.Parsed
import YCHR.Internal.Parser
  ( ParseValidationError (..),
    SourceItem (..),
    convertSourceItems,
    convertTerm,
    isBuiltinDirective,
    scanModuleTerms,
  )
import YCHR.Internal.Pretty (termToPExpr)
import YCHR.Internal.Rename (RenameError (..))
import YCHR.Internal.Rename.Macro
  ( PrimitiveError (..),
    importListPermitsMacro,
    instantiateBody,
    isVariant,
    macroDepthLimit,
    macroExpansionBudget,
    renderExpansionChain,
    selectClause,
    termsSize,
  )
import YCHR.Internal.Types (QualifiedName (..))

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
    imports :: [(Text, Maybe [Declaration])],
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
        [("prelude", Nothing) | m.name /= "prelude"]
          ++ [importOf i | AnnP i _ _ <- m.imports],
      exports = (.node) <$> m.exports,
      macros = m.macros
    }
  where
    importOf (ModuleImport n il) = (n, il)
    importOf (LibraryImport n il) = (n, il)

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
    -- | Definitions by (module, name, arity). First one wins; the
    -- renamer reports duplicates.
    definitions :: Map (Text, Text, Int) MacroDef,
    -- | Exported macros: all of them if there's no export list, else
    -- the @macro(Name\/Arity)@ items.
    exported :: Set (Text, Text, Int)
  }

-- | Index all scopes.
buildDeclMacroEnv :: [MacroScope] -> DeclMacroEnv
buildDeclMacroEnv allScopes =
  DeclMacroEnv
    { scopes = Map.fromList [(s.name, s) | s <- allScopes],
      definitions =
        Map.fromListWith
          (\_new old -> old)
          [ ((s.name, d.node.name, d.node.arity), d.node)
          | s <- allScopes,
            d <- s.macros
          ],
      exported =
        Set.fromList
          [ (s.name, n, a)
          | s <- allScopes,
            (n, a) <- exportedMacros s
          ]
    }
  where
    exportedMacros s =
      let own = [(d.node.name, d.node.arity) | d <- s.macros]
       in case s.exports of
            Nothing -> own
            Just items ->
              [ (meb.name, meb.arity)
              | MacroExportDecl meb <- items,
                (meb.name, meb.arity) `elem` own
              ]

-- | Modules that make macro @n\/a@ of the given kind visible: the
-- module itself, plus imports that export it. Same as the renamer's
-- @visibleMacroProviders@.
providers :: DeclMacroEnv -> MacroScope -> MacroKind -> Text -> Int -> [Text]
providers env scope kind n a =
  filter
    ofKind
    ( nub
        ( [scope.name | Map.member (scope.name, n, a) env.definitions]
            ++ [ mn
               | (mn, il) <- scope.imports,
                 Set.member (mn, n, a) env.exported,
                 importListPermitsMacro n a il
               ]
        )
    )
  where
    ofKind mn = case Map.lookup (mn, n, a) env.definitions of
      Just d -> d.kind == kind
      Nothing -> False

-- ---------------------------------------------------------------------------
-- Expansion
-- ---------------------------------------------------------------------------

-- | A use in the current expansion chain.
data Use = Use
  { step :: ExpansionStep,
    -- | Arguments as written, for the cycle check.
    arguments :: [Term],
    -- | 'termsSize' of 'arguments'. Cheap check before 'isVariant'.
    argumentsSize :: Int,
    -- | Uses in the chain, this one included.
    depth :: Int
  }

-- | Expansion state for one module (like the renamer's macro state).
data ExpState = ExpState
  { nextSeed :: Int,
    -- | Expansions left for the current top-level use.
    remaining :: Int,
    -- | The current top-level use failed (limit hit, or error in a
    -- nested use). Skip the rest silently, so the error shows once.
    abandoned :: Bool
  }

type Expand = StateT ExpState (Writer [Diagnostic DeclMacroError])

-- | A module after expansion and conversion.
data ExpandedModule = ExpandedModule
  { converted :: Module,
    -- | Conversion errors in clauses the user wrote.
    parseErrors :: [AnnP ParseValidationError],
    -- | Expansion errors, definition checks, and conversion errors in
    -- generated clauses (with their chain).
    expansionErrors :: [Diagnostic DeclMacroError]
  }

-- | Expand all uses in a module, then convert it.
expandAndConvert :: DeclMacroEnv -> MacroScope -> [Ann PExpr] -> ExpandedModule
expandAndConvert env scope terms =
  let defErrs = checkDefinitions scope
      (items, expErrs) =
        runWriter (evalStateT (expandModule env scope terms) initialState)
      (m, convErrs) = convertSourceItems scope.name items
   in ExpandedModule
        { converted = m,
          parseErrors = [e | (e, []) <- convErrs],
          expansionErrors =
            defErrs
              ++ expErrs
              ++ [ Diagnostic Nothing (DeclMacroParseError <$> e) (renderExpansionChain chain)
                 | (e, chain@(_ : _)) <- convErrs
                 ]
        }
  where
    initialState = ExpState {nextSeed = 0, remaining = macroExpansionBudget, abandoned = False}

-- | Expand a module's top-level terms. Each top-level use gets a fresh
-- budget. A failed use adds no clauses, so its partial output doesn't
-- cause more errors.
expandModule :: DeclMacroEnv -> MacroScope -> [Ann PExpr] -> Expand [SourceItem]
expandModule env scope terms = concat <$> traverse top terms
  where
    top t = case t.node of
      Compound ":-" [body]
        | not (isBuiltinDirective body.node) -> do
            modify' (\st -> st {remaining = macroExpansionBudget, abandoned = False})
            items <- directive env scope t.sourceLoc [] body
            isAbandoned <- gets (.abandoned)
            pure (if isAbandoned then [] else items)
      _ -> pure [SourceItem t []]

-- | Expand a non-built-in directive @:- T@, at top level (empty
-- @chain@) or nested. @loc@ is where the outermost directive is.
directive ::
  DeclMacroEnv -> MacroScope -> SourceLoc -> [Use] -> Ann PExpr -> Expand [SourceItem]
directive env scope loc chain body = do
  isAbandoned <- gets (.abandoned)
  if isAbandoned
    then pure []
    else case useShape body.node of
      -- Variable, number, string or bad qualified name: not a clause.
      Nothing -> failIn chain (DeclMacroParseError MalformedTopLevel)
      Just (qual, n, rawArgs)
        -- Already reported as a duplicate; don't pile a mismatch on it.
        | qual `elem` [Nothing, Just scope.name],
          Set.member (n, length rawArgs) (mixedKeys scope) ->
            pure []
      Just (qual, n, rawArgs) -> case resolveUse env scope qual n (length rawArgs) of
        Left err -> failIn chain err
        Right prov -> expandUse env scope loc chain body prov n (map convertTerm rawArgs)
  where
    -- A failed nested use kills the whole top-level use.
    failIn c err = do
      if null c then pure () else modify' (\st -> st {abandoned = True})
      emit loc body.node c err
      pure []

-- | Split a directive's term into qualifier, name and arguments.
useShape :: PExpr -> Maybe (Maybe Text, Text, [Ann PExpr])
useShape p = case p of
  Compound ":" [Ann (Atom m) _, Ann (Atom n) _] -> Just (Just m, n, [])
  Compound ":" [Ann (Atom m) _, Ann (Compound n as) _] -> Just (Just m, n, as)
  Compound ":" _ -> Nothing
  Atom n -> Just (Nothing, n, [])
  Compound n as -> Just (Nothing, n, as)
  _ -> Nothing

-- | Find the module that provides the macro a use names.
resolveUse ::
  DeclMacroEnv -> MacroScope -> Maybe Text -> Text -> Int -> Either DeclMacroError Text
resolveUse env scope qual n a = case qual of
  Nothing -> case providers env scope DeclMacro n a of
    [m] -> Right m
    []
      | (g : _) <- providers env scope GoalMacro n a -> kindMismatch g
      | otherwise -> Left (UnknownDirective n a)
    ms -> Left (DeclMacroRenameError (AmbiguousName n a ms))
  Just m
    | m `elem` providers env scope DeclMacro n a -> Right m
    | m `elem` providers env scope GoalMacro n a -> kindMismatch m
    -- Own module, but no such macro.
    | m == scope.name -> Left (UnknownDirective n a)
    | not (Map.member m env.scopes) -> Left (DeclMacroRenameError (UnknownModule m))
    | m `notElem` map fst scope.imports ->
        Left (DeclMacroRenameError (ModuleNotImported m n a))
    | otherwise -> Left (DeclMacroRenameError (NotExportedByModule m n a))
  where
    kindMismatch m =
      Left (DeclMacroRenameError (MacroKindMismatch (QualifiedName m n) a GoalMacro))

-- | Expand a resolved use: pick a clause, instantiate it, splice the
-- elements (expanding nested uses). Same checks as the renamer's
-- @expandMacroUse@.
expandUse ::
  DeclMacroEnv ->
  MacroScope ->
  SourceLoc ->
  [Use] ->
  Ann PExpr ->
  Text ->
  Text ->
  [Term] ->
  Expand [SourceItem]
expandUse env scope loc chain body prov n useArgs = do
  st <- get
  case Map.lookup (prov, n, arity) env.definitions of
    Nothing -> pure [] -- defensive: 'resolveUse' only names real providers
    Just def
      | st.abandoned -> pure []
      | useDepth > macroDepthLimit -> abandon (MacroExpansionTooDeep qn arity)
      | st.remaining <= 0 -> abandon (MacroExpansionTooLarge qn arity)
      | any repeats chain -> failNested chain (MacroCycle qn arity)
      | otherwise -> case selectClause def.clauses useArgs of
          Nothing -> failNested chain (NoMatchingMacroClause qn useArgs)
          Just (binds, clause) -> do
            modify' (\s' -> s' {remaining = s'.remaining - 1, nextSeed = s'.nextSeed + 1})
            let chain' = use : chain
            case instantiateBody "_decl_" st.nextSeed binds clause of
              Left pe ->
                failNested chain' (MalformedMacroPrimitive pe.operand pe.received)
              Right elems -> concat <$> traverse (element env scope loc chain') elems
  where
    arity = length useArgs
    qn = QualifiedName prov n
    useSize = termsSize useArgs
    useDepth = case chain of
      (u : _) -> u.depth + 1
      [] -> 1
    use =
      Use
        { step =
            ExpansionStep {macroModule = prov, macroName = n, macroArity = arity, site = loc},
          arguments = useArgs,
          argumentsSize = useSize,
          depth = useDepth
        }
    repeats u =
      (u.step.macroModule, u.step.macroName, u.step.macroArity) == (prov, n, arity)
        && u.argumentsSize == useSize
        && isVariant u.arguments useArgs
    abandon err = do
      modify' (\s' -> s' {abandoned = True})
      emit loc body.node chain (DeclMacroRenameError err)
      pure []
    -- A nested error kills the top-level use, so a branching macro
    -- reports it once.
    failNested c err = do
      if null chain then pure () else modify' (\s' -> s' {abandoned = True})
      emit loc body.node c (DeclMacroRenameError err)
      pure []

-- | Splice one body element: report a forbidden clause, expand a nested
-- use, or keep the clause (with its chain). @chain@ is never empty
-- here. A forbidden clause kills the top-level use, like a failed
-- nested use does.
element :: DeclMacroEnv -> MacroScope -> SourceLoc -> [Use] -> Term -> Expand [SourceItem]
element env scope loc chain t = do
  isAbandoned <- gets (.abandoned)
  if isAbandoned
    then pure []
    else case forbiddenForm t of
      Just form -> do
        modify' (\st -> st {abandoned = True})
        emit loc (termToPExpr t) chain (MacroDeclsForbiddenClause form)
        pure []
      Nothing -> case relocate loc (termToPExpr t) of
        Ann (Compound ":-" [body]) _
          | not (isBuiltinDirective body.node) -> directive env scope loc chain body
        p -> pure [SourceItem p (map (.step) chain)]

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
       | (n, a) <- Set.toList (mixedKeys scope),
         let err = DeclMacroRenameError (DuplicateMacro n a)
             sameKey d' = (d'.node.name, d'.node.arity) == (n, a),
         -- Report the second definition, as the renamer would.
         d <- take 1 (drop 1 (filter sameKey scope.macros))
       ]

-- | Keys a module defines as both a goal macro and a declaration macro.
mixedKeys :: MacroScope -> Set (Text, Int)
mixedKeys scope =
  Set.intersection (keysOf GoalMacro) (keysOf DeclMacro)
  where
    keysOf k = Set.fromList [(d.node.name, d.node.arity) | d <- scope.macros, d.node.kind == k]

-- | Report an error at the outermost directive, with the chain.
emit :: SourceLoc -> PExpr -> [Use] -> DeclMacroError -> Expand ()
emit loc origin chain err =
  lift
    ( tell
        [ Diagnostic
            Nothing
            (AnnP err loc origin)
            (renderExpansionChain (map (.step) chain))
        ]
    )

-- | Give every node of a term the same location.
relocate :: SourceLoc -> PExpr -> Ann PExpr
relocate loc p = Ann (go p) loc
  where
    go (Compound f as) = Compound f [relocate loc a.node | a <- as]
    go x = x
