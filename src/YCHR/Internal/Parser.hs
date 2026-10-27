{-# LANGUAGE OverloadedStrings #-}

-- | Parser for the CHR surface language.
--
-- Parses Prolog-compatible CHR syntax into a 'Module' value.
--
-- Implementation: parses source text to generic 'PExpr' terms first
-- (via 'YCHR.Internal.PExpr'), then converts each term to the surface AST.
--
-- Supported syntax:
--
-- @
-- % Line comments
--
-- :- module(order, [leq\/2]). -- Export list specifies visible constraints.
-- :- use_module(library(lists)).
--
-- :- chr_constraint leq\/2.
-- :- chr_constraint fib\/2, upto\/1.
--
-- refl \@ leq(X, X) \<=> true.
-- leq(X, X) \<=> true.
-- trans \@ leq(X, Y), leq(Y, Z) ==> leq(X, Z).
-- a \@ kept \\ removed \<=> guard | body.
--
-- [H|T]     -- list with head H and tail T
-- [a, b, c] -- list literal (sugar for '.'(a,'.'(b,'.'(c,'[]'))))
-- @
module YCHR.Internal.Parser
  ( -- * Public parsing functions
    parseModule,
    parseModuleWith,
    parseConstraint,
    parseConstraintWith,
    parseQuery,
    parseQueryWith,
    parseTerm,
    parseTermWith,
    parseRule,
    Converted (..),

    -- * Module conversion with provenance
    parseModuleTermsWith,
    defaultModuleNameForSource,
    SourceItem (..),
    ChainedError (..),
    convertSourceItems,
    scanModuleTerms,
    builtinDirectives,
    isBuiltinDirective,
    convertTerm,

    -- * Operator tables
    OpTable,
    builtinOps,
    mergeOps,
    opTableEntries,

    -- * Module headers
    ModuleHeader (..),
    collectModuleHeader,
    buildModuleOpTable,
    extractOpDecls,

    -- * Validation errors
    ParseValidationError (..),
  )
where

import Control.Monad.Trans.Writer.CPS (Writer, runWriter, tell)
import Data.Either (partitionEithers)
import Data.List.NonEmpty qualified as NE
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe (catMaybes, fromMaybe, isJust, listToMaybe, mapMaybe)
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
-- MicroHs's 'Data.Text' lacks 'last'; the shim supplies it
-- (dev-docs/MICROHS_GAPS.md, gap 4).
import Data.Text.Shim qualified as Text
import System.FilePath (takeBaseName)
import Text.Parsec (ParseError)
import YCHR.Internal.PExpr
  ( LeadingTerms (..),
    PExpr (Atom, Compound, Str, Var),
    mergeOps,
    opTableEntries,
  )
import YCHR.Internal.PExpr qualified as P
import YCHR.Internal.Parsed
import YCHR.Internal.Types (UnqualifiedIdentifier (..))

-- * Operator tables

-- | Operator table: maps fixity levels to operators.
-- Re-exported from 'YCHR.Internal.PExpr'.
type OpTable = P.OpTable

-- | Built-in operators for CHR syntax.
--
-- This is a minimal table containing only the operators needed for CHR
-- language structure. Arithmetic and comparison operators are provided
-- by the @builtins@ library.
--
-- Directive keywords (@chr_constraint@, @function@, @chr_type@, ...)
-- are prefix operators following standard Prolog convention, so that
-- @:- chr_constraint leq\/2.@ parses as a single term.
builtinOps :: OpTable
builtinOps =
  P.mkOpTable
    [ (100, [(P.Yfx, ":")]),
      (400, [(P.Yfx, "/")]),
      (500, [(P.Fx, "fun")]),
      (750, [(P.Xfx, "is"), (P.Xfx, "=")]),
      (1000, [(P.Xfy, ",")]),
      (1105, [(P.Xfy, "|")]),
      (1110, [(P.Xfy, "->")]),
      (1100, [(P.Xfy, ";"), (P.Xfx, "\\")]),
      -- Bounded polymorphism: @sig requiring bound1, bound2, ...@,
      -- and refinement predicates: @sig refining type@.
      -- Looser than @->@ (1110) so the clause sits outside the
      -- signature's arrow, tighter than the directive prefix at 1180
      -- so the clause stays inside the @:- function@ arg.
      -- Comma (1000) is also tighter, so the bound list on the right
      -- is a comma chain consumed as a single argument here.
      -- Both are @xfx@ at the /same/ priority, so they cannot chain:
      -- @sig requiring B refining T@ (and the reverse) is a syntax
      -- error, which is how the two clauses are kept mutually
      -- exclusive without a dedicated check.
      (1140, [(P.Xfx, "requiring"), (P.Xfx, "refining")]),
      (1150, [(P.Xfx, "--->")]),
      (1180, [(P.Xfx, "<=>"), (P.Xfx, "==>")]),
      ( 1180,
        [ (P.Fx, "chr_constraint"),
          (P.Fx, "chr_type"),
          (P.Fx, "opaque_type"),
          (P.Fx, "function"),
          (P.Fx, "open_function"),
          (P.Fx, "class"),
          (P.Fx, "open_class"),
          (P.Fx, "extend_class_type"),
          (P.Fx, "extend_class"),
          (P.Fx, "extend_function"),
          (P.Fx, "inline"),
          (P.Fx, "constraint_use"),
          (P.Fx, "macro"),
          (P.Fx, "macro_decls")
        ]
      ),
      (1190, [(P.Xfx, "@")]),
      (1200, [(P.Fx, ":-")]),
      -- Reserve @end@ as a keyword (for @fun(...) -> ... end@) without
      -- making it a usable operator.  Fixity above 'maxPrec' ensures it
      -- is never consumed by the Pratt parser, but its presence in
      -- 'wordOpSet' prevents 'atomP' from treating it as an atom.
      (P.maxPrec + 1, [(P.Fx, "end")])
    ]

-- * Public parsing functions

-- | Parse a CHR module from source text using the built-in operator table.
--
-- The first argument is the source file name (used in error messages only).
parseModule :: String -> Text -> Either ParseError (Converted Module)
parseModule = parseModuleWith builtinOps

-- | Parse a CHR module from source text using a custom operator table.
parseModuleWith :: OpTable -> String -> Text -> Either ParseError (Converted Module)
parseModuleWith table sourceName src = do
  terms <- P.parseTerms table sourceName src
  pure (convertModule (defaultModuleNameForSource sourceName) terms)

-- | Read a module's top-level terms without converting them. Used by
-- "YCHR.Internal.DeclMacro".
parseModuleTermsWith :: OpTable -> String -> Text -> Either ParseError [Ann PExpr]
parseModuleTermsWith = P.parseTerms

-- | Default module name for a header-less source.
--
-- File-backed inputs become @\<basename\>@ (directory and extension
-- stripped), so an ambiguity diagnostic that mentions two header-less
-- files names the files instead of printing two identical placeholders.
-- Empty or degenerate source names fall back to the sentinel
-- @\<no_module\>@; the DSL, REPL one-shots, and parser tests reach this
-- branch.
defaultModuleNameForSource :: String -> Text
defaultModuleNameForSource sourceName =
  case takeBaseName sourceName of
    "" -> "<no_module>"
    base -> "<" <> Text.pack base <> ">"

-- | Parse a single constraint from surface-language 'Text', using the
-- builtin operator table.
--
-- The outer 'Left' is a parsec parse error; the inner 'Left' is a
-- 'ParseValidationError' (the input parsed but did not denote a
-- constraint, e.g. a bare variable or integer).
--
-- The source name (first argument) is used in error messages only.
-- Example: @parseConstraint "\<query\>" "leq(X, Y)"@.
parseConstraint ::
  String ->
  Text ->
  Either ParseError (Either (AnnP ParseValidationError) Constraint)
parseConstraint = parseConstraintWith builtinOps

-- | Parse a single constraint from surface-language 'Text' using a
-- custom operator table. Used by the single-goal entry points so that
-- user-declared operators (e.g. @+@ from the prelude) are recognized
-- in goal arguments, mirroring the multi-goal parser.
parseConstraintWith ::
  OpTable ->
  String ->
  Text ->
  Either ParseError (Either (AnnP ParseValidationError) Constraint)
parseConstraintWith table sourceName src = do
  term <- P.parseTermNoDot table sourceName src
  pure (convertConstraint term)

-- | Parse a single term from surface-language 'Text'.
--
-- The source name (first argument) is used in error messages only.
-- Example: @parseTerm "\<query\>" "f(X, 42)"@.
parseTerm ::
  String ->
  Text ->
  Either ParseError Term
parseTerm = parseTermWith builtinOps

-- | Parse a single term with a custom operator table.
parseTermWith ::
  OpTable ->
  String ->
  Text ->
  Either ParseError Term
parseTermWith table sourceName src = do
  term <- P.parseTermNoDot table sourceName src
  pure (convertTerm term)

-- | Parse a query: a comma-separated list of goals terminated by a dot.
--
-- The source name (first argument) is used in error messages only.
-- Example: @parseQuery "\<query\>" "fib(10, X), Y is X + 1."@.
parseQuery ::
  String ->
  Text ->
  Either ParseError [Term]
parseQuery = parseQueryWith builtinOps

-- | Parse a query with a custom operator table.
--
-- The terminating @.@ is optional: if @src@ (with trailing whitespace
-- stripped) ends in a dot, the dot-terminated parser is used; otherwise
-- the non-terminated one. Picking the parser up front (rather than
-- retrying on failure) keeps the parse error message attached to the
-- right phase: a missing or extra dot surfaces as a terminator error
-- rather than a term-shape error.
parseQueryWith ::
  OpTable ->
  String ->
  Text ->
  Either ParseError [Term]
parseQueryWith table sourceName src =
  let parser = if dotTerminated then P.parseTerm else P.parseTermNoDot
   in map convertTerm . flattenComma <$> parser table sourceName src
  where
    trimmed = Text.stripEnd src
    dotTerminated = not (Text.null trimmed) && Text.last trimmed == '.'

-- | Parse a single CHR rule from surface-language 'Text'.
--
-- The outer 'Left' is a parsec parse error. On parse success, the
-- value is 'Nothing' if the parsed term is not a rule shape (a
-- 'MalformedTopLevel' error is emitted in that case); otherwise it
-- is the parsed 'Rule', and the errors are any 'MalformedConstraint'
-- errors collected from its head.
--
-- The source name (first argument) is used in error messages only.
parseRule :: String -> Text -> Either ParseError (Converted (Maybe Rule))
parseRule sourceName src = do
  term <- P.parseTerm builtinOps sourceName src
  pure (runConv (convertRule term))

-- * Module headers

-- | Minimal operator table for the first pass: only enough to parse
-- @:- module(...)@ and @:- use_module(...)@ directives.
firstPassTable :: OpTable
firstPassTable =
  P.mkOpTable
    [ (400, [(P.Yfx, "/")]),
      (500, [(P.Fx, "fun")]),
      (1200, [(P.Fx, ":-")])
    ]

-- | Header information collected from a module's leading directives during
-- the lightweight first parsing pass.
--
-- The header captures everything needed to compute per-module operator
-- visibility before the full parse: the module's name, the operators it
-- exports, the @use_module@ directives that immediately follow the
-- @module@ directive, and the source location at which header parsing
-- stopped (used to detect misplaced @use_module@ directives later in the
-- file).
data ModuleHeader = ModuleHeader
  { modName :: Text,
    -- | Source location of the @:- module(...)@ directive. 'dummyLoc' if
    -- the file does not declare a module.
    modLoc :: SourceLoc,
    -- | The original PExpr of the @module(...)@ body, for diagnostics.
    modOrigin :: PExpr,
    -- | Operators declared in the module's export list.
    exportOps :: [OpDecl],
    -- | @use_module@ imports immediately following the @module@ directive
    -- (or, when there is no module directive, immediately at the start of
    -- the file).
    headerImports :: [AnnP Import],
    -- | Source location of the first content that is not a header
    -- directive, or 'Nothing' if the file ends after the header.
    -- Imports appearing at or beyond this location are misplaced.
    trailingLoc :: Maybe SourceLoc
  }
  deriving (Show, Eq)

-- | Collect a 'ModuleHeader' from a source file using the minimal first-pass
-- operator table.
--
-- Stops at the first directive or rule that cannot be parsed by the
-- first-pass table — which in practice means anything other than
-- @:- module(...)@ or @:- use_module(...)@.
collectModuleHeader :: String -> Text -> Either ParseError ModuleHeader
collectModuleHeader sourceName src = do
  LeadingTerms terms tloc <- P.parseLeadingTerms firstPassTable sourceName src
  let (modPart, rest1) = case terms of
        (t : ts) | Just md <- asModuleDirective t -> (Just md, ts)
        _ -> (Nothing, terms)
      (importTerms, leftover) = span isImport rest1
      finalLoc = case leftover of
        [] -> tloc
        (Ann _ loc : _) -> Just loc
      info =
        fromMaybe
          ModuleDirective
            { name = defaultModuleNameForSource sourceName,
              loc = dummyLoc,
              origin = Atom "",
              exports = Nothing
            }
          modPart
  pure
    ModuleHeader
      { modName = info.name,
        modLoc = info.loc,
        modOrigin = info.origin,
        exportOps = [op | OperatorDecl op <- fromMaybe [] info.exports],
        headerImports = mapMaybe toImport importTerms,
        trailingLoc = finalLoc
      }
  where
    asModuleDirective (Ann (Compound ":-" [body]) loc)
      | Compound "module" [Ann (Atom name) _, exports] <- body.node =
          Just
            ModuleDirective
              { name,
                loc,
                origin = body.node,
                exports = Just (map OperatorDecl (extractOpDeclsFromPExpr exports.node))
              }
      | Compound "module" [Ann (Atom name) _] <- body.node =
          Just ModuleDirective {name, loc, origin = body.node, exports = Nothing}
    asModuleDirective _ = Nothing

    isImport (Ann (Compound ":-" [Ann (Compound "use_module" args) _]) _) =
      length args `elem` [1, 2]
    isImport _ = False

    -- Malformed @use_module@ directives are silently skipped here; the full
    -- parse path emits 'MalformedImport' for them via 'convertDirective'.
    toImport (Ann (Compound ":-" [body]) loc) = case body.node of
      Compound "use_module" [imp] ->
        either (const Nothing) Just (convertImport loc body.node imp)
      Compound "use_module" [imp, importList] ->
        (runConv (convertImportWithList loc body.node imp importList)).value
      _ -> Nothing
    toImport _ = Nothing

-- | Build the per-module operator table for a user module.
--
-- Combines the built-in operators, the always-visible prelude operators,
-- the module's own exported operators, and the operators reachable through
-- its @use_module@ imports. Returns @Left name@ if two operator declarations
-- with the same name disagree on fixity or type.
--
-- For each import:
--
--   * @use_module(M)@ (no item list) brings in every operator @M@ exports.
--   * @use_module(M, [items])@ brings in only the operators listed via
--     @op(...)@ entries inside the item list.
--
-- Operators of unknown source modules (e.g. @use_module(missing_lib)@)
-- contribute nothing here; the resulting unknown-library, unknown-module,
-- or unknown-import error is reported elsewhere.
buildModuleOpTable ::
  -- | Built-in operators
  OpTable ->
  -- | Prelude's exported operators (always visible)
  [OpDecl] ->
  -- | Map from module name to that module's exported operators
  Map Text [OpDecl] ->
  -- | The user module's header
  ModuleHeader ->
  Either Text OpTable
buildModuleOpTable base preludeOps exportsByModule header =
  mergeOps base (preludeOps ++ header.exportOps ++ importedOps)
  where
    importedOps = concatMap importedFrom header.headerImports
    importedFrom (AnnP imp _ _) = case imp of
      ModuleImport m Nothing -> Map.findWithDefault [] m exportsByModule
      LibraryImport m Nothing -> Map.findWithDefault [] m exportsByModule
      ModuleImport m (Just items) -> selectOps m items
      LibraryImport m (Just items) -> selectOps m items
    selectOps m items =
      let exported = Map.findWithDefault [] m exportsByModule
       in [op | OperatorDecl op <- items, op `elem` exported]

-- | Extract 'OpDecl' entries from a PExpr representing an export list.
extractOpDeclsFromPExpr :: PExpr -> [OpDecl]
extractOpDeclsFromPExpr pexpr =
  [op | item <- unfoldList pexpr, Just op <- [toOpDecl item.node]]
  where
    toOpDecl (Compound "op" [Ann (P.Int fix) _, Ann tyExpr _, Ann nameExpr _])
      | Just ty <- parseOpTypeFromPExpr tyExpr,
        Just name <- atomName nameExpr =
          Just (OpDecl (fromInteger fix) ty name)
    toOpDecl _ = Nothing

-- | If the expression is an atom, return its text; otherwise 'Nothing'.
atomName :: PExpr -> Maybe Text
atomName (Atom a) = Just a
atomName _ = Nothing

-- | Parse an operator type from a PExpr atom.
parseOpTypeFromPExpr :: PExpr -> Maybe P.OpType
parseOpTypeFromPExpr (Atom "xfx") = Just P.Xfx
parseOpTypeFromPExpr (Atom "xfy") = Just P.Xfy
parseOpTypeFromPExpr (Atom "yfx") = Just P.Yfx
parseOpTypeFromPExpr (Atom "fx") = Just P.Fx
parseOpTypeFromPExpr (Atom "fy") = Just P.Fy
parseOpTypeFromPExpr (Atom "xf") = Just P.Xf
parseOpTypeFromPExpr (Atom "yf") = Just P.Yf
parseOpTypeFromPExpr _ = Nothing

-- | Extract operator declarations from an already-parsed module's export list.
extractOpDecls :: Module -> [OpDecl]
extractOpDecls m = case m.exports of
  Nothing -> []
  Just annExports -> [op | OperatorDecl op <- annExports.node]

-- * Internal: PExpr conversions

{- Note [Qualified name handling]

The qualified-name forms @module:name@ and @module:name(args)@ are
intercepted before the generic 'Compound' fallback. Without this, the parser
would emit a 2-ary @':'@ constructor with two unrelated children, and the
renamer would have to undo that downstream. The same handling is mirrored in
'convertConstraint', 'convertTypeExpr', and 'convertBoundSig'.
-}

-- | Convert a 'PExpr' to a 'Term'.
--
-- See Note [Qualified name handling].
convertTerm :: Ann PExpr -> Term
convertTerm (Ann pexpr _) = case pexpr of
  Var t -> VarTerm t
  P.Int n -> IntTerm n
  P.Float n -> FloatTerm n
  Atom t -> CompoundTerm (Unqualified t) []
  Str t -> TextTerm t
  P.Wildcard -> Wildcard
  Compound ":" [Ann (Atom m) _, Ann (Atom n) _] ->
    CompoundTerm (Qualified m n) []
  Compound ":" [Ann (Atom m) _, Ann (Compound n args) _] ->
    CompoundTerm (Qualified m n) (map convertTerm args)
  Compound f args ->
    CompoundTerm (Unqualified f) (map convertTerm args)

-- | Convert a 'PExpr' to a 'Constraint'.
--
-- Returns 'Left' with a 'MalformedConstraint' error when the input is not
-- an atom or compound term (e.g. a bare variable, integer, or string).
--
-- See Note [Qualified name handling].
convertConstraint :: Ann PExpr -> Either (AnnP ParseValidationError) Constraint
convertConstraint (Ann pexpr loc) = case pexpr of
  Atom name ->
    Right (Constraint (Unqualified name) [])
  Compound ":" [Ann (Atom m) _, Ann (Atom n) _] ->
    Right (Constraint (Qualified m n) [])
  Compound ":" [Ann (Atom m) _, Ann (Compound n args) _] ->
    Right (Constraint (Qualified m n) (map convertTerm args))
  Compound name args ->
    Right (Constraint (Unqualified name) (map convertTerm args))
  _ -> Left (AnnP MalformedConstraint loc pexpr)

-- ** Flattening helpers

-- | Flatten a right-nested comma operator into a non-empty list.
-- Note: O(n) because @,@ is @xfy@ so the tree is right-heavy (left child
-- is always a leaf).
flattenComma1 :: Ann PExpr -> NE.NonEmpty (Ann PExpr)
flattenComma1 (Ann (Compound "," [l, r]) _) =
  flattenComma1 l <> flattenComma1 r
flattenComma1 e = NE.singleton e

-- | List-returning view of 'flattenComma1' for callers that don't need
-- the non-emptiness invariant.
flattenComma :: Ann PExpr -> [Ann PExpr]
flattenComma = NE.toList . flattenComma1

-- | Flatten a right-nested semicolon operator into a list.
flattenSemicolon :: Ann PExpr -> [Ann PExpr]
flattenSemicolon (Ann (Compound ";" [l, r]) _) =
  flattenSemicolon l ++ flattenSemicolon r
flattenSemicolon e = [e]

-- | Unfold a Prolog list ('.'\/2 + '[]') to a flat list of elements.
unfoldList :: PExpr -> [Ann PExpr]
unfoldList (Atom "[]") = []
unfoldList (Compound "." [h, t]) = h : unfoldList t.node
unfoldList _ = [] -- non-proper list tail: ignore

-- | Like 'unfoldList', but returns 'Nothing' for inputs that are not a
-- proper Prolog list (i.e. that do not terminate in @[]@). Use this
-- where a non-list argument should be rejected with a structured error
-- rather than silently coerced to an empty list.
unfoldListStrict :: PExpr -> Maybe [Ann PExpr]
unfoldListStrict (Atom "[]") = Just []
unfoldListStrict (Compound "." [h, t]) = (h :) <$> unfoldListStrict t.node
unfoldListStrict _ = Nothing

-- ** Module conversion

-- | Validation errors, collected in source order.
type Conv = Writer [AnnP ParseValidationError]

-- | Report an error and give 'Nothing'.
failWith :: AnnP ParseValidationError -> Conv (Maybe a)
failWith e = Nothing <$ tell [e]

-- | Report errors and give 'Nothing'.
failWithAll :: [AnnP ParseValidationError] -> Conv (Maybe a)
failWithAll errs = Nothing <$ tell errs

-- | A conversion result and its errors.
data Converted a = Converted
  { -- | The converted value.
    value :: a,
    -- | Validation errors, in source order.
    errors :: [AnnP ParseValidationError]
  }

-- | Run a conversion.
runConv :: Conv a -> Converted a
runConv c = let (a, errs) = runWriter c in Converted a errs

-- | A @:- module(Name)@ or @:- module(Name, Exports)@ directive.
data ModuleDirective = ModuleDirective
  { name :: Text,
    loc :: SourceLoc,
    -- | The @module(...)@ term, for diagnostics.
    origin :: PExpr,
    -- | The export list, or 'Nothing' if there is none.
    exports :: Maybe [Declaration]
  }

-- | Internal directive type.
data Directive
  = DirModule ModuleDirective
  | DirImport (AnnP Import)
  | DirConstraintDecl [Ann Declaration]
  | DirFunctionDecl [Ann Declaration]
  | DirOpenFunctionDecl [Ann Declaration]
  | DirClassDecl [Ann Declaration]
  | DirOpenClassDecl [Ann Declaration]
  | DirInlineDecl [Ann InlineDecl]
  | DirConstraintUseDecl [Ann ConstraintUseDecl]
  | DirExtendClassTypeDecl [Ann Declaration]
  | DirExtendFunctionEqn (AnnP FunctionEquation)
  | DirExtendClassEqn (AnnP FunctionEquation)
  | DirTypeDecl [Ann TypeDefinition]
  | -- | A one-line @:- macro Head ---> [Goals].@ or
    -- @:- macro_decls Head ---> [Clauses].@ definition.
    DirMacro (AnnP MacroDef)
  | -- | A @:- macro Name\/N, ...@ or @:- macro_decls Name\/N, ...@
    -- declaration, whose clauses are top-level @Head ---> [...]@ items.
    -- Each key carries the directive's location and term.
    DirMacroDecl [AnnP MacroKey]
  | DirOther

-- | The kind, name and arity a @:- macro Name\/N@ or
-- @:- macro_decls Name\/N@ declaration declares.
data MacroKey = MacroKey
  { kind :: MacroKind,
    name :: Text,
    arity :: Int
  }

-- | Internal module item type.
data ModuleItem
  = ItemDirective Directive
  | ItemRule Rule
  | ItemEquation (AnnP FunctionEquation)
  | -- | A top-level @Head ---> [Goals].@ macro clause.
    ItemMacroClause NamedClause

-- | A macro clause with its macro's name.
data NamedClause = NamedClause
  { name :: Text,
    clause :: AnnP MacroClause
  }

-- | The name and arity of a clause's macro. The arity is the number of
-- head patterns.
clauseKey :: NamedClause -> UnqualifiedIdentifier
clauseKey nc = UnqualifiedIdentifier nc.name (length nc.clause.node.params)

-- | Validation error detected during module conversion.
data ParseValidationError
  = -- | Equations for a non-open function are not contiguous.
    DiscontiguousEquations Text
  | -- | @:- function@ declarations for a non-open function are not
    -- contiguous within the module.
    DiscontiguousFunctionDecls Text
  | -- | A @use_module@ directive's argument was not a module name or
    -- @library(name)@.
    MalformedImport
  | -- | A constraint position contained something that is not an atom or
    -- compound term (e.g. a bare variable, integer, or string).
    MalformedConstraint
  | -- | A declaration inside @:- chr_constraint@ / @:- function@ /
    -- @:- open_function@ / @:- class@ / @:- open_class@ /
    -- @:- extend_class_type@ has a shape the parser does not recognize.
    -- The declaration is dropped.
    MalformedDeclaration
  | -- | An item in a @module(...)@ export list or @use_module/2@ import
    -- list is not one of the recognized shapes (@name/arity@,
    -- @fun name/arity@, @op(...)@, @type(...)@). The item is dropped.
    MalformedExportItem
  | -- | A type expression (in an argument type, return type, or bound
    -- signature) is not a variable, atom, or compound term — typically a
    -- stray literal or string. The enclosing declaration is dropped.
    MalformedTypeExpr
  | -- | A data constructor in a @:- chr_type ... ---> ...@ definition is
    -- not an atom or compound term. The enclosing type definition is
    -- dropped.
    MalformedDataConstructor
  | -- | A @:- chr_type@ directive does not have the expected
    -- @head ---> alts@ shape. The type definition is dropped.
    MalformedTypeDefinition
  | -- | A @:- opaque_type@ directive carries a constructor body
    -- (@head ---> ...@). Opaque types cannot have data constructors.
    -- The type definition is dropped.
    OpaqueTypeHasConstructors
  | -- | A @:- opaque_type@ directive does not have the expected
    -- @name@ or @name(Vars)@ head shape. The type definition is dropped.
    MalformedOpaqueTypeDefinition
  | -- | A type-definition parameter (in @:- chr_type@ or
    -- @:- opaque_type@) is not a type variable. Atoms, compounds, and
    -- literals are all rejected; the offending parameter is carried as
    -- the error's source context. The type definition is dropped.
    InvalidTypeParameter
  | -- | The same variable appears more than once in a type
    -- definition's parameter list. The type definition is dropped.
    DuplicateTypeParameter Text
  | -- | A bound signature inside a @requiring@ clause does not have the
    -- expected @name(τ₁, …, τₙ) -> τᵣ@ shape. The enclosing declaration
    -- is dropped.
    MalformedBoundSig
  | -- | A @:- extend_function@ / @:- extend_class@ payload, or a
    -- top-level equation, does not have the expected
    -- @lhs [| guard] -> rhs@ shape. The equation is dropped.
    MalformedFunctionEquation
  | -- | A top-level term is neither a directive, a rule
    -- (@\<=\>@/@==\>@), nor a function equation. The item is dropped.
    MalformedTopLevel
  | -- | More than one @:- module(...)@ directive in the same file.
    -- Only one module header is allowed per source file. The first
    -- header is treated as authoritative; one diagnostic is emitted
    -- per redundant header, carrying its module name.
    DuplicateModuleHeader Text
  | -- | A @requiring@ clause appears on a @:- class@ or
    -- @:- open_class@ declaration. @requiring@ is reserved for
    -- @:- function@ / @:- open_function@; the two forms are
    -- intentionally orthogonal. Carries the class's name.
    RequiringOnClass Text
  | -- | A @requiring@ clause appears on a @:- extend_class_type@
    -- directive. Bounds are part of the original declaration; an
    -- extension cannot introduce them. Carries the extension target's
    -- name.
    RequiringOnExtendClassType Text
  | -- | A @refining@ clause appears on a @:- chr_constraint@
    -- declaration. Only a function can be a refinement predicate. The
    -- declaration is dropped.
    RefiningOnConstraint
  | -- | A macro clause's head, or a @:- macro Name\/N@ declaration, is
    -- not an atom or compound named by an unqualified atom that is not
    -- a reserved symbol (@,@, @;@, @\\@, @|@, @->@, @=@, @is@, @true@,
    -- @quote@, @fun@, @'$call'@, @tell@, @'$compound'@, @'$atom'@), or a
    -- @:- macro@ directive has neither shape. The clause or declaration
    -- is dropped.
    MalformedMacroHead
  | -- | A macro clause's body is not a list literal with no tail
    -- variable. The clause is dropped.
    MalformedMacroBody
  | -- | A top-level @Head ---> Body@ clause whose @Name\/N@ is not
    -- declared as a macro in its module (neither by @:- macro Name\/N@
    -- nor by a one-line definition). Carries the name and arity. The
    -- clause is dropped.
    UndeclaredMacroClause Text Int
  | -- | The clauses of one macro do not form one contiguous block of
    -- module items. Carries the name and arity.
    DiscontiguousMacroClauses Text Int
  | -- | A declaration macro has the name and arity of a built-in
    -- directive ('builtinDirectives'). Name and arity. The definition
    -- is dropped.
    DeclMacroBuiltinDirective Text Int
  | -- | A built-in directive with arguments of the wrong shape, e.g.
    -- @:- module(42).@ Carries the directive's name.
    MalformedDirective Text
  deriving (Eq, Show)

-- | Convert a list of top-level PExpr terms to a 'Module', along with
-- any validation errors (discontiguous equations, malformed imports,
-- malformed constraints).
--
-- Items whose conversion fails entirely are dropped from the resulting
-- module; their errors are still returned.
convertModule :: Text -> [Ann PExpr] -> Converted Module
convertModule defaultName terms =
  let items = [SourceItem t [] | t <- terms]
      (m, errs) = runWriter (convertSourceItems defaultName items)
   in Converted m [e.parseError | e <- errs]

-- | A top-level term to convert, with the macro chain that generated
-- it (empty if the user wrote it).
data SourceItem = SourceItem
  { term :: Ann PExpr,
    expansion :: [ExpansionStep]
  }

-- | A conversion error with the macro chain of its item.
data ChainedError = ChainedError
  { -- | The error.
    parseError :: AnnP ParseValidationError,
    -- | The macro chain of the item (empty if the user wrote it).
    expansion :: [ExpansionStep]
  }

-- | 'convertModule' for terms with a chain. Rules and equations keep
-- their item's chain, and each error comes with it. Module-wide errors
-- (contiguity, macro grouping, duplicate headers) get no chain.
convertSourceItems :: Text -> [SourceItem] -> Writer [ChainedError] Module
convertSourceItems defaultName srcItems = do
  items <- catMaybes <$> traverse convertItem srcItems
  let dirs = [d | ItemDirective d <- items]
      moduleDirs = [md | DirModule md <- dirs]
      header = listToMaybe moduleDirs
      (modMacros_, macroErrors) = runWriter (groupMacroClauses items)
      openNames =
        Set.fromList $
          [fd.name | DirOpenFunctionDecl ds <- dirs, Ann (FunctionDecl fd) _ <- ds]
            ++ [fd.name | DirOpenClassDecl ds <- dirs, Ann (FunctionDecl fd) _ <- ds]
      duplicateModuleHeaderErrors =
        [AnnP (DuplicateModuleHeader md.name) md.loc md.origin | md <- drop 1 moduleDirs]
  tell
    [ ChainedError e []
    | e <- checkContiguity openNames items ++ macroErrors ++ duplicateModuleHeaderErrors
    ]
  pure
    Module
      { name = maybe defaultName (.name) header,
        nameLoc = maybe dummyLoc (.loc) header,
        imports = [n | DirImport n <- dirs],
        decls =
          concat [ds | DirConstraintDecl ds <- dirs]
            ++ concat [ds | DirFunctionDecl ds <- dirs]
            ++ concat [ds | DirOpenFunctionDecl ds <- dirs]
            ++ concat [ds | DirClassDecl ds <- dirs]
            ++ concat [ds | DirOpenClassDecl ds <- dirs],
        extensionTypes = concat [ds | DirExtendClassTypeDecl ds <- dirs],
        typeDecls = concat [ds | DirTypeDecl ds <- dirs],
        rules = [r | ItemRule r <- items],
        equations = [e | ItemEquation e <- items],
        extensions = [e | DirExtendFunctionEqn e <- dirs],
        classExtensions = [e | DirExtendClassEqn e <- dirs],
        inlines = concat [ds | DirInlineDecl ds <- dirs],
        constraintUses = concat [ds | DirConstraintUseDecl ds <- dirs],
        macros = modMacros_,
        exports = do
          md <- header
          decls <- md.exports
          pure (AnnP decls md.loc md.origin)
      }
  where
    convertItem si = do
      let (mi, errs) = runWriter (convertModuleItem si.term)
      tell [ChainedError e si.expansion | e <- errs]
      pure (withExpansion si.expansion <$> mi)

-- | Put a chain on an item's rules and equations.
withExpansion :: [ExpansionStep] -> ModuleItem -> ModuleItem
withExpansion [] item = item
withExpansion chain item = case item of
  ItemRule r -> ItemRule (setRule r)
  ItemEquation e -> ItemEquation (setEq <$> e)
  ItemDirective (DirExtendFunctionEqn e) ->
    ItemDirective (DirExtendFunctionEqn (setEq <$> e))
  ItemDirective (DirExtendClassEqn e) ->
    ItemDirective (DirExtendClassEqn (setEq <$> e))
  _ -> item
  where
    -- Positional: a record update of 'expansion' would be ambiguous
    -- (several records have it).
    setRule (Rule n h g b _) = Rule n h g b chain
    setEq (FunctionEquation f as g rhs _) = FunctionEquation f as g rhs chain

-- | Read just the name, exports, imports and macros of a module from
-- its terms. Errors are ignored here; full conversion reports them.
scanModuleTerms :: Text -> [Ann PExpr] -> Module
scanModuleTerms defaultName terms =
  (convertModule defaultName (filter relevant terms)).value
  where
    relevant t = case t.node of
      Compound ":-" [Ann body _] -> case body of
        Compound n _ -> n `elem` ["module", "use_module", "macro", "macro_decls"]
        _ -> False
      Compound "--->" [_, _] -> True
      _ -> False

-- | Built-in directives (name, arity). Any other directive is a
-- declaration-macro use. Declaration macros can't use these keys.
builtinDirectives :: Set UnqualifiedIdentifier
builtinDirectives =
  Set.fromList
    [ UnqualifiedIdentifier "module" 1,
      UnqualifiedIdentifier "module" 2,
      UnqualifiedIdentifier "use_module" 1,
      UnqualifiedIdentifier "use_module" 2,
      UnqualifiedIdentifier "chr_constraint" 1,
      UnqualifiedIdentifier "chr_type" 1,
      UnqualifiedIdentifier "opaque_type" 1,
      UnqualifiedIdentifier "function" 1,
      UnqualifiedIdentifier "open_function" 1,
      UnqualifiedIdentifier "class" 1,
      UnqualifiedIdentifier "open_class" 1,
      UnqualifiedIdentifier "extend_function" 1,
      UnqualifiedIdentifier "extend_class" 1,
      UnqualifiedIdentifier "extend_class_type" 1,
      UnqualifiedIdentifier "inline" 1,
      UnqualifiedIdentifier "constraint_use" 1,
      UnqualifiedIdentifier "macro" 1,
      UnqualifiedIdentifier "macro_decls" 1
    ]

-- | Name of a directive's term (empty if it has none).
directiveName :: PExpr -> Text
directiveName body = case body of
  Atom n -> n
  Compound n _ -> n
  _ -> ""

-- | Is @T@ in @:- T@ a built-in directive?
isBuiltinDirective :: PExpr -> Bool
isBuiltinDirective body = case body of
  Atom n -> Set.member (UnqualifiedIdentifier n 0) builtinDirectives
  Compound n args ->
    Set.member (UnqualifiedIdentifier n (length args)) builtinDirectives
  _ -> False

-- | Group a module's macro definitions and clauses into 'MacroDef's.
--
-- * A one-line definition is a macro of its own, with one clause.
-- * A @:- macro Name\/N@ declaration takes every top-level clause of
--   the same @Name\/N@, in source order, wherever the clauses are. A
--   second declaration of the same key gets no clauses: the renamer
--   reports it as 'YCHR.Internal.Rename.DuplicateMacro'.
-- * Clauses with no declaration but the key of a one-line definition
--   form a further 'MacroDef', anchored at the first of them and placed
--   after every one-line definition, so that the renamer keeps the
--   one-line definition and reports the clauses as
--   'YCHR.Internal.Rename.DuplicateMacro': a one-line definition cannot
--   have further clauses.
-- * Any other clause is 'UndeclaredMacroClause', and is dropped.
groupMacroClauses :: [ModuleItem] -> Conv [AnnP MacroDef]
groupMacroClauses items = do
  tell undeclared
  tell builtinNameErrors
  pure (filter allowed (defined ++ orphanDefs))
  where
    declaredKeys =
      Set.fromList [UnqualifiedIdentifier k.node.name k.node.arity | k <- decls]
    decls = concat [ks | ItemDirective (DirMacroDecl ks) <- items]
    oneLineDefs = [d | ItemDirective (DirMacro d) <- items]
    oneLineKeys =
      Set.fromList [UnqualifiedIdentifier d.node.name d.node.arity | d <- oneLineDefs]
    clauses = [nc | ItemMacroClause nc <- items]
    clausesOf k = [nc.clause | nc <- clauses, clauseKey nc == k]

    -- One-line definitions ('Left') and declared keys ('Right'), in
    -- item order.
    entries =
      concat
        [ case d of
            DirMacro def -> [Left def]
            DirMacroDecl ks -> map Right ks
            _ -> []
        | ItemDirective d <- items
        ]

    -- Definitions and declarations in item order; a repeated
    -- declaration gets no clauses.
    defined = goDefs Set.empty entries
    goDefs _ [] = []
    goDefs seen (Left d : rest) = d : goDefs seen rest
    goDefs seen (Right (AnnP k l p) : rest) =
      let key = UnqualifiedIdentifier k.name k.arity
          cs = if Set.member key seen then [] else clausesOf key
       in AnnP (MacroDef k.kind k.name k.arity cs) l p : goDefs (Set.insert key seen) rest

    -- A declaration macro can't take a built-in directive's key. Drop
    -- it (and any extra clauses); its clauses still count as declared.
    isBuiltinDeclMacro d =
      d.kind == DeclMacro
        && Set.member (UnqualifiedIdentifier d.name d.arity) builtinDirectives
    allowed d = not (isBuiltinDeclMacro d.node)
    builtinNameErrors =
      [ AnnP (DeclMacroBuiltinDirective d.node.name d.node.arity) d.sourceLoc d.parsed
      | d <- defined,
        isBuiltinDeclMacro d.node
      ]

    orphanKeys =
      nubOrd
        [ k
        | nc <- clauses,
          let k = clauseKey nc,
          Set.notMember k declaredKeys,
          Set.member k oneLineKeys
        ]
    -- Clauses for a one-line definition take its kind.
    oneLineKind k =
      case [ d.node.kind
           | d <- oneLineDefs,
             UnqualifiedIdentifier d.node.name d.node.arity == k
           ] of
        (kd : _) -> kd
        [] -> GoalMacro
    orphanDefs =
      [ AnnP (MacroDef (oneLineKind k) n a cs) first.sourceLoc first.parsed
      | k@(UnqualifiedIdentifier n a) <- orphanKeys,
        cs@(first : _) <- [clausesOf k]
      ]
    undeclared =
      [ AnnP
          (UndeclaredMacroClause k.localName k.arity)
          nc.clause.sourceLoc
          nc.clause.parsed
      | nc <- clauses,
        let k = clauseKey nc,
        Set.notMember k declaredKeys,
        Set.notMember k oneLineKeys
      ]
    nubOrd = go Set.empty
      where
        go _ [] = []
        go sn (x : xs)
          | Set.member x sn = go sn xs
          | otherwise = x : go (Set.insert x sn) xs

-- | Check that equations for non-open functions are contiguous.
-- Returns an error for each function whose equations are separated by
-- other items.
checkContiguity :: Set Text -> [ModuleItem] -> [AnnP ParseValidationError]
checkContiguity openNames items =
  checkEquationContiguity openNames items
    ++ checkDeclContiguity openNames items
    ++ checkMacroClauseContiguity items

-- | Macro-clause contiguity: the top-level clauses of one macro
-- (same name and arity) must form one contiguous block of module
-- items, as the equations of a closed function do. Reports the clause
-- that reopens a block that has already ended.
checkMacroClauseContiguity :: [ModuleItem] -> [AnnP ParseValidationError]
checkMacroClauseContiguity = go Set.empty Nothing
  where
    go _closed _prev [] = []
    go closed prev (ItemMacroClause nc : rest) =
      let k = clauseKey nc
          c = nc.clause
       in case prev of
            Just p | p == k -> go closed prev rest
            _ ->
              let closed' = maybe closed (`Set.insert` closed) prev
                  errs =
                    [ AnnP
                        (DiscontiguousMacroClauses k.localName k.arity)
                        c.sourceLoc
                        c.parsed
                    | k `Set.member` closed'
                    ]
               in errs ++ go closed' (Just k) rest
    go closed prev (_ : rest) =
      go (maybe closed (`Set.insert` closed) prev) Nothing rest

-- | Equation contiguity: equations for the same non-open function name
-- must be a contiguous block of module items.
checkEquationContiguity ::
  Set Text -> [ModuleItem] -> [AnnP ParseValidationError]
checkEquationContiguity openNames = go Set.empty Nothing
  where
    -- closed: function names whose equation block has ended.
    -- prev: the function name of the immediately preceding equation (if any).
    go _closed _prev [] = []
    go closed prev (ItemEquation annEq : rest) =
      let n = eqName annEq.node.funName
       in if n `Set.member` openNames
            then go closed prev rest
            else case prev of
              Just p | p == n -> go closed prev rest -- still contiguous
              _ ->
                let closed' = maybe closed (`Set.insert` closed) prev
                 in if n `Set.member` closed'
                      then
                        AnnP (DiscontiguousEquations n) annEq.sourceLoc annEq.parsed
                          : go closed' (Just n) rest
                      else go closed' (Just n) rest
    go closed prev (_ : rest) =
      go (maybe closed (`Set.insert` closed) prev) Nothing rest

    eqName (Unqualified n) = n
    eqName (Qualified _ n) = n

-- | Declaration contiguity: @:- function@ (and @:- open_function@)
-- directives for the same non-open function name must be a contiguous
-- block of module items. Decls inside a single directive (e.g.
-- @:- function f\/1, g\/1.@) count as one block per function and do
-- not close each other.
checkDeclContiguity ::
  Set Text -> [ModuleItem] -> [AnnP ParseValidationError]
checkDeclContiguity openNames = go Set.empty Set.empty
  where
    -- closed: function names whose decl block has ended.
    -- active: function names declared by the immediately preceding decl
    -- directive (still contiguous).
    go _closed _active [] = []
    go closed active (ItemDirective dir : rest)
      | Just ds <- declListOf dir =
          let names = [Ann fd.name loc | Ann (FunctionDecl fd) loc <- ds]
              nonOpenNames = [n.node | n <- names, n.node `Set.notMember` openNames]
              reopened =
                [ noAnnPAt loc (DiscontiguousFunctionDecls n)
                | Ann n loc <- names,
                  n `Set.notMember` openNames,
                  n `Set.member` closed,
                  n `Set.notMember` active
                ]
              active' = Set.fromList nonOpenNames `Set.union` active
           in reopened ++ go closed active' rest
    go closed active (_ : rest) =
      go (active `Set.union` closed) Set.empty rest

    declListOf (DirFunctionDecl ds) = Just ds
    declListOf (DirOpenFunctionDecl ds) = Just ds
    declListOf (DirClassDecl ds) = Just ds
    declListOf (DirOpenClassDecl ds) = Just ds
    declListOf _ = Nothing

-- | Classify and convert a single top-level PExpr, collecting any errors
-- raised during conversion. Returns 'Nothing' if the term does not denote
-- a recognized top-level item; a 'MalformedTopLevel' error is emitted
-- in that case.
convertModuleItem :: Ann PExpr -> Conv (Maybe ModuleItem)
convertModuleItem expr = case expr.node of
  -- Directive: :- body
  Compound ":-" [_] -> Just . ItemDirective <$> convertDirective expr
  -- Named rule: name @ ...
  Compound "@" [_, Ann (Compound "<=>" _) _] -> ruleItem
  Compound "@" [_, Ann (Compound "==>" _) _] -> ruleItem
  -- Unnamed rule
  Compound "<=>" _ -> ruleItem
  Compound "==>" _ -> ruleItem
  -- Macro clause: Head ---> [Goals]. Grouped with its declaration by
  -- 'groupMacroClauses'.
  Compound "--->" [_, _] -> fmap ItemMacroClause <$> convertMacroClause expr
  -- Function equation (contains -> at top level)
  Compound "->" _ -> fmap ItemEquation <$> convertFunctionEquation expr
  -- Anything else at top level is malformed.
  _ -> failWith (AnnP MalformedTopLevel expr.sourceLoc expr.node)
  where
    ruleItem = fmap ItemRule <$> convertRule expr

-- ** Directive conversion

-- | Convert a directive PExpr to a 'Directive', collecting any errors
-- raised during conversion. Malformed sub-items (declarations, equations,
-- export items) are dropped and reported via 'ParseValidationError's.
convertDirective :: Ann PExpr -> Conv Directive
convertDirective (Ann (Compound ":-" [body]) loc) = case body.node of
  -- :- module(name, [exports]).
  Compound "module" [Ann (Atom name) _, exports] -> do
    decls <- collectList convertExportItem (unfoldList exports.node)
    pure (DirModule (ModuleDirective name loc body.node (Just decls)))
  -- :- module(name).  (no export list — exports everything)
  Compound "module" [Ann (Atom name) _] ->
    pure (DirModule (ModuleDirective name loc body.node Nothing))
  -- :- use_module(name).  or  :- use_module(library(name)).
  Compound "use_module" [imp, importList] ->
    maybe DirOther DirImport <$> convertImportWithList loc body.node imp importList
  Compound "use_module" [imp] ->
    case convertImport loc body.node imp of
      Right ann -> pure (DirImport ann)
      Left err -> DirOther <$ tell [err]
  -- :- chr_constraint leq/2, fib/2.
  -- Parsed as prefix op: Compound "chr_constraint" [body]
  Compound "chr_constraint" [decls] ->
    DirConstraintDecl <$> collectDecls convertConstraintDecl decls
  -- :- function foo/2.  or  :- function factorial(int) -> int.
  Compound "function" [decls] ->
    DirFunctionDecl <$> collectDecls convertFunctionDecl decls
  -- :- open_function foo/2.
  Compound "open_function" [decls] ->
    DirOpenFunctionDecl <$> collectDecls convertOpenFunctionDecl decls
  -- :- class size(int) -> int.  or  :- class (size(int) -> int), (size(string) -> int).
  Compound "class" [decls] -> do
    decls' <- collectDecls convertClassDecl decls
    tell (requiringOnClassErrors loc body.node decls')
    pure (DirClassDecl decls')
  -- :- open_class size(int) -> int.
  Compound "open_class" [decls] -> do
    decls' <- collectDecls convertOpenClassDecl decls
    tell (requiringOnClassErrors loc body.node decls')
    pure (DirOpenClassDecl decls')
  -- :- inline double/1, succ/1.
  Compound "inline" [decls] ->
    DirInlineDecl <$> collectDecls convertInlineDecl decls
  -- :- constraint_use fact(log/2), event(click/1).
  Compound "constraint_use" [decls] ->
    DirConstraintUseDecl <$> collectDecls convertConstraintUseDecl decls
  -- :- extend_class_type (foo(int) -> int).
  Compound "extend_class_type" [decls] ->
    DirExtendClassTypeDecl <$> collectDecls convertExtendClassTypeDecl decls
  -- :- extend_function name(args) [| guards] -> body.
  Compound "extend_function" [eqn] ->
    maybe DirOther DirExtendFunctionEqn <$> convertFunctionEquation eqn
  -- :- extend_class name(args) [| guards] -> body.
  Compound "extend_class" [eqn] ->
    maybe DirOther DirExtendClassEqn <$> convertFunctionEquation eqn
  -- :- chr_type name ---> con1 ; con2 ; ...
  -- Parsed as prefix op: Compound "chr_type" [Compound "--->" [head, alts]]
  Compound "chr_type" [typeBody] ->
    maybe DirOther (DirTypeDecl . pure) <$> convertTypeDefinition typeBody
  -- :- opaque_type name(Vars).
  -- Parsed as prefix op (1180): Compound "opaque_type" [head]. A
  -- constructor body @---> ...@ (1150) nests inside as
  -- Compound "opaque_type" [Compound "--->" [..]] and is rejected by
  -- 'convertOpaqueTypeDefinition'.
  Compound "opaque_type" [typeBody] ->
    maybe DirOther (DirTypeDecl . pure) <$> convertOpaqueTypeDefinition typeBody
  -- :- macro Name/N, ...  or  :- macro_decls Name/N, ...
  -- (a declaration; the clauses are top-level items)
  Compound kw [decls@(Ann (Compound "/" [_, _]) _)]
    | Just k <- macroKeyword kw -> macroDecls k decls
  Compound kw [decls@(Ann (Compound "," [Ann (Compound "/" [_, _]) _, _]) _)]
    | Just k <- macroKeyword kw -> macroDecls k decls
  -- :- macro Head ---> [Goals].  or  :- macro_decls Head ---> [Clauses].
  -- (a one-line definition). Parsed as prefix op:
  -- Compound "macro" [Compound "--->" [head, body]]
  Compound kw [macroBody@(Ann (Compound "--->" [_, _]) _)]
    | Just k <- macroKeyword kw ->
        maybe DirOther (macroDef k) <$> convertMacroClause macroBody
  Compound kw [other]
    | Just _ <- macroKeyword kw ->
        DirOther <$ tell [AnnP MalformedMacroHead other.sourceLoc other.node]
  -- A built-in directive in a shape we don't know, e.g. @:- module(42).@
  -- Report it, or it would vanish.
  _
    | isBuiltinDirective body.node ->
        let err = MalformedDirective (directiveName body.node)
         in DirOther <$ tell [AnnP err loc body.node]
  -- Anything else is a macro use or unknown. "YCHR.Internal.DeclMacro"
  -- handles both before this; here we just skip them.
  _ -> pure DirOther
  where
    macroKeyword :: Text -> Maybe MacroKind
    macroKeyword "macro" = Just GoalMacro
    macroKeyword "macro_decls" = Just DeclMacro
    macroKeyword _ = Nothing
    macroDecls k decls = DirMacroDecl <$> collectList (macroKey k) (flattenComma decls)
    macroKey k (Ann d dloc) = case d of
      Compound "/" [Ann (Atom name) _, Ann (P.Int arity) _]
        | Set.notMember name reservedMacroHeadNames,
          arity >= 0 ->
            pure (Just (AnnP (MacroKey k name (fromInteger arity)) loc body.node))
      _ -> failWith (AnnP MalformedMacroHead dloc d)
    macroDef k nc =
      let c = nc.clause
          def = MacroDef k nc.name (length c.node.params) [c]
       in DirMacro (AnnP def c.sourceLoc c.parsed)
convertDirective _ = pure DirOther

-- | Run a per-declaration converter over a comma-separated declaration
-- list, dropping declarations that failed conversion.
collectDecls :: (Ann PExpr -> Conv (Maybe (Ann a))) -> Ann PExpr -> Conv [Ann a]
collectDecls conv = collectList conv . flattenComma

-- | Convert each element, dropping the ones that failed.
collectList :: (Ann PExpr -> Conv (Maybe a)) -> [Ann PExpr] -> Conv [a]
collectList conv = fmap catMaybes . traverse conv

-- | Convert an import PExpr (use_module/1, imports everything).
-- Returns 'Left' with a 'MalformedImport' error if the argument is not a
-- module name or @library(name)@.
convertImport ::
  SourceLoc ->
  PExpr ->
  Ann PExpr ->
  Either (AnnP ParseValidationError) (AnnP Import)
convertImport dirLoc dirPExpr (Ann pexpr loc) = case pexpr of
  Compound "library" [Ann (Atom name) _] ->
    Right (AnnP (LibraryImport name Nothing) dirLoc dirPExpr)
  Atom name -> Right (AnnP (ModuleImport name Nothing) dirLoc dirPExpr)
  _ -> Left (AnnP MalformedImport loc pexpr)

-- | Convert an import PExpr with an explicit import list (use_module/2).
-- Reports a 'MalformedImport' error if the import target is not a module
-- name or @library(name)@. On success, also reports any
-- 'MalformedExportItem' errors from items inside the import list.
convertImportWithList ::
  SourceLoc ->
  PExpr ->
  Ann PExpr ->
  Ann PExpr ->
  Conv (Maybe (AnnP Import))
convertImportWithList dirLoc dirPExpr imp importList = case imp.node of
  Compound "library" [Ann (Atom name) _] -> do
    items <- importItems
    pure (Just (AnnP (LibraryImport name (Just items)) dirLoc dirPExpr))
  Atom name -> do
    items <- importItems
    pure (Just (AnnP (ModuleImport name (Just items)) dirLoc dirPExpr))
  _ -> failWith (AnnP MalformedImport imp.sourceLoc imp.node)
  where
    importItems = collectList convertExportItem (unfoldList importList.node)

-- | Report a 'RequiringOnClass' error for every declaration inside a
-- @:- class@ or @:- open_class@ directive that carries a @requiring@
-- clause. Bounded polymorphism is reserved for @:- function@ /
-- @:- open_function@; the two forms are intentionally orthogonal.
-- The shared location and origin come from the surrounding directive
-- so the diagnostic points at the whole @:- class@.
requiringOnClassErrors ::
  SourceLoc -> PExpr -> [Ann Declaration] -> [AnnP ParseValidationError]
requiringOnClassErrors loc origin decls =
  [ AnnP (RequiringOnClass fd.name) loc origin
  | Ann (FunctionDecl fd) _ <- decls,
    isJust fd.requiring
  ]

-- | Convert an export item PExpr to a 'Declaration'. Items whose shape
-- is not recognized are dropped with a 'MalformedExportItem' error.
--
-- For @type(name\/arity, [con1, …])@ the constructor list is validated
-- strictly: a non-list argument or any non-atom element causes the
-- entire export item to be dropped, with one 'MalformedExportItem'
-- error per offending position. Dropping (rather than salvaging the
-- well-formed atoms) keeps the parser uniform with the rest of the
-- malformed-input policy, and avoids accidentally widening or
-- narrowing the constructor allowlist relative to what the user wrote.
convertExportItem :: Ann PExpr -> Conv (Maybe Declaration)
convertExportItem (Ann pexpr loc) = case pexpr of
  Compound "fun" [Ann (Compound "/" [Ann (Atom name) _, Ann (P.Int arity) _]) _] ->
    pure
      ( Just
          ( FunctionDecl
              FunctionDeclBody
                { name,
                  arity = fromInteger arity,
                  argTypes = Nothing,
                  returnType = Nothing,
                  isOpen = False,
                  kind = DKFunction,
                  requiring = Nothing,
                  refining = Nothing
                }
          )
      )
  Compound "/" [Ann (Atom name) _, Ann (P.Int arity) _] ->
    pure
      (Just (ConstraintDecl (ConstraintDeclBody name (fromInteger arity) Nothing Nothing)))
  Compound "macro" [Ann (Compound "/" [Ann (Atom name) _, Ann (P.Int arity) _]) _] ->
    pure (Just (MacroExportDecl (MacroExportDeclBody name (fromInteger arity))))
  Compound "op" [Ann (P.Int fix) _, Ann tyExpr _, Ann nameExpr _]
    | Just ty <- parseOpTypeFromPExpr tyExpr,
      Just name <- atomName nameExpr ->
        pure (Just (OperatorDecl (OpDecl (fromInteger fix) ty name)))
  -- @type(name/arity)@ — covers both algebraic and opaque types (they
  -- share one type namespace).
  Compound "type" [Ann (Compound "/" [Ann (Atom name) _, Ann (P.Int arity) _]) _] ->
    pure (Just (TypeExportDecl (TypeExportDeclBody name (fromInteger arity) Nothing)))
  Compound "type" [spec, conList]
    | Compound "/" [Ann (Atom name) _, Ann (P.Int arity) _] <- spec.node ->
        case unfoldListStrict conList.node of
          Nothing -> failWith (AnnP MalformedExportItem conList.sourceLoc conList.node)
          Just items -> case partitionEithers (map atomElement items) of
            ([], names) ->
              pure
                ( Just
                    ( TypeExportDecl
                        (TypeExportDeclBody name (fromInteger arity) (Just names))
                    )
                )
            (errs, _) -> failWithAll errs
  _ -> failWith (AnnP MalformedExportItem loc pexpr)
  where
    atomElement (Ann (Atom n) _) = Right n
    atomElement (Ann e l) = Left (AnnP MalformedExportItem l e)

-- | Convert a PExpr to a constraint declaration. Returns 'Nothing' and
-- a 'MalformedDeclaration' (or 'MalformedTypeExpr' / 'MalformedBoundSig'
-- from sub-conversions) error if the declaration cannot be converted.
convertConstraintDecl :: Ann PExpr -> Conv (Maybe (Ann Declaration))
convertConstraintDecl (Ann pexpr loc) = case pexpr of
  -- @sig requiring bound, ...@
  Compound "requiring" [sig, bounds] -> case sig.node of
    Compound name args ->
      let (argTypeErrs, argTypes) = partitionEithers (map convertTypeExpr args)
          (boundErrs, bs) =
            partitionEithers (map convertBoundSig (flattenComma bounds))
       in case argTypeErrs ++ boundErrs of
            [] ->
              found
                (ConstraintDeclBody name (length args) (Just argTypes) (Just bs))
            errs -> failWithAll errs
    _ -> failWith (AnnP MalformedDeclaration loc pexpr)
  -- Untyped: name/arity
  Compound "/" [Ann (Atom name) _, Ann (P.Int arity) _] ->
    found (ConstraintDeclBody name (fromInteger arity) Nothing Nothing)
  -- @refining@ is an operator word, so @c(any) refining int@ parses as
  -- a compound named @refining@ at arity 2 — indistinguishable from a
  -- constraint literally named @refining@ with two arguments. Only a
  -- function can be a refinement predicate, so the shape is rejected
  -- before the generic arm below, which would otherwise declare it.
  -- Any other arity cannot come from the operator and is left alone.
  Compound "refining" [_, _] -> failWith (AnnP RefiningOnConstraint loc pexpr)
  -- Typed: name(type, ...)
  Compound name args -> case partitionEithers (map convertTypeExpr args) of
    ([], argTypes) ->
      found (ConstraintDeclBody name (length args) (Just argTypes) Nothing)
    (errs, _) -> failWithAll errs
  -- Zero-arity bare atom
  Atom name -> found (ConstraintDeclBody name 0 Nothing Nothing)
  _ -> failWith (AnnP MalformedDeclaration loc pexpr)
  where
    found body = pure (Just (Ann (ConstraintDecl body) loc))

-- | Convert one @name\/arity@ entry of an @:- inline@ directive.
convertInlineDecl :: Ann PExpr -> Conv (Maybe (Ann InlineDecl))
convertInlineDecl (Ann pexpr loc) = case pexpr of
  Compound "/" [Ann (Atom name) _, Ann (P.Int arity) _] ->
    pure (Just (Ann (InlineDecl name (fromInteger arity)) loc))
  _ -> failWith (AnnP MalformedDeclaration loc pexpr)

-- | Convert one @Tag(name\/arity)@ entry of a @:- constraint_use@
-- directive. The tag must be one of the four modes, applied to exactly
-- one @name\/arity@.
convertConstraintUseDecl :: Ann PExpr -> Conv (Maybe (Ann ConstraintUseDecl))
convertConstraintUseDecl (Ann pexpr loc) = case pexpr of
  Compound tag [Ann (Compound "/" [Ann (Atom name) _, Ann (P.Int arity) _]) _]
    | Just use <- constraintUseTag tag ->
        pure (Just (Ann (ConstraintUseDecl use name (fromInteger arity)) loc))
  _ -> failWith (AnnP MalformedDeclaration loc pexpr)
  where
    constraintUseTag :: Text -> Maybe ConstraintUse
    constraintUseTag t = case t of
      "any" -> Just UseAny
      "fact" -> Just UseFact
      "event" -> Just UseEvent
      "tell_only" -> Just UseTellOnly
      _ -> Nothing

-- | Convert a PExpr to a closed-function declaration.
convertFunctionDecl :: Ann PExpr -> Conv (Maybe (Ann Declaration))
convertFunctionDecl = convertFunctionDeclWith False DKFunction

-- | Convert a PExpr to an open-function declaration.
convertOpenFunctionDecl :: Ann PExpr -> Conv (Maybe (Ann Declaration))
convertOpenFunctionDecl = convertFunctionDeclWith True DKFunction

-- | Convert a PExpr to a closed-class declaration.
convertClassDecl :: Ann PExpr -> Conv (Maybe (Ann Declaration))
convertClassDecl = convertFunctionDeclWith False DKClass

-- | Convert a PExpr to an open-class declaration.
convertOpenClassDecl :: Ann PExpr -> Conv (Maybe (Ann Declaration))
convertOpenClassDecl = convertFunctionDeclWith True DKClass

-- | Convert a PExpr to an extension type declaration. Targets
-- @:- open_class@ declarations and adds an overloaded signature.
-- Only the typed form @name(types) -> type@ is supported.
--
-- A @requiring@ clause on an @:- extend_class_type@ is rejected
-- syntactically: bounds belong to the original declaration, not to
-- an extension. The inner signature is still converted so that any
-- sub-errors (malformed type expressions) are reported alongside the
-- 'RequiringOnExtendClassType' error.
convertExtendClassTypeDecl :: Ann PExpr -> Conv (Maybe (Ann Declaration))
convertExtendClassTypeDecl (Ann pexpr loc) = case pexpr of
  -- @requiring@ is Xfx, so the inner @sig@ is never another @requiring@.
  Compound "requiring" [sig, _] -> do
    let targetName = case sig.node of
          Compound "->" [Ann (Compound n _) _, _] -> n
          _ -> "<unknown>"
    tell [AnnP (RequiringOnExtendClassType targetName) loc pexpr]
    convertSig sig
  _ -> convertSig (Ann pexpr loc)
  where
    convertSig (Ann e l) = case e of
      Compound "->" [Ann (Compound name args) _, ret] ->
        case (partitionEithers (map convertTypeExpr args), convertTypeExpr ret) of
          (([], argTypes), Right retType) ->
            pure
              ( Just
                  ( Ann
                      ( ExtendClassTypeDecl
                          ( ExtendClassTypeDeclBody
                              name
                              (length args)
                              (Just argTypes)
                              (Just retType)
                              Nothing
                          )
                      )
                      l
                  )
              )
          ((argErrs, _), retE) -> failWithAll (argErrs ++ leftToList retE)
      _ -> failWith (AnnP MalformedDeclaration l e)

-- | Shared implementation of 'convertFunctionDecl',
-- 'convertOpenFunctionDecl', 'convertClassDecl' and
-- 'convertOpenClassDecl'. The 'Bool' argument is the @open@ flag and
-- the 'FunctionDeclKind' selects between @:- function@ and @:- class@.
-- Malformed declarations are dropped and reported via errors.
convertFunctionDeclWith ::
  Bool ->
  FunctionDeclKind ->
  Ann PExpr ->
  Conv (Maybe (Ann Declaration))
convertFunctionDeclWith open kind (Ann pexpr loc) = case pexpr of
  -- @name(types) -> ret requiring bound, ...@
  Compound "requiring" [sig, bounds] ->
    let (boundErrs, bs) =
          partitionEithers (map convertBoundSig (flattenComma bounds))
     in case typedCore sig of
          Left errs -> failWithAll (errs ++ boundErrs)
          Right core
            | null boundErrs -> found (withClauses core (Just bs) Nothing)
            | otherwise -> failWithAll boundErrs
  -- @name(any) -> bool refining type@. The untyped core is accepted
  -- here so that Resolve can reject it as an invalid @refining@ clause
  -- (YCHR-16021) rather than a bare syntax error.
  Compound "refining" [core, ty] ->
    let tyResult = convertTypeExpr ty
     in case (anyCore core, tyResult) of
          (Left errs, _) -> failWithAll (errs ++ leftToList tyResult)
          (Right _, Left err) -> failWith err
          (Right c, Right t) -> found (withClauses c Nothing (Just t))
  _ -> case anyCore (Ann pexpr loc) of
    Left errs -> failWithAll errs
    Right core -> found (FunctionDecl core)
  where
    malformed = [AnnP MalformedDeclaration loc pexpr]
    found decl = pure (Just (Ann decl loc))

    -- The core fields, with no @requiring@ / @refining@ clause yet.
    coreBody name arity argTypes returnType =
      FunctionDeclBody
        { name,
          arity,
          argTypes,
          returnType,
          isOpen = open,
          kind,
          requiring = Nothing,
          refining = Nothing
        }

    -- Add the two optional trailing clauses to a core.
    withClauses core requiring refining =
      FunctionDecl core {requiring, refining}

    -- The typed spelling @name(type, ...) -> type@.
    typedCore sig = case sig.node of
      Compound "->" [Ann (Compound name args) _, ret] ->
        case ( partitionEithers (map convertTypeExpr args),
               convertTypeExpr ret
             ) of
          (([], argTypes), Right retType) ->
            Right (coreBody name (length args) (Just argTypes) (Just retType))
          ((argErrs, _), retE) -> Left (argErrs ++ leftToList retE)
      _ -> Left malformed

    -- Either spelling: the untyped @name/arity@ or the typed one.
    anyCore core = case core.node of
      Compound "/" [Ann (Atom name) _, Ann (P.Int arity) _] ->
        Right (coreBody name (fromInteger arity) Nothing Nothing)
      _ -> typedCore core

-- | Lift a single 'Left' into a singleton list of errors, dropping the
-- 'Right' case. Used when threading 'Either'-based sub-conversion
-- results into an accumulating @[error]@ list.
leftToList :: Either e a -> [e]
leftToList = either pure (const [])

-- | Convert a single bound signature inside a @requiring@ clause. The
-- expected shape is @name(τ₁, ..., τₙ) -> τᵣ@; a bare @name -> τᵣ@ is
-- treated as a zero-arity bound. The name may be module-qualified
-- (@module:name(...) -> τᵣ@), same as any other reference. A malformed
-- shape (or a malformed type inside) is returned as 'Left'; the
-- enclosing declaration is then dropped.
--
-- See Note [Qualified name handling].
convertBoundSig :: Ann PExpr -> Either (AnnP ParseValidationError) BoundSig
convertBoundSig (Ann pexpr loc) = case pexpr of
  Compound "->" [Ann (Compound ":" [Ann (Atom m) _, Ann (Compound n args) _]) _, ret] ->
    build (Qualified m n) args ret
  Compound "->" [Ann (Compound ":" [Ann (Atom m) _, Ann (Atom n) _]) _, ret] ->
    build (Qualified m n) [] ret
  Compound "->" [Ann (Compound ":" _) _, _] -> Left (AnnP MalformedBoundSig loc pexpr)
  Compound "->" [Ann (Compound name args) _, ret] -> build (Unqualified name) args ret
  Compound "->" [Ann (Atom name) _, ret] -> build (Unqualified name) [] ret
  _ -> Left (AnnP MalformedBoundSig loc pexpr)
  where
    build name args ret = do
      argTypes <- traverse convertTypeExpr args
      returnType <- convertTypeExpr ret
      Right BoundSig {name, arity = length args, argTypes, returnType, loc}

-- | Convert a PExpr to a 'TypeExpr'.
--
-- Returns 'Left' with a 'MalformedTypeExpr' error when the input is not
-- a variable, atom, or compound term (e.g. a stray literal or string in
-- a type position).
--
-- See Note [Qualified name handling].
convertTypeExpr :: Ann PExpr -> Either (AnnP ParseValidationError) TypeExpr
convertTypeExpr (Ann pexpr loc) = case pexpr of
  Var t -> Right (TypeVar t)
  Atom "[]" -> Right (TypeCon (Unqualified "[]") [])
  Atom name -> Right (TypeCon (Unqualified name) [])
  Compound ":" [Ann (Atom m) _, Ann (Atom n) _] ->
    Right (TypeCon (Qualified m n) [])
  Compound ":" [Ann (Atom m) _, Ann (Compound n args) _] ->
    TypeCon (Qualified m n) <$> traverse convertTypeExpr args
  Compound "." args ->
    TypeCon (Unqualified ".") <$> traverse convertTypeExpr args
  Compound name args ->
    TypeCon (Unqualified name) <$> traverse convertTypeExpr args
  _ -> Left (AnnP MalformedTypeExpr loc pexpr)

-- | Convert a PExpr to a 'TypeDefinition'. Returns 'Nothing' and a
-- 'MalformedTypeDefinition' (or 'MalformedDataConstructor' /
-- 'MalformedTypeExpr' from sub-conversions) error if the definition
-- cannot be converted.
convertTypeDefinition :: Ann PExpr -> Conv (Maybe (Ann TypeDefinition))
convertTypeDefinition (Ann pexpr loc) = case pexpr of
  -- name(Vars) ---> con1 ; con2 ; ...
  Compound "--->" [typeHead, alts] -> case compoundView typeHead.node of
    Compound tname rawParams -> case validateTypeParams rawParams of
      Left errs -> failWithAll errs
      Right tvars ->
        case partitionEithers
          (map convertDataConstructor (flattenSemicolon alts)) of
          ([], cons) ->
            pure
              ( Just
                  ( Ann
                      (TypeDefinition (Unqualified tname) tvars (Algebraic cons) loc)
                      loc
                  )
              )
          (errs, _) -> failWithAll errs
    _ -> malformed
  _ -> malformed
  where
    malformed = failWith (AnnP MalformedTypeDefinition loc pexpr)

-- | View an atom as a compound with no arguments.
compoundView :: PExpr -> PExpr
compoundView (Atom n) = Compound n []
compoundView e = e

-- | Validate a type head's parameter list: every parameter must be a
-- variable, and no variable may repeat. Rejecting outright keeps the
-- declared arity equal to the written arity: dropping a malformed
-- parameter would shrink the arity, and keeping a duplicate would
-- alias two parameter positions to one variable.
validateTypeParams ::
  [Ann PExpr] -> Either [AnnP ParseValidationError] [Text]
validateTypeParams params = case go Set.empty params of
  [] -> Right [v | Ann (Var v) _ <- params]
  errs -> Left errs
  where
    go _ [] = []
    go seen (Ann p ploc : rest) = case p of
      Var v
        | Set.member v seen ->
            AnnP (DuplicateTypeParameter v) ploc p : go seen rest
        | otherwise -> go (Set.insert v seen) rest
      _ -> AnnP InvalidTypeParameter ploc p : go seen rest

-- | Convert the body of a @:- opaque_type@ directive to an opaque
-- 'TypeDefinition'. An opaque type has no data constructors, so a
-- constructor body (@---> ...@) is rejected with
-- 'OpaqueTypeHasConstructors'; any other non-head shape is
-- 'MalformedOpaqueTypeDefinition'.
convertOpaqueTypeDefinition :: Ann PExpr -> Conv (Maybe (Ann TypeDefinition))
convertOpaqueTypeDefinition (Ann pexpr loc) = case pexpr of
  Compound "--->" _ -> failWith (AnnP OpaqueTypeHasConstructors loc pexpr)
  Atom n -> pure (Just (mk n []))
  Compound n vars -> case validateTypeParams vars of
    Left errs -> failWithAll errs
    Right tvars -> pure (Just (mk n tvars))
  _ -> failWith (AnnP MalformedOpaqueTypeDefinition loc pexpr)
  where
    mk tname tvars =
      Ann (TypeDefinition (Unqualified tname) tvars Opaque loc) loc

-- | Reserved macro-head names: control-flow and expression symbols the
-- rest of the language parses specially, and the two construction
-- primitives. A macro head using one of these would be
-- indistinguishable from the built-in form at every use site, so it is
-- rejected at definition time rather than left to collide silently.
-- Mirrors 'YCHR.Internal.Rename.Types.reservedSymbolSet' plus the
-- conjunction\/disjunction\/guard operators, which that set does not
-- need to cover because the renamer never resolves a bare
-- @,@\/@;@\/@\\@\/@|@ as a callable name. @:@ is included so that a
-- qualified head @m:f(...)@ is rejected in one error.
reservedMacroHeadNames :: Set Text
reservedMacroHeadNames =
  Set.fromList
    [ ",",
      ";",
      "\\",
      "|",
      "->",
      "=",
      "is",
      "true",
      "quote",
      "fun",
      "$call",
      "tell",
      ":",
      "$compound",
      "$atom"
    ]

-- | Convert a macro clause, @Head ---> Body@ (the @Compound \"--->\"@
-- term a one-line @:- macro@ directive wraps, or a top-level clause),
-- to a 'MacroClause' with its macro's name.
--
-- The head must be an atom or a compound named by an unqualified atom
-- outside 'reservedMacroHeadNames' ('MalformedMacroHead' otherwise).
-- Its arguments are patterns, kept as ordinary 'Term's: any term is a
-- valid pattern. The body must be a list literal with no tail variable
-- ('MalformedMacroBody' otherwise); its elements are kept exactly as
-- written, since whether an expansion is valid depends on where it is
-- used (see "YCHR.Internal.Rename.Macro").
convertMacroClause :: Ann PExpr -> Conv (Maybe NamedClause)
convertMacroClause (Ann pexpr loc) = case pexpr of
  Compound "--->" [macroHead, macroBody] -> case compoundView macroHead.node of
    Compound mname rawParams
      | Set.notMember mname reservedMacroHeadNames ->
          case unfoldListStrict macroBody.node of
            Nothing ->
              failWith (AnnP MalformedMacroBody macroBody.sourceLoc macroBody.node)
            Just elems ->
              let clause = MacroClause (map convertTerm rawParams) (map convertTerm elems)
               in pure (Just (NamedClause mname (AnnP clause loc pexpr)))
    _ -> failWith (AnnP MalformedMacroHead macroHead.sourceLoc macroHead.node)
  _ -> failWith (AnnP MalformedMacroHead loc pexpr)

-- | Convert a PExpr to a 'DataConstructor'. Returns 'Left' if the
-- constructor or any of its argument types is malformed.
convertDataConstructor ::
  Ann PExpr -> Either (AnnP ParseValidationError) DataConstructor
convertDataConstructor (Ann pexpr loc) = case pexpr of
  Atom "[]" -> Right (DataConstructor (Unqualified "[]") [])
  Atom name -> Right (DataConstructor (Unqualified name) [])
  -- [T|list(T)] — list constructor sugar
  Compound "." args ->
    DataConstructor (Unqualified ".") <$> traverse convertTypeExpr args
  Compound name args ->
    DataConstructor (Unqualified name) <$> traverse convertTypeExpr args
  _ -> Left (AnnP MalformedDataConstructor loc pexpr)

-- ** Rule conversion

-- | Convert a top-level PExpr to a 'Rule', collecting any
-- 'MalformedConstraint' errors found in its head.
--
-- Returns 'Nothing' and a 'MalformedTopLevel' error when the input is
-- not a recognized rule shape (named or unnamed @\<=\>@/@==\>@).
convertRule :: Ann PExpr -> Conv (Maybe Rule)
convertRule expr = case expr.node of
  Compound "@" [Ann (Atom name) nameLoc, body] -> named (Just (Ann name nameLoc)) body
  _ -> named Nothing expr
  where
    named mName ruleExpr = case ruleExpr.node of
      Compound "<=>" [h, gb] -> mkRule mName gb <$> convertHead h
      Compound "==>" [h, gb] -> mkRule mName gb <$> convertPropagationHead h
      _ -> failWith (AnnP MalformedTopLevel expr.sourceLoc expr.node)
    mkRule mName gb head_ =
      let gab = splitGuardBody gb
       in Just (Rule mName head_ gab.guard gab.body [])

-- | Convert the head of a simplification or simpagation rule. Malformed
-- constraints are dropped from the resulting head and reported as errors.
--
-- No aggregate can appear here: an aggregate is written as a term the
-- macro preprocessor has to expand first, so the renamer is where heads
-- gain their aggregates.
convertHead :: Ann PExpr -> Conv (AnnP Head)
convertHead (Ann pexpr loc) = case pexpr of
  Compound "\\" [kept, removed] -> do
    keptOk <- convertConstraints kept
    removedOk <- convertConstraints removed
    pure (AnnP (Simpagation keptOk removedOk []) loc pexpr)
  _ -> do
    ok <- convertConstraints (Ann pexpr loc)
    pure (AnnP (Simplification ok []) loc pexpr)

-- | Convert the head of a propagation rule. Malformed constraints are
-- dropped from the resulting head and reported as errors.
convertPropagationHead :: Ann PExpr -> Conv (AnnP Head)
convertPropagationHead (Ann pexpr loc) = do
  ok <- convertConstraints (Ann pexpr loc)
  pure (AnnP (Propagation ok []) loc pexpr)

-- | Convert a comma-separated list of constraints, dropping and
-- reporting malformed ones.
convertConstraints :: Ann PExpr -> Conv [Constraint]
convertConstraints expr = do
  let (errs, ok) = partitionEithers (map convertConstraint (flattenComma expr))
  tell errs
  pure ok

-- | A rule's guard and body.
data GuardAndBody = GuardAndBody
  { guard :: AnnP [Term],
    body :: AnnP [Term]
  }

-- | Split a guard|body PExpr into guard and body term lists.
splitGuardBody :: Ann PExpr -> GuardAndBody
splitGuardBody expr = case expr.node of
  Compound "|" [guard_, body_] -> GuardAndBody (goalList guard_) (goalList body_)
  _ -> GuardAndBody (noAnnPAt expr.sourceLoc []) (goalList expr)

-- | Convert a comma-separated goal list, annotated with its own term.
goalList :: Ann PExpr -> AnnP [Term]
goalList x = AnnP (map convertTerm (flattenComma x)) x.sourceLoc x.node

-- ** Function equation conversion

-- | Convert a top-level PExpr to a 'FunctionEquation'. Returns 'Nothing'
-- and a 'MalformedFunctionEquation' error when the input is not of the
-- expected @lhs [| guard] -> rhs@ shape.
convertFunctionEquation :: Ann PExpr -> Conv (Maybe (AnnP FunctionEquation))
convertFunctionEquation (Ann pexpr loc) = case pexpr of
  Compound "->" [lhs, rhs] -> case lhs.node of
    -- Guarded: lhs_pattern | guard -> rhs
    Compound "|" [p, guard_] -> equation p (goalList guard_) rhs
    -- Unguarded: lhs_pattern -> rhs
    _ -> equation lhs (noAnnPAt lhs.sourceLoc []) rhs
  _ -> failWith (AnnP MalformedFunctionEquation loc pexpr)
  where
    equation pat guardAnn rhs = case equationHead pat of
      Just c ->
        let rhsAnn = AnnP (convertRhsSequence rhs) rhs.sourceLoc rhs.node
            eqn = FunctionEquation (Unqualified c.name) c.args guardAnn rhsAnn []
         in pure (Just (AnnP eqn loc pexpr))
      Nothing -> failWith (AnnP MalformedFunctionEquation loc pexpr)

-- | Flatten a function-equation RHS (or lambda body) on the top-level
-- comma operator. Non-empty by construction.
convertRhsSequence :: Ann PExpr -> NE.NonEmpty Term
convertRhsSequence = fmap convertTerm . flattenComma1

-- | The function name and argument patterns of an equation LHS.
data EquationHead = EquationHead
  { name :: Text,
    args :: [Term]
  }

-- | Read an equation LHS.
--
-- Handles prefix notation @name(args)@ and operator notation @X op Y@
-- (which parses as @Compound op [X, Y]@). Returns 'Nothing' if the LHS
-- is a literal, variable, wildcard, or string.
equationHead :: Ann PExpr -> Maybe EquationHead
equationHead (Ann pexpr _) = case pexpr of
  -- Prefix: name(arg1, arg2, ...) — also covers operator notation.
  Compound name args -> Just (EquationHead name (map convertTerm args))
  -- Bare atom (zero-arity function)
  Atom name -> Just (EquationHead name [])
  _ -> Nothing
