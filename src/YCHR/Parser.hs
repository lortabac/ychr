{-# LANGUAGE OverloadedStrings #-}

-- | Parser for the CHR surface language.
--
-- Parses Prolog-compatible CHR syntax into a 'Module' value.
--
-- Implementation: parses source text to generic 'PExpr' terms first
-- (via 'YCHR.PExpr'), then converts each term to the surface AST.
--
-- Supported syntax:
--
-- @
-- % Line comments
--
-- :- module(order, [leq\/2]). -- Export list specifies visible constraints.
-- :- use_module(stdlib).
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
module YCHR.Parser
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

import Data.Either (partitionEithers)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as Text
import System.FilePath (takeBaseName)
import Text.Parsec (ParseError)
import YCHR.PExpr (PExpr (Atom, Compound, Str, Var))
import YCHR.PExpr qualified as P
import YCHR.Parsed

-- * Operator tables

-- | Operator table: maps fixity levels to operators.
-- Re-exported from 'YCHR.PExpr'.
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
      -- Bounded polymorphism: @sig requiring bound1, bound2, ...@.
      -- Looser than @->@ (1110) so the bound clause sits outside the
      -- signature's arrow, tighter than the directive prefix at 1180
      -- so a @requiring@ clause stays inside the @:- function@ arg.
      -- Comma (1000) is also tighter, so the bound list on the right
      -- is a comma chain consumed as a single argument here.
      (1140, [(P.Xfx, "requiring")]),
      (1150, [(P.Xfx, "--->")]),
      (1180, [(P.Xfx, "<=>"), (P.Xfx, "==>")]),
      ( 1180,
        [ (P.Fx, "chr_constraint"),
          (P.Fx, "chr_type"),
          (P.Fx, "function"),
          (P.Fx, "open_function"),
          (P.Fx, "class"),
          (P.Fx, "open_class"),
          (P.Fx, "extend_class_type"),
          (P.Fx, "extend_class"),
          (P.Fx, "extend_function")
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

-- | Merge user-defined operators into an existing table.
-- Returns 'Left' with the conflicting operator name if a naming conflict is
-- found (same operator name at a different fixity or type).
mergeOps :: OpTable -> [OpDecl] -> Either Text OpTable
mergeOps base decls =
  P.mergeOps base [(d.fixity, d.opType, d.opName) | d <- decls]

-- | List all operator entries in an 'OpTable' as @(fixity, type, name)@
-- triples. The order is unspecified.
opTableEntries :: OpTable -> [(Int, P.OpType, Text)]
opTableEntries = P.opTableEntries

-- * Public parsing functions

-- | Parse a CHR module from source text using the built-in operator table.
--
-- The first argument is the source file name (used in error messages only).
parseModule ::
  String ->
  Text ->
  Either (ParseError) (Module, [AnnP ParseValidationError])
parseModule = parseModuleWith builtinOps

-- | Parse a CHR module from source text using a custom operator table.
parseModuleWith ::
  OpTable ->
  String ->
  Text ->
  Either (ParseError) (Module, [AnnP ParseValidationError])
parseModuleWith table sourceName src = do
  terms <- P.parseTerms table sourceName src
  pure (convertModule (defaultModuleNameForSource sourceName) terms)

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
  Either (ParseError) (Either (AnnP ParseValidationError) Constraint)
parseConstraint = parseConstraintWith builtinOps

-- | Parse a single constraint from surface-language 'Text' using a
-- custom operator table. Used by the single-goal entry points so that
-- user-declared operators (e.g. @+@ from the prelude) are recognized
-- in goal arguments, mirroring the multi-goal parser.
parseConstraintWith ::
  OpTable ->
  String ->
  Text ->
  Either (ParseError) (Either (AnnP ParseValidationError) Constraint)
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
  Either (ParseError) Term
parseTerm = parseTermWith builtinOps

-- | Parse a single term with a custom operator table.
parseTermWith ::
  OpTable ->
  String ->
  Text ->
  Either (ParseError) Term
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
  Either (ParseError) [Term]
parseQuery = parseQueryWith builtinOps

-- | Parse a query with a custom operator table.
--
-- The terminating @.@ is optional: if @src@ (with trailing whitespace
-- stripped) ends in a dot, the dot-terminated parser is used; otherwise
-- the non-terminated one. Picking the parser up front (rather than
-- retrying on failure) keeps the parse error message attached to the
-- right phase — a missing or extra dot is no longer reported as a
-- term-shape error.
parseQueryWith ::
  OpTable ->
  String ->
  Text ->
  Either (ParseError) [Term]
parseQueryWith table sourceName src =
  let parser = if dotTerminated then P.parseTerm else P.parseTermNoDot
   in map convertTerm . flattenComma <$> parser table sourceName src
  where
    trimmed = Text.stripEnd src
    dotTerminated = not (Text.null trimmed) && Text.last trimmed == '.'

-- | Parse a single CHR rule from surface-language 'Text'.
--
-- The outer 'Left' is a parsec parse error. On parse success, the
-- 'Maybe' is 'Nothing' if the parsed term is not a rule shape (a
-- 'MalformedTopLevel' error is emitted in that case); otherwise it
-- contains the parsed 'Rule' and any 'MalformedConstraint' errors
-- collected from its head.
--
-- The source name (first argument) is used in error messages only.
parseRule ::
  String ->
  Text ->
  Either (ParseError) (Maybe Rule, [AnnP ParseValidationError])
parseRule sourceName src = do
  term <- P.parseTerm builtinOps sourceName src
  pure (convertRule term)

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

-- | Information extracted from a leading @:- module(...)@ directive.
-- Private to 'collectModuleHeader'.
data ModuleDirectiveInfo = ModuleDirectiveInfo
  { name :: Text,
    loc :: SourceLoc,
    origin :: PExpr,
    exportOps :: [OpDecl]
  }

-- | Collect a 'ModuleHeader' from a source file using the minimal first-pass
-- operator table.
--
-- Stops at the first directive or rule that cannot be parsed by the
-- first-pass table — which in practice means anything other than
-- @:- module(...)@ or @:- use_module(...)@.
collectModuleHeader :: String -> Text -> Either (ParseError) ModuleHeader
collectModuleHeader sourceName src = do
  (terms, tloc) <- P.parseLeadingTerms firstPassTable sourceName src
  let (modPart, rest1) = case terms of
        (t : ts) | Just i <- asModuleDirective t -> (Just i, ts)
        _ -> (Nothing, terms)
      (imps, leftover) = takeImports rest1
      finalLoc = case leftover of
        [] -> tloc
        (Ann _ loc : _) -> Just loc
      info = case modPart of
        Just i -> i
        Nothing ->
          ModuleDirectiveInfo
            { name = defaultModuleNameForSource sourceName,
              loc = dummyLoc,
              origin = Atom "",
              exportOps = []
            }
  pure
    ModuleHeader
      { modName = info.name,
        modLoc = info.loc,
        modOrigin = info.origin,
        exportOps = info.exportOps,
        headerImports = imps,
        trailingLoc = finalLoc
      }
  where
    asModuleDirective (Ann (Compound ":-" [body]) loc)
      | Compound "module" [Ann (Atom name) _, exports] <- body.node =
          Just
            ModuleDirectiveInfo
              { name,
                loc,
                origin = body.node,
                exportOps = extractOpDeclsFromPExpr exports.node
              }
      | Compound "module" [Ann (Atom name) _] <- body.node =
          Just
            ModuleDirectiveInfo
              { name,
                loc,
                origin = body.node,
                exportOps = []
              }
    asModuleDirective _ = Nothing

    takeImports [] = ([], [])
    -- Malformed @use_module@ directives are silently skipped here; the full
    -- parse path emits 'MalformedImport' for them via 'convertDirective'.
    takeImports all_@(Ann (Compound ":-" [body]) loc : rest) = case body.node of
      Compound "use_module" [imp] ->
        let (more, leftover) = takeImports rest
         in case convertImport loc body.node imp of
              Right ann -> (ann : more, leftover)
              Left _ -> (more, leftover)
      Compound "use_module" [imp, importList] ->
        let (more, leftover) = takeImports rest
         in case convertImportWithList loc body.node imp importList of
              Right (ann, _) -> (ann : more, leftover)
              Left _ -> (more, leftover)
      _ -> ([], all_)
    takeImports rest = ([], rest)

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
-- contribute nothing here; the resulting unknown-library or unknown-import
-- error is reported elsewhere.
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
          Just (OpDecl fix ty name)
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
'convertConstraint' and 'convertTypeExpr'.
-}

-- | Convert a 'PExpr' to a 'Term'.
--
-- See Note [Qualified name handling].
convertTerm :: Ann PExpr -> Term
convertTerm (Ann pexpr _) = case pexpr of
  Var t -> VarTerm t
  P.Int n -> IntTerm n
  P.Float n -> FloatTerm n
  Atom t -> AtomTerm t
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

-- | Flatten a right-nested comma operator into a list.
-- Note: O(n) because @,@ is @xfy@ so the tree is right-heavy (left child
-- is always a leaf).
flattenComma :: Ann PExpr -> [Ann PExpr]
flattenComma (Ann (Compound "," [l, r]) _) = flattenComma l ++ flattenComma r
flattenComma e = [e]

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

-- | Internal directive type.
data Directive
  = DirModule Text SourceLoc PExpr (Maybe [Declaration])
  | DirImport (AnnP Import)
  | DirConstraintDecl [Ann Declaration]
  | DirFunctionDecl [Ann Declaration]
  | DirOpenFunctionDecl [Ann Declaration]
  | DirClassDecl [Ann Declaration]
  | DirOpenClassDecl [Ann Declaration]
  | DirExtendClassTypeDecl [Ann Declaration]
  | DirExtendFunctionEqn (AnnP FunctionEquation)
  | DirExtendClassEqn (AnnP FunctionEquation)
  | DirTypeDecl [Ann TypeDefinition]
  | DirOther

-- | Internal module item type.
data ModuleItem
  = ItemDirective Directive
  | ItemRule Rule
  | ItemEquation (AnnP FunctionEquation)

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
  deriving (Eq, Show)

-- | Convert a list of top-level PExpr terms to a 'Module', along with
-- any validation errors (discontiguous equations, malformed imports,
-- malformed constraints).
--
-- Items whose conversion fails entirely are dropped from the resulting
-- module; their errors are still returned in the second component.
convertModule :: Text -> [Ann PExpr] -> (Module, [AnnP ParseValidationError])
convertModule defaultName terms =
  let itemResults = map convertModuleItem terms
      items = [i | (Just i, _) <- itemResults]
      itemErrors = concatMap snd itemResults
      dirs = [d | ItemDirective d <- items]
      rules = [r | ItemRule r <- items]
      eqs = [e | ItemEquation e <- items]
      (modName_, modNameLoc_, modExports_) = case [(n, l, p, e) | DirModule n l p e <- dirs] of
        ((n, l, p, Just decls) : _) -> (n, l, Just (AnnP decls l p))
        ((n, l, _, Nothing) : _) -> (n, l, Nothing)
        [] -> (defaultName, dummyLoc, Nothing)
      modImports_ = [n | DirImport n <- dirs]
      modDecls_ =
        concat [ds | DirConstraintDecl ds <- dirs]
          ++ concat [ds | DirFunctionDecl ds <- dirs]
          ++ concat [ds | DirOpenFunctionDecl ds <- dirs]
          ++ concat [ds | DirClassDecl ds <- dirs]
          ++ concat [ds | DirOpenClassDecl ds <- dirs]
      modExtensionTypes_ = concat [ds | DirExtendClassTypeDecl ds <- dirs]
      modTypeDecls_ = concat [ds | DirTypeDecl ds <- dirs]
      modExtensions_ = [e | ItemDirective (DirExtendFunctionEqn e) <- items]
      modClassExtensions_ = [e | ItemDirective (DirExtendClassEqn e) <- items]
      openNames =
        Set.fromList $
          [d.name | DirOpenFunctionDecl ds <- dirs, Ann d _ <- ds]
            ++ [d.name | DirOpenClassDecl ds <- dirs, Ann d _ <- ds]
      contiguityErrors = checkContiguity openNames items
      mod_ =
        Module
          { name = modName_,
            nameLoc = modNameLoc_,
            imports = modImports_,
            decls = modDecls_,
            extensionTypes = modExtensionTypes_,
            typeDecls = modTypeDecls_,
            rules = rules,
            equations = eqs,
            extensions = modExtensions_,
            classExtensions = modClassExtensions_,
            exports = modExports_
          }
   in (mod_, itemErrors ++ contiguityErrors)

-- | Check that equations for non-open functions are contiguous.
-- Returns an error for each function whose equations are separated by
-- other items.
checkContiguity :: Set.Set Text -> [ModuleItem] -> [AnnP ParseValidationError]
checkContiguity openNames items =
  checkEquationContiguity openNames items
    ++ checkDeclContiguity openNames items

-- | Equation contiguity: equations for the same non-open function name
-- must be a contiguous block of module items.
checkEquationContiguity ::
  Set.Set Text -> [ModuleItem] -> [AnnP ParseValidationError]
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
  Set.Set Text -> [ModuleItem] -> [AnnP ParseValidationError]
checkDeclContiguity openNames = go Set.empty Set.empty
  where
    -- closed: function names whose decl block has ended.
    -- active: function names declared by the immediately preceding decl
    -- directive (still contiguous).
    go _closed _active [] = []
    go closed active (ItemDirective dir : rest)
      | Just ds <- declListOf dir =
          let names = [(d.name, loc) | Ann d loc <- ds]
              nonOpenNames = [n | n <- map fst names, n `Set.notMember` openNames]
              reopened =
                [ noAnnPAt loc (DiscontiguousFunctionDecls n)
                | (n, loc) <- names,
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
convertModuleItem ::
  Ann PExpr -> (Maybe ModuleItem, [AnnP ParseValidationError])
convertModuleItem expr = case expr.node of
  -- Directive: :- body
  Compound ":-" [_] ->
    let (d, errs) = convertDirective expr in (Just (ItemDirective d), errs)
  -- Named rule: name @ ...
  Compound "@" [_, Ann (Compound "<=>" _) _] -> ruleItem
  Compound "@" [_, Ann (Compound "==>" _) _] -> ruleItem
  -- Unnamed rule
  Compound "<=>" _ -> ruleItem
  Compound "==>" _ -> ruleItem
  -- Function equation (contains -> at top level)
  Compound "->" _ ->
    let (mEq, errs) = convertFunctionEquation expr
     in (ItemEquation <$> mEq, errs)
  -- Anything else at top level is malformed.
  _ -> (Nothing, [AnnP MalformedTopLevel expr.sourceLoc expr.node])
  where
    ruleItem = let (mr, errs) = convertRule expr in (ItemRule <$> mr, errs)

-- ** Directive conversion

-- | Convert a directive PExpr to a 'Directive', collecting any errors
-- raised during conversion. Malformed sub-items (declarations, equations,
-- export items) are dropped and reported via 'ParseValidationError's.
convertDirective :: Ann PExpr -> (Directive, [AnnP ParseValidationError])
convertDirective (Ann (Compound ":-" [body]) loc) = case body.node of
  -- :- module(name, [exports]).
  Compound "module" [Ann (Atom name) _, exports] ->
    let (decls, errs) = collectMaybes (map convertExportItem (unfoldList exports.node))
     in (DirModule name loc body.node (Just decls), errs)
  -- :- module(name).  (no export list — exports everything)
  Compound "module" [Ann (Atom name) _] ->
    (DirModule name loc body.node Nothing, [])
  -- :- use_module(name).  or  :- use_module(library(name)).
  Compound "use_module" [imp, importList] ->
    case convertImportWithList loc body.node imp importList of
      Right (ann, errs) -> (DirImport ann, errs)
      Left err -> (DirOther, [err])
  Compound "use_module" [imp] ->
    case convertImport loc body.node imp of
      Right ann -> (DirImport ann, [])
      Left err -> (DirOther, [err])
  -- :- chr_constraint leq/2, fib/2.
  -- Parsed as prefix op: Compound "chr_constraint" [body]
  Compound "chr_constraint" [decls] ->
    let (decls', errs) = collectDecls convertConstraintDecl decls
     in (DirConstraintDecl decls', errs)
  -- :- function foo/2.  or  :- function factorial(int) -> int.
  Compound "function" [decls] ->
    let (decls', errs) = collectDecls convertFunctionDecl decls
     in (DirFunctionDecl decls', errs)
  -- :- open_function foo/2.
  Compound "open_function" [decls] ->
    let (decls', errs) = collectDecls convertOpenFunctionDecl decls
     in (DirOpenFunctionDecl decls', errs)
  -- :- class size(int) -> int.  or  :- class (size(int) -> int), (size(string) -> int).
  Compound "class" [decls] ->
    let (decls', errs) = collectDecls convertClassDecl decls
        classReqErrs = requiringOnClassErrors loc body.node decls'
     in (DirClassDecl decls', errs ++ classReqErrs)
  -- :- open_class size(int) -> int.
  Compound "open_class" [decls] ->
    let (decls', errs) = collectDecls convertOpenClassDecl decls
        classReqErrs = requiringOnClassErrors loc body.node decls'
     in (DirOpenClassDecl decls', errs ++ classReqErrs)
  -- :- extend_class_type (foo(int) -> int).
  Compound "extend_class_type" [decls] ->
    let (decls', errs) = collectDecls convertExtendClassTypeDecl decls
     in (DirExtendClassTypeDecl decls', errs)
  -- :- extend_function name(args) [| guards] -> body.
  Compound "extend_function" [eqn] ->
    case convertFunctionEquation eqn of
      (Just annEq, errs) -> (DirExtendFunctionEqn annEq, errs)
      (Nothing, errs) -> (DirOther, errs)
  -- :- extend_class name(args) [| guards] -> body.
  Compound "extend_class" [eqn] ->
    case convertFunctionEquation eqn of
      (Just annEq, errs) -> (DirExtendClassEqn annEq, errs)
      (Nothing, errs) -> (DirOther, errs)
  -- :- chr_type name ---> con1 ; con2 ; ...
  -- Parsed as prefix op: Compound "chr_type" [Compound "--->" [head, alts]]
  Compound "chr_type" [typeBody] ->
    case convertTypeDefinition typeBody of
      (Just annDef, errs) -> (DirTypeDecl [annDef], errs)
      (Nothing, errs) -> (DirOther, errs)
  -- Unknown directives (any other @:- name(...)@ shape).
  _ -> (DirOther, [])
convertDirective _ = (DirOther, [])

-- | Run a per-declaration converter over a comma-separated declaration
-- list, dropping declarations that failed conversion and accumulating
-- their errors.
collectDecls ::
  (Ann PExpr -> (Maybe (Ann Declaration), [AnnP ParseValidationError])) ->
  Ann PExpr ->
  ([Ann Declaration], [AnnP ParseValidationError])
collectDecls conv = collectMaybes . map conv . flattenComma

-- | Flatten a list of @(Maybe a, errors)@ results: keep the successes,
-- concatenate the errors.
collectMaybes :: [(Maybe a, [e])] -> ([a], [e])
collectMaybes results = ([a | (Just a, _) <- results], concatMap snd results)

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
-- Returns 'Left' with a 'MalformedImport' error if the import target is not
-- a module name or @library(name)@. On success, also returns any
-- 'MalformedExportItem' errors from items inside the import list.
convertImportWithList ::
  SourceLoc ->
  PExpr ->
  Ann PExpr ->
  Ann PExpr ->
  Either
    (AnnP ParseValidationError)
    (AnnP Import, [AnnP ParseValidationError])
convertImportWithList dirLoc dirPExpr imp importList =
  let (items, itemErrs) =
        collectMaybes (map convertExportItem (unfoldList importList.node))
   in case imp.node of
        Compound "library" [Ann (Atom name) _] ->
          Right (AnnP (LibraryImport name (Just items)) dirLoc dirPExpr, itemErrs)
        Atom name ->
          Right (AnnP (ModuleImport name (Just items)) dirLoc dirPExpr, itemErrs)
        _ -> Left (AnnP MalformedImport imp.sourceLoc imp.node)

-- | Report a 'RequiringOnClass' error for every declaration inside a
-- @:- class@ or @:- open_class@ directive that carries a @requiring@
-- clause. Bounded polymorphism is reserved for @:- function@ /
-- @:- open_function@; the two forms are intentionally orthogonal.
-- The shared location and origin come from the surrounding directive
-- so the diagnostic points at the whole @:- class@.
requiringOnClassErrors ::
  SourceLoc -> PExpr -> [Ann Declaration] -> [AnnP ParseValidationError]
requiringOnClassErrors loc origin decls =
  [ AnnP (RequiringOnClass d.name) loc origin
  | Ann d _ <- decls,
    case d of
      FunctionDecl {requiring = Just _} -> True
      _ -> False
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
convertExportItem ::
  Ann PExpr -> (Maybe Declaration, [AnnP ParseValidationError])
convertExportItem (Ann pexpr loc) = case pexpr of
  Compound "fun" [Ann (Compound "/" [Ann (Atom name) _, Ann (P.Int arity) _]) _] ->
    (Just (FunctionDecl name arity Nothing Nothing False DKFunction Nothing), [])
  Compound "/" [Ann (Atom name) _, Ann (P.Int arity) _] ->
    (Just (ConstraintDecl name arity Nothing Nothing), [])
  Compound "op" [Ann (P.Int fix) _, Ann tyExpr _, Ann nameExpr _]
    | Just ty <- parseOpTypeFromPExpr tyExpr,
      Just name <- atomName nameExpr ->
        (Just (OperatorDecl (OpDecl fix ty name)), [])
  Compound "type" [Ann (Compound "/" [Ann (Atom name) _, Ann (P.Int arity) _]) _] ->
    (Just (TypeExportDecl name arity Nothing), [])
  Compound "type" [Ann (Compound "/" [Ann (Atom name) _, Ann (P.Int arity) _]) _, conList] ->
    case unfoldListStrict conList.node of
      Nothing ->
        (Nothing, [AnnP MalformedExportItem conList.sourceLoc conList.node])
      Just items -> case partitionEithers (map atomElement items) of
        ([], names) -> (Just (TypeExportDecl name arity (Just names)), [])
        (errs, _) -> (Nothing, errs)
  _ -> (Nothing, [AnnP MalformedExportItem loc pexpr])
  where
    atomElement (Ann (Atom n) _) = Right n
    atomElement (Ann e l) = Left (AnnP MalformedExportItem l e)

-- | Convert a PExpr to a constraint declaration. Returns 'Nothing' and
-- a 'MalformedDeclaration' (or 'MalformedTypeExpr' / 'MalformedBoundSig'
-- from sub-conversions) error if the declaration cannot be converted.
convertConstraintDecl ::
  Ann PExpr -> (Maybe (Ann Declaration), [AnnP ParseValidationError])
convertConstraintDecl (Ann pexpr loc) = case pexpr of
  -- @sig requiring bound, ...@
  Compound "requiring" [sig, bounds] -> case sig.node of
    Compound name args ->
      let (argTypeErrs, argTypes) = partitionEithers (map convertTypeExpr args)
          (boundErrs, bs) =
            partitionEithers (map convertBoundSig (flattenComma bounds))
       in case argTypeErrs ++ boundErrs of
            [] ->
              ( Just
                  ( Ann
                      ( ConstraintDecl
                          name
                          (length args)
                          (Just argTypes)
                          (Just bs)
                      )
                      loc
                  ),
                []
              )
            errs -> (Nothing, errs)
    _ -> (Nothing, [AnnP MalformedDeclaration loc pexpr])
  -- Untyped: name/arity
  Compound "/" [Ann (Atom name) _, Ann (P.Int arity) _] ->
    (Just (Ann (ConstraintDecl name arity Nothing Nothing) loc), [])
  -- Typed: name(type, ...)
  Compound name args -> case partitionEithers (map convertTypeExpr args) of
    ([], argTypes) ->
      ( Just
          ( Ann
              (ConstraintDecl name (length args) (Just argTypes) Nothing)
              loc
          ),
        []
      )
    (errs, _) -> (Nothing, errs)
  -- Zero-arity bare atom
  Atom name ->
    (Just (Ann (ConstraintDecl name 0 Nothing Nothing) loc), [])
  _ -> (Nothing, [AnnP MalformedDeclaration loc pexpr])

-- | Convert a PExpr to a closed-function declaration.
convertFunctionDecl ::
  Ann PExpr -> (Maybe (Ann Declaration), [AnnP ParseValidationError])
convertFunctionDecl = convertFunctionDeclWith False DKFunction

-- | Convert a PExpr to an open-function declaration.
convertOpenFunctionDecl ::
  Ann PExpr -> (Maybe (Ann Declaration), [AnnP ParseValidationError])
convertOpenFunctionDecl = convertFunctionDeclWith True DKFunction

-- | Convert a PExpr to a closed-class declaration.
convertClassDecl ::
  Ann PExpr -> (Maybe (Ann Declaration), [AnnP ParseValidationError])
convertClassDecl = convertFunctionDeclWith False DKClass

-- | Convert a PExpr to an open-class declaration.
convertOpenClassDecl ::
  Ann PExpr -> (Maybe (Ann Declaration), [AnnP ParseValidationError])
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
convertExtendClassTypeDecl ::
  Ann PExpr -> (Maybe (Ann Declaration), [AnnP ParseValidationError])
convertExtendClassTypeDecl (Ann pexpr loc) = case pexpr of
  -- @requiring@ is Xfx, so the inner @sig@ is never another @requiring@.
  Compound "requiring" [sig, _] ->
    let (mDecl, errs) = convertSig sig
        targetName = case sig.node of
          Compound "->" [Ann (Compound n _) _, _] -> n
          _ -> "<unknown>"
        reqErr = AnnP (RequiringOnExtendClassType targetName) loc pexpr
     in (mDecl, reqErr : errs)
  _ -> convertSig (Ann pexpr loc)
  where
    convertSig (Ann e l) = case e of
      Compound "->" [Ann (Compound name args) _, ret] ->
        case (partitionEithers (map convertTypeExpr args), convertTypeExpr ret) of
          (([], argTypes), Right retType) ->
            ( Just
                ( Ann
                    ( ExtendClassTypeDecl
                        name
                        (length args)
                        (Just argTypes)
                        (Just retType)
                        Nothing
                    )
                    l
                ),
              []
            )
          ((argErrs, _), retE) ->
            (Nothing, argErrs ++ leftToList retE)
      _ -> (Nothing, [AnnP MalformedDeclaration l e])

-- | Shared implementation of 'convertFunctionDecl',
-- 'convertOpenFunctionDecl', 'convertClassDecl' and
-- 'convertOpenClassDecl'. The 'Bool' argument is the @open@ flag and
-- the 'FunctionDeclKind' selects between @:- function@ and @:- class@.
-- Malformed declarations are dropped and reported via errors.
convertFunctionDeclWith ::
  Bool ->
  FunctionDeclKind ->
  Ann PExpr ->
  (Maybe (Ann Declaration), [AnnP ParseValidationError])
convertFunctionDeclWith open kind (Ann pexpr loc) = case pexpr of
  -- @name(types) -> ret requiring bound, ...@
  Compound "requiring" [sig, bounds] -> case sig.node of
    Compound "->" [Ann (Compound name args) _, ret] ->
      let (argErrs, argTypes) = partitionEithers (map convertTypeExpr args)
          retResult = convertTypeExpr ret
          (boundErrs, bs) =
            partitionEithers (map convertBoundSig (flattenComma bounds))
       in case (argErrs, retResult, boundErrs) of
            ([], Right retType, []) ->
              ( Just
                  ( Ann
                      ( FunctionDecl
                          name
                          (length args)
                          (Just argTypes)
                          (Just retType)
                          open
                          kind
                          (Just bs)
                      )
                      loc
                  ),
                []
              )
            _ -> (Nothing, argErrs ++ leftToList retResult ++ boundErrs)
    _ -> (Nothing, [AnnP MalformedDeclaration loc pexpr])
  -- Untyped: name/arity
  Compound "/" [Ann (Atom name) _, Ann (P.Int arity) _] ->
    ( Just (Ann (FunctionDecl name arity Nothing Nothing open kind Nothing) loc),
      []
    )
  -- Typed: name(type, ...) -> type
  Compound "->" [Ann (Compound name args) _, ret] ->
    case (partitionEithers (map convertTypeExpr args), convertTypeExpr ret) of
      (([], argTypes), Right retType) ->
        ( Just
            ( Ann
                ( FunctionDecl
                    name
                    (length args)
                    (Just argTypes)
                    (Just retType)
                    open
                    kind
                    Nothing
                )
                loc
            ),
          []
        )
      ((argErrs, _), retE) -> (Nothing, argErrs ++ leftToList retE)
  _ -> (Nothing, [AnnP MalformedDeclaration loc pexpr])

-- | Lift a single 'Left' into a singleton list of errors, dropping the
-- 'Right' case. Used when threading 'Either'-based sub-conversion
-- results into an accumulating @[error]@ list.
leftToList :: Either e a -> [e]
leftToList = either pure (const [])

-- | Convert a single bound signature inside a @requiring@ clause. The
-- expected shape is @name(τ₁, ..., τₙ) -> τᵣ@; a bare @name -> τᵣ@ is
-- treated as a zero-arity bound. A malformed shape (or a malformed type
-- inside) is returned as 'Left'; the enclosing declaration is then
-- dropped.
convertBoundSig :: Ann PExpr -> Either (AnnP ParseValidationError) BoundSig
convertBoundSig (Ann pexpr loc) = case pexpr of
  Compound "->" [Ann (Compound name args) _, ret] -> do
    argTypes <- traverse convertTypeExpr args
    returnType <- convertTypeExpr ret
    Right
      BoundSig
        { name = Unqualified name,
          arity = length args,
          argTypes,
          returnType,
          loc
        }
  Compound "->" [Ann (Atom name) _, ret] -> do
    returnType <- convertTypeExpr ret
    Right
      BoundSig
        { name = Unqualified name,
          arity = 0,
          argTypes = [],
          returnType,
          loc
        }
  _ -> Left (AnnP MalformedBoundSig loc pexpr)

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
convertTypeDefinition ::
  Ann PExpr -> (Maybe (Ann TypeDefinition), [AnnP ParseValidationError])
convertTypeDefinition (Ann pexpr loc) = case pexpr of
  -- name(Vars) ---> con1 ; con2 ; ...
  Compound "--->" [typeHead, alts] -> case typeHeadShape typeHead.node of
    Nothing -> (Nothing, [AnnP MalformedTypeDefinition loc pexpr])
    Just (tname, tvars) ->
      case partitionEithers
        (map convertDataConstructor (flattenSemicolon alts)) of
        ([], cons) ->
          ( Just (Ann (TypeDefinition (Unqualified tname) tvars cons loc) loc),
            []
          )
        (errs, _) -> (Nothing, errs)
  _ -> (Nothing, [AnnP MalformedTypeDefinition loc pexpr])
  where
    typeHeadShape (Atom n) = Just (n, [])
    typeHeadShape (Compound n vars) = Just (n, [v | Ann (Var v) _ <- vars])
    typeHeadShape _ = Nothing

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
convertRule :: Ann PExpr -> (Maybe Rule, [AnnP ParseValidationError])
convertRule expr =
  let (mName, ruleExpr) = case expr.node of
        Compound "@" [Ann (Atom name) nameLoc, body] ->
          (Just (Ann name nameLoc), body)
        _ -> (Nothing, expr)
   in case ruleExpr.node of
        Compound "<=>" [h, gb] ->
          let (head_, headErrs) = convertHead h
              (guard_, body_) = splitGuardBody gb
           in (Just (Rule mName head_ guard_ body_), headErrs)
        Compound "==>" [h, gb] ->
          let (head_, headErrs) = convertPropagationHead h
              (guard_, body_) = splitGuardBody gb
           in (Just (Rule mName head_ guard_ body_), headErrs)
        _ -> (Nothing, [AnnP MalformedTopLevel expr.sourceLoc expr.node])

-- | Convert the head of a simplification or simpagation rule. Malformed
-- constraints are dropped from the resulting head and reported as errors.
convertHead :: Ann PExpr -> (AnnP Head, [AnnP ParseValidationError])
convertHead (Ann pexpr loc) = case pexpr of
  Compound "\\" [kept, removed] ->
    let (keptErrs, keptOk) = partitionEithers (map convertConstraint (flattenComma kept))
        ( removedErrs,
          removedOk
          ) = partitionEithers (map convertConstraint (flattenComma removed))
     in (AnnP (Simpagation keptOk removedOk) loc pexpr, keptErrs ++ removedErrs)
  _ ->
    let (errs, ok) = partitionEithers (map convertConstraint (flattenComma (Ann pexpr loc)))
     in (AnnP (Simplification ok) loc pexpr, errs)

-- | Convert the head of a propagation rule. Malformed constraints are
-- dropped from the resulting head and reported as errors.
convertPropagationHead :: Ann PExpr -> (AnnP Head, [AnnP ParseValidationError])
convertPropagationHead (Ann pexpr loc) =
  let (errs, ok) = partitionEithers (map convertConstraint (flattenComma (Ann pexpr loc)))
   in (AnnP (Propagation ok) loc pexpr, errs)

-- | Split a guard|body PExpr into guard and body term lists.
splitGuardBody :: Ann PExpr -> (AnnP [Term], AnnP [Term])
splitGuardBody expr = case expr.node of
  Compound "|" [guard_, body_] ->
    ( AnnP (map convertTerm (flattenComma guard_)) guard_.sourceLoc guard_.node,
      AnnP (map convertTerm (flattenComma body_)) body_.sourceLoc body_.node
    )
  _ ->
    ( noAnnPAt expr.sourceLoc [],
      AnnP (map convertTerm (flattenComma expr)) expr.sourceLoc expr.node
    )

-- ** Function equation conversion

-- | Convert a top-level PExpr to a 'FunctionEquation'. Returns 'Nothing'
-- and a 'MalformedFunctionEquation' error when the input is not of the
-- expected @lhs [| guard] -> rhs@ shape.
convertFunctionEquation ::
  Ann PExpr -> (Maybe (AnnP FunctionEquation), [AnnP ParseValidationError])
convertFunctionEquation (Ann pexpr loc) = case pexpr of
  Compound "->" [lhs, rhs] -> case lhs.node of
    -- Guarded: lhs_pattern | guard -> rhs
    Compound "|" [pat, guard_] -> case extractFunNameArgs pat of
      Just (name, args) ->
        ( Just
            ( AnnP
                ( FunctionEquation
                    (Unqualified name)
                    args
                    ( AnnP
                        (map convertTerm (flattenComma guard_))
                        guard_.sourceLoc
                        guard_.node
                    )
                    (AnnP (convertTerm rhs) rhs.sourceLoc rhs.node)
                )
                loc
                pexpr
            ),
          []
        )
      Nothing -> (Nothing, [AnnP MalformedFunctionEquation loc pexpr])
    -- Unguarded: lhs_pattern -> rhs
    _ -> case extractFunNameArgs lhs of
      Just (name, args) ->
        ( Just
            ( AnnP
                ( FunctionEquation
                    (Unqualified name)
                    args
                    (noAnnPAt lhs.sourceLoc [])
                    (AnnP (convertTerm rhs) rhs.sourceLoc rhs.node)
                )
                loc
                pexpr
            ),
          []
        )
      Nothing -> (Nothing, [AnnP MalformedFunctionEquation loc pexpr])
  _ -> (Nothing, [AnnP MalformedFunctionEquation loc pexpr])

-- | Extract the function name and argument list from an equation LHS.
--
-- Handles prefix notation @name(args)@ and operator notation @X op Y@
-- (which parses as @Compound op [X, Y]@). Returns 'Nothing' if the LHS
-- is a literal, variable, wildcard, or string.
extractFunNameArgs :: Ann PExpr -> Maybe (Text, [Term])
extractFunNameArgs (Ann pexpr _) = case pexpr of
  -- Prefix: name(arg1, arg2, ...) — also covers operator notation.
  Compound name args -> Just (name, map convertTerm args)
  -- Bare atom (zero-arity function)
  Atom name -> Just (name, [])
  _ -> Nothing
