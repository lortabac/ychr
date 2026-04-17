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
  ( parseModule,
    parseModuleWith,
    parseConstraint,
    parseQuery,
    parseQueryWith,
    parseTerm,
    parseTermWith,
    parseRule,
    OpTable,
    builtinOps,
    mergeOps,
    opTableEntries,
    ModuleHeader (..),
    collectModuleHeader,
    buildModuleOpTable,
    extractOpDecls,
    ParseValidationError (..),
  )
where

import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Void (Void)
import Text.Megaparsec (ParseErrorBundle)
import YCHR.PExpr (PExpr (Atom, Compound, Str, Var))
import YCHR.PExpr qualified as P
import YCHR.Parsed

-- ---------------------------------------------------------------------------
-- Operator table (re-exported from PExpr)
-- ---------------------------------------------------------------------------

-- | Operator table: maps fixity levels to operators.
-- Re-exported from 'YCHR.PExpr'.
type OpTable = P.OpTable

-- | Built-in operators for CHR syntax.
--
-- This is a minimal table containing only the operators needed for CHR
-- language structure. Arithmetic and comparison operators are provided
-- by the @builtins@ library.
--
-- Directive keywords (@chr_constraint@, @function@, @chr_type@, @dynamic@)
-- are prefix operators following standard Prolog convention, so that
-- @:- chr_constraint leq\/2.@ parses as a single term.
builtinOps :: OpTable
builtinOps =
  P.mkOpTable
    [ (100, [(P.Yfx, ":")]),
      (400, [(P.Yfx, "/")]),
      (700, [(P.Xfx, "is"), (P.Xfx, "=")]),
      (1000, [(P.Xfy, ",")]),
      (1105, [(P.Xfy, "|")]),
      (1110, [(P.Xfy, "->")]),
      (1100, [(P.Xfy, ";"), (P.Xfx, "\\")]),
      (1150, [(P.Xfx, "--->"), (P.Fx, "dynamic")]),
      (1180, [(P.Xfx, "<=>"), (P.Xfx, "==>")]),
      (1180, [(P.Fx, "chr_constraint"), (P.Fx, "chr_type"), (P.Fx, "function"), (P.Fx, "open_function")]),
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

-- ---------------------------------------------------------------------------
-- Public parsing functions
-- ---------------------------------------------------------------------------

-- | Parse a CHR module from source text using the built-in operator table.
--
-- The first argument is the source file name (used in error messages only).
parseModule ::
  String ->
  Text ->
  Either (ParseErrorBundle Text Void) (Module, [AnnP ParseValidationError])
parseModule = parseModuleWith builtinOps

-- | Parse a CHR module from source text using a custom operator table.
parseModuleWith ::
  OpTable ->
  String ->
  Text ->
  Either (ParseErrorBundle Text Void) (Module, [AnnP ParseValidationError])
parseModuleWith table sourceName src = do
  terms <- P.parseTerms table sourceName src
  pure (convertModule terms)

-- | Parse a single constraint from surface-language 'Text'.
--
-- The source name (first argument) is used in error messages only.
-- Example: @parseConstraint "\<query\>" "leq(X, Y)"@.
parseConstraint ::
  String ->
  Text ->
  Either (ParseErrorBundle Text Void) Constraint
parseConstraint sourceName src = do
  term <- P.parseTermNoDot builtinOps sourceName src
  pure (convertConstraint term)

-- | Parse a single term from surface-language 'Text'.
--
-- The source name (first argument) is used in error messages only.
-- Example: @parseTerm "\<query\>" "f(X, 42)"@.
parseTerm ::
  String ->
  Text ->
  Either (ParseErrorBundle Text Void) Term
parseTerm = parseTermWith builtinOps

-- | Parse a single term with a custom operator table.
parseTermWith ::
  OpTable ->
  String ->
  Text ->
  Either (ParseErrorBundle Text Void) Term
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
  Either (ParseErrorBundle Text Void) [Term]
parseQuery = parseQueryWith builtinOps

-- | Parse a query with a custom operator table.
parseQueryWith ::
  OpTable ->
  String ->
  Text ->
  Either (ParseErrorBundle Text Void) [Term]
parseQueryWith table sourceName src =
  -- Try with dot terminator first, then without.
  case P.parseTerm table sourceName src of
    Right term -> Right (map convertTerm (flattenComma term))
    Left _ -> do
      term <- P.parseTermNoDot table sourceName src
      pure (map convertTerm (flattenComma term))

-- | Parse a single CHR rule from surface-language 'Text'.
--
-- The source name (first argument) is used in error messages only.
parseRule ::
  String ->
  Text ->
  Either (ParseErrorBundle Text Void) Rule
parseRule sourceName src = do
  term <- P.parseTerm builtinOps sourceName src
  pure (convertRule term)

-- ---------------------------------------------------------------------------
-- First-pass module-header collector
-- ---------------------------------------------------------------------------

-- | Minimal operator table for the first pass: only enough to parse
-- @:- module(...)@ and @:- use_module(...)@ directives.
firstPassTable :: OpTable
firstPassTable =
  P.mkOpTable
    [ (400, [(P.Yfx, "/")]),
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
collectModuleHeader :: String -> Text -> Either (ParseErrorBundle Text Void) ModuleHeader
collectModuleHeader sourceName src = do
  (terms, tloc) <- P.parseLeadingTerms firstPassTable sourceName src
  let (modPart, rest1) = case terms of
        (t : ts) | Just info <- asModuleDirective t -> (Just info, ts)
        _ -> (Nothing, terms)
      (imps, leftover) = takeImports rest1
      finalLoc = case leftover of
        [] -> tloc
        (Ann _ loc : _) -> Just loc
      (mn, ml, mo, ops) = case modPart of
        Just info -> info
        Nothing -> ("<no_module>", dummyLoc, Atom "", [])
  pure
    ModuleHeader
      { modName = mn,
        modLoc = ml,
        modOrigin = mo,
        exportOps = ops,
        headerImports = imps,
        trailingLoc = finalLoc
      }
  where
    asModuleDirective (Ann (Compound ":-" [body]) loc)
      | Compound "module" [Ann (Atom name) _, exports] <- body.node =
          Just (name, loc, body.node, extractOpDeclsFromPExpr exports.node)
    asModuleDirective _ = Nothing

    takeImports [] = ([], [])
    takeImports all_@(Ann (Compound ":-" [body]) loc : rest) = case body.node of
      Compound "use_module" [imp] ->
        let (more, leftover) = takeImports rest
         in (convertImport loc body.node imp : more, leftover)
      Compound "use_module" [imp, importList] ->
        let (more, leftover) = takeImports rest
         in (convertImportWithList loc body.node imp importList : more, leftover)
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
        Just name <- extractAtomName nameExpr =
          Just (OpDecl fix ty name)
    toOpDecl _ = Nothing

    extractAtomName (Atom a) = Just a
    extractAtomName _ = Nothing

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

-- ---------------------------------------------------------------------------
-- PExpr → Term conversion
-- ---------------------------------------------------------------------------

-- | Convert a 'PExpr' to a 'Term'.
convertTerm :: Ann PExpr -> Term
convertTerm (Ann pexpr _) = case pexpr of
  Var t -> VarTerm t
  P.Int n -> IntTerm n
  Atom t -> AtomTerm t
  Str t -> TextTerm t
  P.Wildcard -> Wildcard
  -- Qualified name: module:name or module:name(args)
  Compound ":" [Ann (Atom m) _, Ann (Atom n) _] ->
    CompoundTerm (Qualified m n) []
  Compound ":" [Ann (Atom m) _, Ann (Compound n args) _] ->
    CompoundTerm (Qualified m n) (map convertTerm args)
  -- Regular compound
  Compound f args ->
    CompoundTerm (Unqualified f) (map convertTerm args)

-- ---------------------------------------------------------------------------
-- PExpr → Constraint conversion
-- ---------------------------------------------------------------------------

-- | Convert a 'PExpr' to a 'Constraint'.
convertConstraint :: Ann PExpr -> Constraint
convertConstraint (Ann pexpr _) = case pexpr of
  Atom name ->
    Constraint (Unqualified name) []
  Compound ":" [Ann (Atom m) _, Ann (Atom n) _] ->
    Constraint (Qualified m n) []
  Compound ":" [Ann (Atom m) _, Ann (Compound n args) _] ->
    Constraint (Qualified m n) (map convertTerm args)
  Compound name args ->
    Constraint (Unqualified name) (map convertTerm args)
  -- Bare variable / integer / etc. in constraint position — produce
  -- a best-effort result; downstream will report the error.
  _ -> Constraint (Unqualified "<invalid>") []

-- ---------------------------------------------------------------------------
-- Flattening helpers
-- ---------------------------------------------------------------------------

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

-- ---------------------------------------------------------------------------
-- Module conversion
-- ---------------------------------------------------------------------------

-- | Internal directive type.
data Directive
  = DirModule Text SourceLoc PExpr [Declaration]
  | DirImport (AnnP Import)
  | DirConstraintDecl [Ann Declaration]
  | DirFunctionDecl [Ann Declaration]
  | DirOpenFunctionDecl [Ann Declaration]
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
  deriving (Eq, Show)

-- | Convert a list of top-level PExpr terms to a 'Module', along with
-- any validation errors (e.g. discontiguous equations).
convertModule :: [Ann PExpr] -> (Module, [AnnP ParseValidationError])
convertModule terms =
  let items = map convertModuleItem terms
      dirs = [d | ItemDirective d <- items]
      rules = [r | ItemRule r <- items]
      eqs = [e | ItemEquation e <- items]
      (modName_, modExports_) = case [(n, l, p, e) | DirModule n l p e <- dirs] of
        ((n, l, p, e) : _) -> (n, Just (AnnP e l p))
        [] -> ("<no_module>", Nothing)
      modImports_ = [n | DirImport n <- dirs]
      modDecls_ =
        concat [ds | DirConstraintDecl ds <- dirs]
          ++ concat [ds | DirFunctionDecl ds <- dirs]
          ++ concat [ds | DirOpenFunctionDecl ds <- dirs]
      modTypeDecls_ = concat [ds | DirTypeDecl ds <- dirs]
      openNames =
        Set.fromList
          [d.name | DirOpenFunctionDecl ds <- dirs, Ann d _ <- ds]
      contiguityErrors = checkContiguity openNames items
      mod_ = Module modName_ modImports_ modDecls_ modTypeDecls_ rules eqs modExports_
   in (mod_, contiguityErrors)

-- | Check that equations for non-open functions are contiguous.
-- Returns an error for each function whose equations are separated by
-- other items.
checkContiguity :: Set.Set Text -> [ModuleItem] -> [AnnP ParseValidationError]
checkContiguity openNames = go Set.empty Nothing
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

-- | Classify and convert a single top-level PExpr.
convertModuleItem :: Ann PExpr -> ModuleItem
convertModuleItem expr = case expr.node of
  -- Directive: :- body
  Compound ":-" [_] -> ItemDirective (convertDirective expr)
  -- Named rule: name @ ...
  Compound "@" [_, Ann (Compound "<=>" _) _] -> ItemRule (convertRule expr)
  Compound "@" [_, Ann (Compound "==>" _) _] -> ItemRule (convertRule expr)
  -- Unnamed rule
  Compound "<=>" _ -> ItemRule (convertRule expr)
  Compound "==>" _ -> ItemRule (convertRule expr)
  -- Function equation (contains -> at top level)
  Compound "->" _ -> ItemEquation (convertFunctionEquation expr)
  -- Fallback: try as rule
  _ -> ItemRule (convertRule expr)

-- ---------------------------------------------------------------------------
-- Directive conversion
-- ---------------------------------------------------------------------------

-- | Convert a directive PExpr to a 'Directive'.
convertDirective :: Ann PExpr -> Directive
convertDirective (Ann (Compound ":-" [body]) loc) = case body.node of
  -- :- module(name, [exports]).
  Compound "module" [Ann (Atom name) _, exports] ->
    DirModule name loc body.node (map convertExportItem (unfoldList exports.node))
  -- :- use_module(name).  or  :- use_module(library(name)).
  Compound "use_module" [imp, importList] ->
    DirImport (convertImportWithList loc body.node imp importList)
  Compound "use_module" [imp] ->
    DirImport (convertImport loc body.node imp)
  -- :- chr_constraint leq/2, fib/2.
  -- Parsed as prefix op: Compound "chr_constraint" [body]
  Compound "chr_constraint" [decls] ->
    DirConstraintDecl (map convertConstraintDecl (flattenComma decls))
  -- :- function foo/2.  or  :- function factorial(int) -> int.
  Compound "function" [decls] ->
    DirFunctionDecl (map convertFunctionDecl (flattenComma decls))
  -- :- open_function foo/2.
  Compound "open_function" [decls] ->
    DirOpenFunctionDecl (map convertOpenFunctionDecl (flattenComma decls))
  -- :- chr_type name ---> con1 ; con2 ; ...
  -- Parsed as prefix op: Compound "chr_type" [Compound "--->" [head, alts]]
  Compound "chr_type" [typeBody] ->
    DirTypeDecl [convertTypeDefinition typeBody]
  -- Unknown directives (e.g. :- dynamic foo/1.)
  _ -> DirOther
convertDirective _ = DirOther

-- | Convert an import PExpr (use_module/1, imports everything).
convertImport :: SourceLoc -> PExpr -> Ann PExpr -> AnnP Import
convertImport dirLoc dirPExpr (Ann pexpr _) = case pexpr of
  Compound "library" [Ann (Atom name) _] -> AnnP (LibraryImport name Nothing) dirLoc dirPExpr
  Atom name -> AnnP (ModuleImport name Nothing) dirLoc dirPExpr
  _ -> AnnP (ModuleImport "<unknown>" Nothing) dirLoc dirPExpr

-- | Convert an import PExpr with an explicit import list (use_module/2).
convertImportWithList :: SourceLoc -> PExpr -> Ann PExpr -> Ann PExpr -> AnnP Import
convertImportWithList dirLoc dirPExpr imp importList =
  let items = map convertExportItem (unfoldList importList.node)
   in case imp.node of
        Compound "library" [Ann (Atom name) _] -> AnnP (LibraryImport name (Just items)) dirLoc dirPExpr
        Atom name -> AnnP (ModuleImport name (Just items)) dirLoc dirPExpr
        _ -> AnnP (ModuleImport "<unknown>" (Just items)) dirLoc dirPExpr

-- | Convert an export item PExpr to a 'Declaration'.
convertExportItem :: Ann PExpr -> Declaration
convertExportItem (Ann pexpr _) = case pexpr of
  Compound "/" [Ann (Atom name) _, Ann (P.Int arity) _] ->
    ConstraintDecl name arity Nothing
  Compound "op" [Ann (P.Int fix) _, Ann tyExpr _, Ann nameExpr _]
    | Just ty <- parseOpTypeFromPExpr tyExpr,
      Just name <- extractName nameExpr ->
        OperatorDecl (OpDecl fix ty name)
  Compound "type" [Ann (Compound "/" [Ann (Atom name) _, Ann (P.Int arity) _]) _] ->
    TypeExportDecl name arity
  _ -> ConstraintDecl "<unknown>" 0 Nothing
  where
    extractName (Atom a) = Just a
    extractName _ = Nothing

-- | Convert a PExpr to a constraint declaration.
convertConstraintDecl :: Ann PExpr -> Ann Declaration
convertConstraintDecl (Ann pexpr loc) = case pexpr of
  -- Untyped: name/arity
  Compound "/" [Ann (Atom name) _, Ann (P.Int arity) _] ->
    Ann (ConstraintDecl name arity Nothing) loc
  -- Typed: name(type, ...)
  Compound name args ->
    Ann (ConstraintDecl name (length args) (Just (map convertTypeExpr args))) loc
  -- Zero-arity bare atom
  Atom name ->
    Ann (ConstraintDecl name 0 Nothing) loc
  _ -> Ann (ConstraintDecl "<unknown>" 0 Nothing) loc

-- | Convert a PExpr to a function declaration.
convertFunctionDecl :: Ann PExpr -> Ann Declaration
convertFunctionDecl = convertFunctionDeclWith False

convertOpenFunctionDecl :: Ann PExpr -> Ann Declaration
convertOpenFunctionDecl = convertFunctionDeclWith True

convertFunctionDeclWith :: Bool -> Ann PExpr -> Ann Declaration
convertFunctionDeclWith open (Ann pexpr loc) = case pexpr of
  -- Untyped: name/arity
  Compound "/" [Ann (Atom name) _, Ann (P.Int arity) _] ->
    Ann (FunctionDecl name arity Nothing Nothing open) loc
  -- Typed: name(type, ...) -> type
  Compound "->" [Ann (Compound name args) _, ret] ->
    Ann
      ( FunctionDecl
          name
          (length args)
          (Just (map convertTypeExpr args))
          (Just (convertTypeExpr ret))
          open
      )
      loc
  _ -> Ann (FunctionDecl "<unknown>" 0 Nothing Nothing open) loc

-- | Convert a PExpr to a 'TypeExpr'.
convertTypeExpr :: Ann PExpr -> TypeExpr
convertTypeExpr (Ann pexpr _) = case pexpr of
  Var t -> TypeVar t
  Atom "[]" -> TypeCon (Unqualified "[]") []
  Atom name -> TypeCon (Unqualified name) []
  Compound "." args -> TypeCon (Unqualified ".") (map convertTypeExpr args)
  Compound name args -> TypeCon (Unqualified name) (map convertTypeExpr args)
  _ -> TypeCon (Unqualified "<unknown>") []

-- | Convert a PExpr to a 'TypeDefinition'.
convertTypeDefinition :: Ann PExpr -> Ann TypeDefinition
convertTypeDefinition (Ann pexpr loc) = case pexpr of
  -- name(Vars) ---> con1 ; con2 ; ...
  Compound "--->" [typeHead, alts] ->
    let (tname, tvars) = case typeHead.node of
          Atom n -> (n, [])
          Compound n vars -> (n, [v | Ann (Var v) _ <- vars])
          _ -> ("<unknown>", [])
        cons = map convertDataConstructor (flattenSemicolon alts)
     in Ann (TypeDefinition (Unqualified tname) tvars cons) loc
  _ -> Ann (TypeDefinition (Unqualified "<unknown>") [] []) loc

-- | Convert a PExpr to a 'DataConstructor'.
convertDataConstructor :: Ann PExpr -> DataConstructor
convertDataConstructor (Ann pexpr _) = case pexpr of
  Atom "[]" -> DataConstructor (Unqualified "[]") []
  Atom name -> DataConstructor (Unqualified name) []
  -- [T|list(T)] — list constructor sugar
  Compound "." args ->
    DataConstructor (Unqualified ".") (map convertTypeExpr args)
  Compound name args ->
    DataConstructor (Unqualified name) (map convertTypeExpr args)
  _ -> DataConstructor (Unqualified "<unknown>") []

-- ---------------------------------------------------------------------------
-- Rule conversion
-- ---------------------------------------------------------------------------

-- | Convert a top-level PExpr to a 'Rule'.
convertRule :: Ann PExpr -> Rule
convertRule expr =
  let (mName, ruleExpr) = case expr.node of
        Compound "@" [Ann (Atom name) nameLoc, body] ->
          (Just (Ann name nameLoc), body)
        _ -> (Nothing, expr)
      (head_, guardBody) = case ruleExpr.node of
        Compound "<=>" [h, gb] -> (convertHead h, gb)
        Compound "==>" [h, gb] -> (convertPropagationHead h, gb)
        _ -> (noAnnP (Simplification []), ruleExpr) -- fallback
      (guard_, body_) = splitGuardBody guardBody
   in Rule mName head_ guard_ body_

-- | Convert the head of a simplification or simpagation rule.
convertHead :: Ann PExpr -> AnnP Head
convertHead (Ann pexpr loc) = case pexpr of
  Compound "\\" [kept, removed] ->
    AnnP
      ( Simpagation
          (map convertConstraint (flattenComma kept))
          (map convertConstraint (flattenComma removed))
      )
      loc
      pexpr
  _ ->
    AnnP (Simplification (map convertConstraint (flattenComma (Ann pexpr loc)))) loc pexpr

-- | Convert the head of a propagation rule.
convertPropagationHead :: Ann PExpr -> AnnP Head
convertPropagationHead (Ann pexpr loc) =
  AnnP (Propagation (map convertConstraint (flattenComma (Ann pexpr loc)))) loc pexpr

-- | Split a guard|body PExpr into guard and body term lists.
splitGuardBody :: Ann PExpr -> (AnnP [Term], AnnP [Term])
splitGuardBody expr = case expr.node of
  Compound "|" [guard_, body_] ->
    ( AnnP (map convertTerm (flattenComma guard_)) guard_.sourceLoc guard_.node,
      AnnP (map convertTerm (flattenComma body_)) body_.sourceLoc body_.node
    )
  _ ->
    ( AnnP [] expr.sourceLoc (Atom ""),
      AnnP (map convertTerm (flattenComma expr)) expr.sourceLoc expr.node
    )

-- ---------------------------------------------------------------------------
-- Function equation conversion
-- ---------------------------------------------------------------------------

-- | Convert a top-level PExpr to a 'FunctionEquation'.
convertFunctionEquation :: Ann PExpr -> AnnP FunctionEquation
convertFunctionEquation (Ann pexpr loc) = case pexpr of
  Compound "->" [lhs, rhs] ->
    case lhs.node of
      -- Guarded: lhs_pattern | guard -> rhs
      Compound "|" [pat, guard_] ->
        let (name, args) = extractFunNameArgs pat
         in AnnP
              ( FunctionEquation
                  (Unqualified name)
                  args
                  (AnnP (map convertTerm (flattenComma guard_)) guard_.sourceLoc guard_.node)
                  (AnnP (convertTerm rhs) rhs.sourceLoc rhs.node)
              )
              loc
              pexpr
      -- Unguarded: lhs_pattern -> rhs
      _ ->
        let (name, args) = extractFunNameArgs lhs
         in AnnP
              ( FunctionEquation
                  (Unqualified name)
                  args
                  (AnnP [] lhs.sourceLoc (Atom ""))
                  (AnnP (convertTerm rhs) rhs.sourceLoc rhs.node)
              )
              loc
              pexpr
  _ ->
    AnnP (FunctionEquation (Unqualified "<unknown>") [] (AnnP [] loc (Atom "")) (AnnP (convertTerm (Ann pexpr loc)) loc pexpr)) loc pexpr

-- | Extract the function name and argument list from an equation LHS.
--
-- Handles prefix notation @name(args)@ and operator notation @X op Y@.
extractFunNameArgs :: Ann PExpr -> (Text, [Term])
extractFunNameArgs (Ann pexpr _) = case pexpr of
  -- Prefix: name(arg1, arg2, ...)
  Compound name args -> (name, map convertTerm args)
  -- Bare atom (zero-arity function)
  Atom name -> (name, [])
  -- Shouldn't happen, but provide a fallback
  _ -> ("<unknown>", [])
