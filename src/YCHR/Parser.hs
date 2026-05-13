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
import Data.Void (Void)
import Text.Megaparsec (ParseErrorBundle)
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
-- Directive keywords (@chr_constraint@, @function@, @chr_type@, @dynamic@)
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
      (1150, [(P.Xfx, "--->"), (P.Fx, "dynamic")]),
      (1180, [(P.Xfx, "<=>"), (P.Xfx, "==>")]),
      ( 1180,
        [ (P.Fx, "chr_constraint"),
          (P.Fx, "chr_type"),
          (P.Fx, "function"),
          (P.Fx, "open_function"),
          (P.Fx, "extend_function_type"),
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
-- The outer 'Left' is a megaparsec parse error; the inner 'Left' is a
-- 'ParseValidationError' (the input parsed but did not denote a
-- constraint, e.g. a bare variable or integer).
--
-- The source name (first argument) is used in error messages only.
-- Example: @parseConstraint "\<query\>" "leq(X, Y)"@.
parseConstraint ::
  String ->
  Text ->
  Either (ParseErrorBundle Text Void) (Either (AnnP ParseValidationError) Constraint)
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
-- The outer 'Left' is a megaparsec parse error; the second component of
-- the 'Right' is a list of 'ParseValidationError's collected while
-- converting the rule (currently only 'MalformedConstraint' from rule
-- heads).
--
-- The source name (first argument) is used in error messages only.
parseRule ::
  String ->
  Text ->
  Either (ParseErrorBundle Text Void) (Rule, [AnnP ParseValidationError])
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
collectModuleHeader :: String -> Text -> Either (ParseErrorBundle Text Void) ModuleHeader
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
            { name = "<no_module>",
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
              Right ann -> (ann : more, leftover)
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

-- ** Module conversion

-- | Internal directive type.
data Directive
  = DirModule Text SourceLoc PExpr (Maybe [Declaration])
  | DirImport (AnnP Import)
  | DirConstraintDecl [Ann Declaration]
  | DirFunctionDecl [Ann Declaration]
  | DirOpenFunctionDecl [Ann Declaration]
  | DirExtendFunctionTypeDecl [Ann Declaration]
  | DirExtendFunctionEqn (AnnP FunctionEquation)
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
  | -- | A @requiring@ clause appears inside a comma-separated
    -- multi-signature @:- function@ declaration. The bounded form is
    -- only permitted on a typed single-signature declaration; the
    -- spec rules this out at the surface-syntax level. Carries the
    -- bounded function's name.
    RequiringOnMultiSig Text
  | -- | A @requiring@ clause appears on a @:- extend_function_type@
    -- directive. Bounds are part of the original declaration; an
    -- extension cannot introduce them. Carries the extension target's
    -- name.
    RequiringOnExtendFunctionType Text
  deriving (Eq, Show)

-- | Convert a list of top-level PExpr terms to a 'Module', along with
-- any validation errors (discontiguous equations, malformed imports,
-- malformed constraints).
convertModule :: [Ann PExpr] -> (Module, [AnnP ParseValidationError])
convertModule terms =
  let itemResults = map convertModuleItem terms
      items = map fst itemResults
      itemErrors = concatMap snd itemResults
      dirs = [d | ItemDirective d <- items]
      rules = [r | ItemRule r <- items]
      eqs = [e | ItemEquation e <- items]
      (modName_, modExports_) = case [(n, l, p, e) | DirModule n l p e <- dirs] of
        ((n, l, p, Just decls) : _) -> (n, Just (AnnP decls l p))
        ((n, _, _, Nothing) : _) -> (n, Nothing)
        [] -> ("<no_module>", Nothing)
      modImports_ = [n | DirImport n <- dirs]
      modDecls_ =
        concat [ds | DirConstraintDecl ds <- dirs]
          ++ concat [ds | DirFunctionDecl ds <- dirs]
          ++ concat [ds | DirOpenFunctionDecl ds <- dirs]
      modExtensionTypes_ = concat [ds | DirExtendFunctionTypeDecl ds <- dirs]
      modTypeDecls_ = concat [ds | DirTypeDecl ds <- dirs]
      modExtensions_ = [e | ItemDirective (DirExtendFunctionEqn e) <- items]
      openNames =
        Set.fromList
          [d.name | DirOpenFunctionDecl ds <- dirs, Ann d _ <- ds]
      contiguityErrors = checkContiguity openNames items
      mod_ =
        Module
          { name = modName_,
            imports = modImports_,
            decls = modDecls_,
            extensionTypes = modExtensionTypes_,
            typeDecls = modTypeDecls_,
            rules = rules,
            equations = eqs,
            extensions = modExtensions_,
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
                [ AnnP (DiscontiguousFunctionDecls n) loc (Atom "")
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
    declListOf _ = Nothing

-- | Classify and convert a single top-level PExpr, collecting any errors
-- raised during conversion.
convertModuleItem :: Ann PExpr -> (ModuleItem, [AnnP ParseValidationError])
convertModuleItem expr = case expr.node of
  -- Directive: :- body
  Compound ":-" [_] ->
    let (d, errs) = convertDirective expr in (ItemDirective d, errs)
  -- Named rule: name @ ...
  Compound "@" [_, Ann (Compound "<=>" _) _] -> ruleItem
  Compound "@" [_, Ann (Compound "==>" _) _] -> ruleItem
  -- Unnamed rule
  Compound "<=>" _ -> ruleItem
  Compound "==>" _ -> ruleItem
  -- Function equation (contains -> at top level)
  Compound "->" _ -> (ItemEquation (convertFunctionEquation expr), [])
  -- Fallback: try as rule
  _ -> ruleItem
  where
    ruleItem = let (r, errs) = convertRule expr in (ItemRule r, errs)

-- ** Directive conversion

-- | Convert a directive PExpr to a 'Directive', collecting any errors
-- raised during conversion (currently only from malformed @use_module@
-- arguments).
convertDirective :: Ann PExpr -> (Directive, [AnnP ParseValidationError])
convertDirective (Ann (Compound ":-" [body]) loc) = case body.node of
  -- :- module(name, [exports]).
  Compound "module" [Ann (Atom name) _, exports] ->
    (DirModule name loc body.node (Just (map convertExportItem (unfoldList exports.node))), [])
  -- :- module(name).  (no export list — exports everything)
  Compound "module" [Ann (Atom name) _] ->
    (DirModule name loc body.node Nothing, [])
  -- :- use_module(name).  or  :- use_module(library(name)).
  Compound "use_module" [imp, importList] ->
    case convertImportWithList loc body.node imp importList of
      Right ann -> (DirImport ann, [])
      Left err -> (DirOther, [err])
  Compound "use_module" [imp] ->
    case convertImport loc body.node imp of
      Right ann -> (DirImport ann, [])
      Left err -> (DirOther, [err])
  -- :- chr_constraint leq/2, fib/2.
  -- Parsed as prefix op: Compound "chr_constraint" [body]
  Compound "chr_constraint" [decls] ->
    let pieces = flattenComma decls
        results = map convertConstraintDecl pieces
        decls' = map fst results
        errs = concatMap snd results
     in (DirConstraintDecl decls', errs)
  -- :- function foo/2.  or  :- function factorial(int) -> int.
  Compound "function" [decls] ->
    let pieces = flattenComma decls
        results = map convertFunctionDecl pieces
        decls' = map fst results
        innerErrs = concatMap snd results
        multiSigErrs = multiSigRequiringErrors loc body.node decls'
     in (DirFunctionDecl decls', innerErrs ++ multiSigErrs)
  -- :- open_function foo/2.
  Compound "open_function" [decls] ->
    let pieces = flattenComma decls
        results = map convertOpenFunctionDecl pieces
        decls' = map fst results
        innerErrs = concatMap snd results
        multiSigErrs = multiSigRequiringErrors loc body.node decls'
     in (DirOpenFunctionDecl decls', innerErrs ++ multiSigErrs)
  -- :- extend_function_type (foo(int) -> int).
  Compound "extend_function_type" [decls] ->
    let pieces = flattenComma decls
        results = map convertExtendFunctionTypeDecl pieces
        decls' = map fst results
        errs = concatMap snd results
     in (DirExtendFunctionTypeDecl decls', errs)
  -- :- extend_function name(args) [| guards] -> body.
  Compound "extend_function" [eqn] ->
    (DirExtendFunctionEqn (convertFunctionEquation eqn), [])
  -- :- chr_type name ---> con1 ; con2 ; ...
  -- Parsed as prefix op: Compound "chr_type" [Compound "--->" [head, alts]]
  Compound "chr_type" [typeBody] ->
    (DirTypeDecl [convertTypeDefinition typeBody], [])
  -- Unknown directives (e.g. :- dynamic foo/1.)
  _ -> (DirOther, [])
convertDirective _ = (DirOther, [])

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
-- a module name or @library(name)@.
convertImportWithList ::
  SourceLoc ->
  PExpr ->
  Ann PExpr ->
  Ann PExpr ->
  Either (AnnP ParseValidationError) (AnnP Import)
convertImportWithList dirLoc dirPExpr imp importList =
  let items = map convertExportItem (unfoldList importList.node)
   in case imp.node of
        Compound "library" [Ann (Atom name) _] ->
          Right (AnnP (LibraryImport name (Just items)) dirLoc dirPExpr)
        Atom name -> Right (AnnP (ModuleImport name (Just items)) dirLoc dirPExpr)
        _ -> Left (AnnP MalformedImport imp.sourceLoc imp.node)

-- | Report a 'RequiringOnMultiSig' error for every declaration in a
-- comma-separated group of two or more function declarations that
-- carries a @requiring@ clause. A single-decl group is the normal
-- bounded form and produces no error. The shared location and origin
-- come from the surrounding directive so the diagnostic points at the
-- whole @:- function@.
multiSigRequiringErrors ::
  SourceLoc -> PExpr -> [Ann Declaration] -> [AnnP ParseValidationError]
multiSigRequiringErrors loc origin decls
  | length decls < 2 = []
  | otherwise =
      [ AnnP (RequiringOnMultiSig d.name) loc origin
      | Ann d _ <- decls,
        case d of
          FunctionDecl {requiring = Just _} -> True
          _ -> False
      ]

-- | Convert an export item PExpr to a 'Declaration'.
convertExportItem :: Ann PExpr -> Declaration
convertExportItem (Ann pexpr _) = case pexpr of
  Compound "fun" [Ann (Compound "/" [Ann (Atom name) _, Ann (P.Int arity) _]) _] ->
    FunctionDecl name arity Nothing Nothing False Nothing
  Compound "/" [Ann (Atom name) _, Ann (P.Int arity) _] ->
    ConstraintDecl name arity Nothing Nothing
  Compound "op" [Ann (P.Int fix) _, Ann tyExpr _, Ann nameExpr _]
    | Just ty <- parseOpTypeFromPExpr tyExpr,
      Just name <- atomName nameExpr ->
        OperatorDecl (OpDecl fix ty name)
  Compound "type" [Ann (Compound "/" [Ann (Atom name) _, Ann (P.Int arity) _]) _] ->
    TypeExportDecl name arity Nothing
  Compound
    "type"
    [ Ann (Compound "/" [Ann (Atom name) _, Ann (P.Int arity) _]) _,
      Ann conList _
      ] ->
      TypeExportDecl name arity (Just [c | Ann (Atom c) _ <- unfoldList conList])
  _ -> ConstraintDecl "<unknown>" 0 Nothing Nothing

-- | Convert a PExpr to a constraint declaration. Returns both the
-- 'Declaration' and any parse-validation errors found (currently only
-- @requiring@ on an untyped constraint, which is silently ignored — the
-- spec restricts @requiring@ to typed forms).
convertConstraintDecl :: Ann PExpr -> (Ann Declaration, [AnnP ParseValidationError])
convertConstraintDecl (Ann pexpr loc) = case pexpr of
  -- @sig requiring bound, ...@
  Compound "requiring" [sig, bounds] ->
    case sig.node of
      Compound name args ->
        let bs = map convertBoundSig (flattenComma bounds)
         in ( Ann
                ( ConstraintDecl
                    name
                    (length args)
                    (Just (map convertTypeExpr args))
                    (Just bs)
                )
                loc,
              []
            )
      _ ->
        -- Malformed: @requiring@ on an untyped or non-compound LHS.
        (Ann (ConstraintDecl "<unknown>" 0 Nothing Nothing) loc, [])
  -- Untyped: name/arity
  Compound "/" [Ann (Atom name) _, Ann (P.Int arity) _] ->
    (Ann (ConstraintDecl name arity Nothing Nothing) loc, [])
  -- Typed: name(type, ...)
  Compound name args ->
    (Ann (ConstraintDecl name (length args) (Just (map convertTypeExpr args)) Nothing) loc, [])
  -- Zero-arity bare atom
  Atom name ->
    (Ann (ConstraintDecl name 0 Nothing Nothing) loc, [])
  _ -> (Ann (ConstraintDecl "<unknown>" 0 Nothing Nothing) loc, [])

-- | Convert a PExpr to a closed-function declaration.
convertFunctionDecl :: Ann PExpr -> (Ann Declaration, [AnnP ParseValidationError])
convertFunctionDecl = convertFunctionDeclWith False

-- | Convert a PExpr to an open-function declaration.
convertOpenFunctionDecl :: Ann PExpr -> (Ann Declaration, [AnnP ParseValidationError])
convertOpenFunctionDecl = convertFunctionDeclWith True

-- | Convert a PExpr to an extension type declaration.
-- Only the typed form @name(types) -> type@ is supported: an extension
-- declaration that does not carry a signature has nothing to contribute.
--
-- A @requiring@ clause on an @:- extend_function_type@ is rejected
-- syntactically: bounds belong to the original declaration, not to
-- an extension.
convertExtendFunctionTypeDecl :: Ann PExpr -> (Ann Declaration, [AnnP ParseValidationError])
convertExtendFunctionTypeDecl (Ann pexpr loc) = case pexpr of
  Compound "requiring" [sig, _] ->
    let (declAnn, errs) = convertExtendFunctionTypeDecl sig
        targetName = case sig.node of
          Compound "->" [Ann (Compound n _) _, _] -> n
          _ -> "<unknown>"
        err = AnnP (RequiringOnExtendFunctionType targetName) loc pexpr
     in (declAnn, err : errs)
  Compound "->" [Ann (Compound name args) _, ret] ->
    ( Ann
        ( ExtendFunctionTypeDecl
            name
            (length args)
            (Just (map convertTypeExpr args))
            (Just (convertTypeExpr ret))
            Nothing
        )
        loc,
      []
    )
  _ -> (Ann (ExtendFunctionTypeDecl "<unknown>" 0 Nothing Nothing Nothing) loc, [])

-- | Shared implementation of 'convertFunctionDecl' and
-- 'convertOpenFunctionDecl'. The 'Bool' argument is the @open@ flag stored
-- on the resulting 'FunctionDecl'. Returns parse-validation errors for
-- malformed @requiring@ placements.
convertFunctionDeclWith ::
  Bool -> Ann PExpr -> (Ann Declaration, [AnnP ParseValidationError])
convertFunctionDeclWith open (Ann pexpr loc) = case pexpr of
  -- @name(types) -> ret requiring bound, ...@
  Compound "requiring" [sig, bounds] ->
    case sig.node of
      Compound "->" [Ann (Compound name args) _, ret] ->
        let bs = map convertBoundSig (flattenComma bounds)
         in ( Ann
                ( FunctionDecl
                    name
                    (length args)
                    (Just (map convertTypeExpr args))
                    (Just (convertTypeExpr ret))
                    open
                    (Just bs)
                )
                loc,
              []
            )
      _ ->
        -- Malformed: @requiring@ on a non-typed signature. Drop the
        -- requiring clause and fall through to the malformed-decl
        -- placeholder used elsewhere; there is nothing meaningful to
        -- attach the bounds to.
        (Ann (FunctionDecl "<unknown>" 0 Nothing Nothing open Nothing) loc, [])
  -- Untyped: name/arity
  Compound "/" [Ann (Atom name) _, Ann (P.Int arity) _] ->
    (Ann (FunctionDecl name arity Nothing Nothing open Nothing) loc, [])
  -- Typed: name(type, ...) -> type
  Compound "->" [Ann (Compound name args) _, ret] ->
    ( Ann
        ( FunctionDecl
            name
            (length args)
            (Just (map convertTypeExpr args))
            (Just (convertTypeExpr ret))
            open
            Nothing
        )
        loc,
      []
    )
  _ -> (Ann (FunctionDecl "<unknown>" 0 Nothing Nothing open Nothing) loc, [])

-- | Convert a single bound signature inside a @requiring@ clause. The
-- expected shape is @name(τ₁, ..., τₙ) -> τᵣ@. A name appearing without
-- arguments (e.g. @foo -> bool@) is treated as a zero-arity bound. A
-- malformed shape yields a placeholder bound that the resolver's
-- 'unknown_bound_function' check will reject.
convertBoundSig :: Ann PExpr -> BoundSig
convertBoundSig (Ann pexpr loc) = case pexpr of
  Compound "->" [Ann (Compound name args) _, ret] ->
    BoundSig
      { name = Unqualified name,
        arity = length args,
        argTypes = map convertTypeExpr args,
        returnType = convertTypeExpr ret,
        loc = loc
      }
  Compound "->" [Ann (Atom name) _, ret] ->
    BoundSig
      { name = Unqualified name,
        arity = 0,
        argTypes = [],
        returnType = convertTypeExpr ret,
        loc = loc
      }
  _ ->
    BoundSig
      { name = Unqualified "<unknown>",
        arity = 0,
        argTypes = [],
        returnType = TypeCon (Unqualified "any") [],
        loc = loc
      }

-- | Convert a PExpr to a 'TypeExpr'.
convertTypeExpr :: Ann PExpr -> TypeExpr
convertTypeExpr (Ann pexpr _) = case pexpr of
  Var t -> TypeVar t
  Atom "[]" -> TypeCon (Unqualified "[]") []
  Atom name -> TypeCon (Unqualified name) []
  -- See Note [Qualified name handling].
  Compound ":" [Ann (Atom m) _, Ann (Atom n) _] ->
    TypeCon (Qualified m n) []
  Compound ":" [Ann (Atom m) _, Ann (Compound n args) _] ->
    TypeCon (Qualified m n) (map convertTypeExpr args)
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
     in Ann (TypeDefinition (Unqualified tname) tvars cons loc) loc
  _ -> Ann (TypeDefinition (Unqualified "<unknown>") [] [] loc) loc

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

-- ** Rule conversion

-- | Convert a top-level PExpr to a 'Rule', collecting any
-- 'MalformedConstraint' errors found in its head.
convertRule :: Ann PExpr -> (Rule, [AnnP ParseValidationError])
convertRule expr =
  let (mName, ruleExpr) = case expr.node of
        Compound "@" [Ann (Atom name) nameLoc, body] ->
          (Just (Ann name nameLoc), body)
        _ -> (Nothing, expr)
      ((head_, headErrs), guardBody) = case ruleExpr.node of
        Compound "<=>" [h, gb] -> (convertHead h, gb)
        Compound "==>" [h, gb] -> (convertPropagationHead h, gb)
        _ -> ((noAnnP (Simplification []), []), ruleExpr) -- fallback
      (guard_, body_) = splitGuardBody guardBody
   in (Rule mName head_ guard_ body_, headErrs)

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
    ( AnnP [] expr.sourceLoc (Atom ""),
      AnnP (map convertTerm (flattenComma expr)) expr.sourceLoc expr.node
    )

-- ** Function equation conversion

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
    AnnP
      ( FunctionEquation
          (Unqualified "<unknown>")
          []
          (AnnP [] loc (Atom ""))
          ( AnnP
              (convertTerm (Ann pexpr loc))
              loc
              pexpr
          )
      )
      loc
      pexpr

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
