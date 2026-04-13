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
    collectOperatorDecls,
    extractOpDecls,
  )
where

import Data.Text (Text)
import Data.Void (Void)
import Text.Megaparsec (ParseErrorBundle)
import YCHR.PExpr (PExpr (Atom, Compound, Str, Var))
import YCHR.PExpr qualified as P
import YCHR.Parsed
import YCHR.Types (Name (..))

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
      (1180, [(P.Fx, "chr_constraint"), (P.Fx, "chr_type"), (P.Fx, "function")]),
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
  Either (ParseErrorBundle Text Void) Module
parseModule = parseModuleWith builtinOps

-- | Parse a CHR module from source text using a custom operator table.
parseModuleWith ::
  OpTable ->
  String ->
  Text ->
  Either (ParseErrorBundle Text Void) Module
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
-- First-pass operator collector
-- ---------------------------------------------------------------------------

-- | Minimal operator table for the first pass: only enough to parse
-- the @:- module(name, [exports]).@ directive.
firstPassTable :: OpTable
firstPassTable =
  P.mkOpTable
    [ (400, [(P.Yfx, "/")]),
      (1200, [(P.Fx, ":-")])
    ]

-- | Collect operator declarations from a module's @:- module(...)@ directive.
--
-- Since the module directive is always at the top of the file, this parser
-- attempts to parse the first dot-terminated term and extract any @op(...)@
-- entries from the export list. If no module directive is found, returns @[]@.
collectOperatorDecls :: String -> Text -> Either (ParseErrorBundle Text Void) [OpDecl]
collectOperatorDecls sourceName src = do
  mTerm <- P.parseFirstTerm firstPassTable sourceName src
  pure $ case mTerm of
    Just (Ann (Compound ":-" [Ann (Compound "module" [_, exports]) _]) _) ->
      extractOpDeclsFromPExpr exports.node
    _ -> []

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
  Just exports -> [op | OperatorDecl op <- exports]

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
  = DirModule Text [Declaration]
  | DirImport (Ann Import)
  | DirConstraintDecl [Ann Declaration]
  | DirFunctionDecl [Ann Declaration]
  | DirTypeDecl [Ann TypeDefinition]
  | DirOther

-- | Internal module item type.
data ModuleItem
  = ItemDirective Directive
  | ItemRule Rule
  | ItemEquation (Ann FunctionEquation)

-- | Convert a list of top-level PExpr terms to a 'Module'.
convertModule :: [Ann PExpr] -> Module
convertModule terms =
  let items = map convertModuleItem terms
      dirs = [d | ItemDirective d <- items]
      rules = [r | ItemRule r <- items]
      eqs = [e | ItemEquation e <- items]
      (modName_, modExports_) = case [(n, e) | DirModule n e <- dirs] of
        ((n, e) : _) -> (n, Just e)
        [] -> ("<no_module>", Nothing)
      modImports_ = [n | DirImport n <- dirs]
      modDecls_ =
        concat [ds | DirConstraintDecl ds <- dirs]
          ++ concat [ds | DirFunctionDecl ds <- dirs]
      modTypeDecls_ = concat [ds | DirTypeDecl ds <- dirs]
   in Module modName_ modImports_ modDecls_ modTypeDecls_ rules eqs modExports_

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
convertDirective (Ann (Compound ":-" [body]) _) = case body.node of
  -- :- module(name, [exports]).
  Compound "module" [Ann (Atom name) _, exports] ->
    DirModule name (map convertExportItem (unfoldList exports.node))
  -- :- use_module(name).  or  :- use_module(library(name)).
  Compound "use_module" [imp] ->
    DirImport (convertImport imp)
  -- :- chr_constraint leq/2, fib/2.
  -- Parsed as prefix op: Compound "chr_constraint" [body]
  Compound "chr_constraint" [decls] ->
    DirConstraintDecl (map convertConstraintDecl (flattenComma decls))
  -- :- function foo/2.  or  :- function factorial(int) -> int.
  Compound "function" [decls] ->
    DirFunctionDecl (map convertFunctionDecl (flattenComma decls))
  -- :- chr_type name ---> con1 ; con2 ; ...
  -- Parsed as prefix op: Compound "chr_type" [Compound "--->" [head, alts]]
  Compound "chr_type" [typeBody] ->
    DirTypeDecl [convertTypeDefinition typeBody]
  -- Unknown directives (e.g. :- dynamic foo/1.)
  _ -> DirOther
convertDirective _ = DirOther

-- | Convert an import PExpr.
convertImport :: Ann PExpr -> Ann Import
convertImport (Ann pexpr loc) = case pexpr of
  Compound "library" [Ann (Atom name) _] -> Ann (LibraryImport name) loc
  Atom name -> Ann (ModuleImport name) loc
  _ -> Ann (ModuleImport "<unknown>") loc

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
convertFunctionDecl (Ann pexpr loc) = case pexpr of
  -- Untyped: name/arity
  Compound "/" [Ann (Atom name) _, Ann (P.Int arity) _] ->
    Ann (FunctionDecl name arity Nothing Nothing) loc
  -- Typed: name(type, ...) -> type
  Compound "->" [Ann (Compound name args) _, ret] ->
    Ann
      ( FunctionDecl
          name
          (length args)
          (Just (map convertTypeExpr args))
          (Just (convertTypeExpr ret))
      )
      loc
  _ -> Ann (FunctionDecl "<unknown>" 0 Nothing Nothing) loc

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
        _ -> (noAnn (Simplification []), ruleExpr) -- fallback
      (guard_, body_) = splitGuardBody guardBody
   in Rule mName head_ guard_ body_

-- | Convert the head of a simplification or simpagation rule.
convertHead :: Ann PExpr -> Ann Head
convertHead expr@(Ann pexpr loc) = case pexpr of
  Compound "\\" [kept, removed] ->
    Ann
      ( Simpagation
          (map convertConstraint (flattenComma kept))
          (map convertConstraint (flattenComma removed))
      )
      loc
  _ ->
    Ann (Simplification (map convertConstraint (flattenComma expr))) loc

-- | Convert the head of a propagation rule.
convertPropagationHead :: Ann PExpr -> Ann Head
convertPropagationHead expr =
  Ann (Propagation (map convertConstraint (flattenComma expr))) expr.sourceLoc

-- | Split a guard|body PExpr into guard and body term lists.
splitGuardBody :: Ann PExpr -> (Ann [Term], Ann [Term])
splitGuardBody expr = case expr.node of
  Compound "|" [guard_, body_] ->
    ( Ann (map convertTerm (flattenComma guard_)) guard_.sourceLoc,
      Ann (map convertTerm (flattenComma body_)) body_.sourceLoc
    )
  _ ->
    ( Ann [] expr.sourceLoc,
      Ann (map convertTerm (flattenComma expr)) expr.sourceLoc
    )

-- ---------------------------------------------------------------------------
-- Function equation conversion
-- ---------------------------------------------------------------------------

-- | Convert a top-level PExpr to a 'FunctionEquation'.
convertFunctionEquation :: Ann PExpr -> Ann FunctionEquation
convertFunctionEquation expr@(Ann pexpr loc) = case pexpr of
  Compound "->" [lhs, rhs] ->
    case lhs.node of
      -- Guarded: lhs_pattern | guard -> rhs
      Compound "|" [pat, guard_] ->
        let (name, args) = extractFunNameArgs pat
         in Ann
              ( FunctionEquation
                  name
                  args
                  (Ann (map convertTerm (flattenComma guard_)) guard_.sourceLoc)
                  (Ann (convertTerm rhs) rhs.sourceLoc)
              )
              loc
      -- Unguarded: lhs_pattern -> rhs
      _ ->
        let (name, args) = extractFunNameArgs lhs
         in Ann
              ( FunctionEquation
                  name
                  args
                  (Ann [] lhs.sourceLoc)
                  (Ann (convertTerm rhs) rhs.sourceLoc)
              )
              loc
  _ ->
    Ann (FunctionEquation "<unknown>" [] (Ann [] loc) (Ann (convertTerm expr) loc)) loc

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
