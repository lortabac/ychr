{-# LANGUAGE OverloadedStrings #-}

-- | Pretty-printing utilities for CHR terms and binding maps.
module YCHR.Pretty
  ( -- * Pretty-printing functions
    prettyTerm,
    prettyBindings,
    prettyQueryResult,
    prettyTermSrc,
    prettyConstraintSrc,
    prettyHeadSrc,
    prettyRuleSrc,
    prettyPExprSrc,
    renderAtom,

    -- * Declaration pretty-printers
    DeclKind (..),
    prettyQualifiedName,
    prettyConstraintDecl,
    prettyFunctionDecl,
    prettyTypeDecl,
    prettyTypeExpr,
  )
where

import Data.Char (isUpper)
import Data.List (intercalate)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Text (Text)
import Data.Text qualified as T
import YCHR.Loc (Ann (..), noAnn)
import YCHR.PExpr qualified as PE
import YCHR.Parsed qualified as P
import YCHR.Parser (builtinOps)
import YCHR.Types
  ( BoundSig (..),
    Constraint (..),
    DataConstructor (..),
    Name (..),
    QualifiedName (..),
    Term (..),
    TypeDefinition (..),
    TypeExpr (..),
  )

-- ---------------------------------------------------------------------------
-- Operator table for source pretty-printing
-- ---------------------------------------------------------------------------

-- | Operator table for source pretty-printing.
-- Extends 'builtinOps' with the standard arithmetic\/comparison operators
-- from the builtins library.
prettyOps :: PE.OpTable
prettyOps = case PE.mergeOps builtinOps stdArithOps of
  Right t -> t
  Left _ -> builtinOps
  where
    stdArithOps =
      [ (200, PE.Fy, "-"),
        (500, PE.Yfx, "+"),
        (500, PE.Yfx, "-"),
        (400, PE.Yfx, "*"),
        (400, PE.Yfx, "div"),
        (400, PE.Yfx, "mod"),
        (400, PE.Yfx, "rem"),
        (700, PE.Xfx, "<"),
        (700, PE.Xfx, ">"),
        (700, PE.Xfx, ">="),
        (700, PE.Xfx, "=<"),
        (700, PE.Xfx, "==")
      ]

-- ---------------------------------------------------------------------------
-- AST → PExpr conversion
-- ---------------------------------------------------------------------------

-- | Convert a 'Term' to a 'PE.PExpr'.
-- This is the inverse of 'convertTerm' in "YCHR.Parser".
termToPExpr :: Term -> PE.PExpr
termToPExpr (VarTerm v) = PE.Var v
termToPExpr (IntTerm n) = PE.Int n
termToPExpr (FloatTerm n) = PE.Float n
termToPExpr (TextTerm s) = PE.Str s
termToPExpr Wildcard = PE.Wildcard
termToPExpr (CompoundTerm (Unqualified f) []) = PE.Atom f
termToPExpr (CompoundTerm (Qualified m f) []) =
  PE.Compound ":" [noAnn (PE.Atom m), noAnn (PE.Atom f)]
termToPExpr (CompoundTerm (Qualified m f) args) =
  PE.Compound ":" [noAnn (PE.Atom m), noAnn (PE.Compound f (map (noAnn . termToPExpr) args))]
termToPExpr (CompoundTerm (Unqualified f) args) =
  PE.Compound f (map (noAnn . termToPExpr) args)

-- | Convert a 'Constraint' to a 'PE.PExpr'.
-- This is the inverse of 'convertConstraint' in "YCHR.Parser".
constraintToPExpr :: Constraint -> PE.PExpr
constraintToPExpr (Constraint (Unqualified name) args) =
  PE.Compound name (map (noAnn . termToPExpr) args)
constraintToPExpr (Constraint (Qualified m name) args) =
  PE.Compound
    ":"
    [ noAnn (PE.Atom m),
      noAnn (PE.Compound name (map (noAnn . termToPExpr) args))
    ]

-- | Convert a parsed 'P.Head' to a 'PE.PExpr'.
headToPExpr :: P.Head -> PE.PExpr
headToPExpr (P.Simplification cs) = commaSepPExpr (map constraintToPExpr cs)
headToPExpr (P.Propagation cs) = commaSepPExpr (map constraintToPExpr cs)
headToPExpr (P.Simpagation ks rs) =
  PE.Compound
    "\\"
    [ noAnn (commaSepPExpr (map constraintToPExpr ks)),
      noAnn (commaSepPExpr (map constraintToPExpr rs))
    ]

-- | Convert a parsed 'P.Rule' to a 'PE.PExpr'.
ruleToPExpr :: P.Rule -> PE.PExpr
ruleToPExpr r =
  let headPE = headToPExpr r.head.node
      arrow = case r.head.node of
        P.Propagation {} -> "==>"
        _ -> "<=>"
      bodyPE = commaSepPExpr (map termToPExpr r.body.node)
      guardAndBody = case r.guard.node of
        [] -> bodyPE
        gs -> PE.Compound "|" [noAnn (commaSepPExpr (map termToPExpr gs)), noAnn bodyPE]
      arrowExpr = PE.Compound arrow [noAnn headPE, noAnn guardAndBody]
   in case r.name of
        Nothing -> arrowExpr
        Just ann -> PE.Compound "@" [noAnn (PE.Atom ann.node), noAnn arrowExpr]

-- | Right-fold a list of 'PE.PExpr' into a comma-operator chain.
commaSepPExpr :: [PE.PExpr] -> PE.PExpr
commaSepPExpr [] = PE.Atom "true"
commaSepPExpr [x] = x
commaSepPExpr (x : xs) = PE.Compound "," [noAnn x, noAnn (commaSepPExpr xs)]

-- ---------------------------------------------------------------------------
-- Surface pretty-printers (via PExpr)
-- ---------------------------------------------------------------------------

-- | Render a 'Term' as valid surface-language source text.
-- Unlike 'prettyTerm', variable names are preserved rather than collapsed to @_@.
prettyTermSrc :: Term -> String
prettyTermSrc = PE.prettyPExpr prettyOps . termToPExpr

-- | Render a 'Constraint' as valid surface-language source text.
prettyConstraintSrc :: Constraint -> String
prettyConstraintSrc = PE.prettyPExpr prettyOps . constraintToPExpr

-- | Render a parsed 'P.Head' as valid surface-language source text.
prettyHeadSrc :: P.Head -> String
prettyHeadSrc = PE.prettyPExpr prettyOps . headToPExpr

-- | Render a parsed 'P.Rule' as valid surface-language source text.
prettyRuleSrc :: P.Rule -> String
prettyRuleSrc r = PE.prettyPExpr prettyOps (ruleToPExpr r) ++ "."

-- | Render an atom, quoting with @\'...\'@ if necessary.
renderAtom :: Text -> String
renderAtom = PE.renderAtom prettyOps.wordOpSet

-- ---------------------------------------------------------------------------
-- Runtime pretty-printer (via PExpr)
-- ---------------------------------------------------------------------------

-- | Render a 'Term' as a Prolog-compatible string.
-- 'Wildcard' is shown as @_@; 'VarTerm' is shown by its name (it
-- appears here only when 'YCHR.Meta.valueToTerm' decided to surface
-- an alias for an unbound variable).
-- Operators are displayed using their declared fixity and precedence.
prettyTerm :: Term -> String
prettyTerm = PE.prettyPExpr prettyOps . runtimeToPExpr

-- | Convert a runtime 'Term' to a 'PE.PExpr' for pretty-printing.
-- Like 'termToPExpr' but renders 'Wildcard' as @_@ (the form
-- 'YCHR.Meta.valueToTerm' uses for unaliased free variables) and
-- unwraps closure terms to show their source form.
runtimeToPExpr :: Term -> PE.PExpr
runtimeToPExpr (VarTerm v) = PE.Var v
runtimeToPExpr Wildcard = PE.Wildcard
runtimeToPExpr (CompoundTerm (Unqualified "__closure") (_ : sourceForm : _)) =
  unquoteToPExpr sourceForm
-- Canonicalized cons/nil: render as the surface list syntax. This
-- mirrors the analogous case in 'YCHR.Meta.valueToTerm', kept here too
-- because Term values constructed without going through 'valueToTerm'
-- (e.g. round-trips of already-rendered runtime values) still hit
-- this path.
runtimeToPExpr (CompoundTerm (Unqualified "prelude__[]") []) = PE.Atom "[]"
runtimeToPExpr (CompoundTerm (Qualified "prelude" "[]") []) = PE.Atom "[]"
runtimeToPExpr (CompoundTerm (Unqualified "prelude__.") args) =
  PE.Compound "." (map (noAnn . runtimeToPExpr) args)
runtimeToPExpr (CompoundTerm (Unqualified f) []) = PE.Atom f
runtimeToPExpr (CompoundTerm (Qualified m f) []) =
  PE.Compound ":" [noAnn (PE.Atom m), noAnn (PE.Atom f)]
runtimeToPExpr (CompoundTerm (Qualified m f) args) =
  PE.Compound
    ":"
    [ noAnn (PE.Atom m),
      noAnn (PE.Compound f (map (noAnn . runtimeToPExpr) args))
    ]
runtimeToPExpr (CompoundTerm (Unqualified f) args) =
  PE.Compound f (map (noAnn . runtimeToPExpr) args)
runtimeToPExpr (IntTerm n) = PE.Int n
runtimeToPExpr (FloatTerm n) = PE.Float n
runtimeToPExpr (TextTerm s) = PE.Str s

-- | Like 'runtimeToPExpr' but reverses the 'quoteTerm' transformation:
-- atoms that look like variable names (start with uppercase or @_@) are
-- rendered as variables. Used for closure source forms where 'quoteTerm'
-- has turned @VarTerm v@ into a 0-arity unqualified compound.
unquoteToPExpr :: Term -> PE.PExpr
unquoteToPExpr (CompoundTerm (Unqualified s) [])
  | Just (c, _) <- T.uncons s, isUpper c || c == '_' = PE.Var s
  | otherwise = PE.Atom s
unquoteToPExpr (CompoundTerm (Unqualified f) args) =
  PE.Compound f (map (noAnn . unquoteToPExpr) args)
unquoteToPExpr (CompoundTerm (Qualified m f) []) =
  PE.Compound ":" [noAnn (PE.Atom m), noAnn (PE.Atom f)]
unquoteToPExpr (CompoundTerm (Qualified m f) args) =
  PE.Compound
    ":"
    [ noAnn (PE.Atom m),
      noAnn (PE.Compound f (map (noAnn . unquoteToPExpr) args))
    ]
unquoteToPExpr t = runtimeToPExpr t

-- ---------------------------------------------------------------------------
-- User-facing output (binding map)
-- ---------------------------------------------------------------------------

-- | Serialize a variable binding map to the golden file format.
--
-- Keys are sorted alphabetically for determinism. Each line has the form
-- @K = V@ followed by a newline, matching the output of 'unlines'.
prettyBindings :: Map Text Term -> String
prettyBindings m =
  unlines [T.unpack k ++ " = " ++ prettyTerm v | (k, v) <- Map.toAscList m]

-- | Render a variable binding map as a Prolog-style query result.
--
-- Variables starting with @_@ are filtered out (internal/wildcard).
-- If no user-visible bindings remain, returns an empty string.
-- Otherwise, comma-separated @K = V@ lines terminated with a dot.
prettyQueryResult :: Map Text Term -> String
prettyQueryResult m =
  let visible = [(k, v) | (k, v) <- Map.toAscList m, not ("_" `T.isPrefixOf` k)]
   in case visible of
        [] -> ""
        _ -> formatBindings visible
  where
    formatBindings [] = ""
    formatBindings [(k, v)] = T.unpack k ++ " = " ++ prettyTerm v ++ ".\n"
    formatBindings ((k, v) : rest) =
      T.unpack k ++ " = " ++ prettyTerm v ++ ",\n" ++ formatBindings rest

-- | Render a 'PExpr' as valid surface-language source text.
prettyPExprSrc :: PE.PExpr -> String
prettyPExprSrc = PE.prettyPExpr prettyOps

-- ---------------------------------------------------------------------------
-- Declaration pretty-printers (used by the REPL @:info@ command)
-- ---------------------------------------------------------------------------

-- | The four flavors a 'FunctionDef' can have, recovered by the
-- @:info@ command from the original 'P.Declaration' kept in
-- 'CompiledProgram.allModules'.
data DeclKind
  = DKFunction
  | DKOpenFunction
  | DKClass
  | DKOpenClass
  deriving (Show, Eq)

declKindKeyword :: DeclKind -> String
declKindKeyword DKFunction = "function"
declKindKeyword DKOpenFunction = "open_function"
declKindKeyword DKClass = "class"
declKindKeyword DKOpenClass = "open_class"

-- | Convert a 'TypeExpr' to a 'PE.PExpr' for pretty-printing. The
-- module qualifier on 'Qualified' constructors is intentionally
-- dropped: declaration-body rendering follows the user-facing
-- source form where types are usually written unqualified. The
-- qualified name is still shown on the header line of @:info@
-- output, so no information is lost. The special case for
-- @TypeCon (Unqualified ".") args@ preserves the surface @[H|T]@
-- list-cons syntax.
typeExprToPExpr :: TypeExpr -> PE.PExpr
typeExprToPExpr (TypeVar v) = PE.Var v
typeExprToPExpr (TypeCon (Unqualified ".") args) =
  PE.Compound "." (map (noAnn . typeExprToPExpr) args)
typeExprToPExpr (TypeCon name []) = PE.Atom (typeConBaseName name)
typeExprToPExpr (TypeCon name args) =
  PE.Compound (typeConBaseName name) (map (noAnn . typeExprToPExpr) args)

typeConBaseName :: Name -> Text
typeConBaseName (Unqualified n) = n
typeConBaseName (Qualified _ n) = n

-- | Render a 'TypeExpr' as valid surface-language source text.
prettyTypeExpr :: TypeExpr -> String
prettyTypeExpr = PE.prettyPExpr prettyOps . typeExprToPExpr

-- | Render a 'QualifiedName' as @mod:name@ with both halves atom-quoted
-- where necessary (so @prelude:'+'@ comes out correctly).
prettyQualifiedName :: QualifiedName -> String
prettyQualifiedName (QualifiedName m n) = renderAtom m ++ ":" ++ renderAtom n

-- | Render a function signature @name(T1, ..., Tn) -> Tret@. The name
-- is rendered through 'renderAtom' so operator names like @'+'@ quote
-- correctly. Used for both standalone declarations and elements of a
-- multi-sig @:- class@ list.
prettyFunSig :: Text -> [TypeExpr] -> TypeExpr -> String
prettyFunSig name argTys retTy =
  renderAtom name
    ++ "("
    ++ intercalate ", " (map prettyTypeExpr argTys)
    ++ ") -> "
    ++ prettyTypeExpr retTy

-- | Render a single bound signature in a @requiring@ clause, using
-- the bound's base name (qualified-name module is dropped to match
-- the surface @requiring@ form).
prettyBoundSig :: BoundSig -> String
prettyBoundSig b =
  let baseName = case b.name of
        Unqualified n -> n
        Qualified _ n -> n
   in prettyFunSig baseName b.argTypes b.returnType

-- | Render a list of bounds as the @requiring B1, B2, ..., Bn@ trailer
-- (no leading space, no trailing period). Empty input renders as the
-- empty string so callers can append unconditionally.
prettyRequiring :: [BoundSig] -> String
prettyRequiring [] = ""
prettyRequiring bs = " requiring " ++ intercalate ", " (map prettyBoundSig bs)

-- | Render a @:- chr_constraint@ declaration. The base name (not the
-- qualified form) is used inside the declaration body, matching the
-- surface syntax users write. Untyped constraints use the @name/arity@
-- form; typed constraints use the @name(T1, ..., Tn)@ form, optionally
-- followed by a @requiring@ clause.
prettyConstraintDecl :: QualifiedName -> Int -> Maybe [TypeExpr] -> [BoundSig] -> String
prettyConstraintDecl qn arity mArgTys bounds = case mArgTys of
  Nothing ->
    ":- chr_constraint " ++ renderAtom qn.baseName ++ "/" ++ show arity ++ "."
  Just argTys ->
    ":- chr_constraint "
      ++ renderAtom qn.baseName
      ++ "("
      ++ intercalate ", " (map prettyTypeExpr argTys)
      ++ ")"
      ++ prettyRequiring bounds
      ++ "."

-- | Render a function-flavored declaration (@:- function@,
-- @:- open_function@, @:- class@, @:- open_class@). Single-signature
-- forms stay on one line; multi-signature forms switch to the indented
-- per-line layout used in @libraries\/prelude.chr@. A @requiring@ clause
-- is only emitted for function-flavored kinds; it is rejected on
-- classes by the parser, so a non-empty bound list there is silently
-- dropped.
prettyFunctionDecl ::
  QualifiedName ->
  Int ->
  [([TypeExpr], TypeExpr)] ->
  [BoundSig] ->
  DeclKind ->
  String
prettyFunctionDecl qn arity sigs bounds kind =
  let keyword = declKindKeyword kind
      isFunction = kind == DKFunction || kind == DKOpenFunction
      reqStr = if isFunction then prettyRequiring bounds else ""
   in case sigs of
        [] ->
          -- An unsignatured function declaration falls back to the
          -- @name/arity@ form. This shape is not currently produced by
          -- the resolver but is handled here so the printer is total.
          ":- " ++ keyword ++ " " ++ renderAtom qn.baseName ++ "/" ++ show arity ++ "."
        [(argTys, retTy)] ->
          ":- " ++ keyword ++ " " ++ prettyFunSig qn.baseName argTys retTy ++ reqStr ++ "."
        _ ->
          let oneSig (argTys, retTy) = "    (" ++ prettyFunSig qn.baseName argTys retTy ++ ")"
           in ":- " ++ keyword ++ "\n" ++ intercalate ",\n" (map oneSig sigs) ++ reqStr ++ "."

-- | Render a @:- chr_type@ declaration: the type head (with its type
-- variables) followed by @--->@ and the list of data constructors
-- separated by @;@. The type's base name is used unqualified, matching
-- the surface form. Constructor rendering is routed through 'PE.PExpr'
-- so the empty-list atom and cons-cell list constructor render with
-- their surface @[]@ \/ @[H|T]@ syntax rather than as quoted @'[]'@ \/
-- @'.'(H, T)@.
prettyTypeDecl :: TypeDefinition -> String
prettyTypeDecl td =
  let tname = renderAtom (typeConBaseName td.name)
      head_ = case td.typeVars of
        [] -> tname
        vs -> tname ++ "(" ++ intercalate ", " (map T.unpack vs) ++ ")"
      ctors = intercalate " ; " (map ctorToString td.constructors)
   in ":- chr_type " ++ head_ ++ " ---> " ++ ctors ++ "."

ctorToString :: DataConstructor -> String
ctorToString c =
  let baseName = case c.conName of
        Unqualified n -> n
        Qualified _ n -> n
      pexpr = case c.conArgs of
        [] -> PE.Atom baseName
        args -> PE.Compound baseName (map (noAnn . typeExprToPExpr) args)
   in PE.prettyPExpr prettyOps pexpr
