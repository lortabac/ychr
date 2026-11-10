{-# LANGUAGE OverloadedStrings #-}

-- | @ychr scheme-types@: an R6RS library of constructors, predicates and
-- accessors for one module's @:- chr_type@ declarations, plus an
-- optional machine-readable schema. See
-- @docs\/reference\/scheme-types.md@.
--
-- The library needs only @(rnrs)@ and @(ychr var)@, so it loads without
-- the compiled CHR program. Both are imported with a prefix
-- (@rnrs:@, @ychr:@): a generated name such as @list?@ would otherwise
-- redefine an imported binding, which R6RS rejects.
--
-- Each accessor knows its constructor's arity, so it reads the field
-- with the arity-specific record accessor (@compound2-a1@), with no
-- dispatch.
module YCHR.Internal.Backend.SchemeTypes
  ( SchemeTypesOptions (..),
    SchemeTypesOutput (..),
    SchemeTypesError (..),
    selectModule,
    defaultLibraryName,
    generateSchemeTypes,
  )
where

import Data.List (nub)
import Data.List.NonEmpty qualified as NE
import Data.Map.Strict qualified as Map
import Data.Maybe (mapMaybe)
import Data.Text (Text)
import Data.Text qualified as T
import YCHR.Internal.Backend.Scheme
  ( encodeAliasComponent,
    flatMaxArity,
    isValidSchemeIdentifier,
  )
import YCHR.Internal.Collected (CollectedModule (..))
import YCHR.Internal.Compile.Names (encodeIdentifier, vmName)
import YCHR.Internal.Compile.Pipeline (CompiledProgram (..))
import YCHR.Internal.Desugared qualified as D
import YCHR.Internal.Loc (SourceLoc (..))
import YCHR.Internal.SExpr (SExpr (..), printSExpr)
import YCHR.Internal.TypeExports (TypeEntry (..), typeExport)
import YCHR.Internal.Types
  ( ConFields (..),
    DataConstructor (..),
    Name (..),
    TypeDefinition (..),
    TypeExpr (..),
    TypeKind (..),
    conArgs,
    typeConstructors,
  )
import YCHR.Internal.VM.Types qualified as VM

data SchemeTypesOptions = SchemeTypesOptions
  { -- | The module whose types are generated.
    moduleName :: Text,
    -- | The R6RS library name, one segment per element.
    libraryName :: [Text],
    -- | Every declared type, not only the exported ones.
    allTypes :: Bool,
    -- | Accessors check the constructor and raise on a mismatch.
    checked :: Bool
  }

data SchemeTypesOutput = SchemeTypesOutput
  { -- | The @.sls@ library.
    library :: Text,
    -- | The schema s-expression file.
    schema :: Text
  }

data SchemeTypesError
  = -- | Two definitions would get the same Scheme name. Carries the
    -- name, a description of each definition, and the location of the
    -- first type involved.
    TypesNameCollision Text [Text] SourceLoc
  | -- | @-m@ names no loaded module. Carries the name and the modules
    -- that are loaded.
    TypesUnknownModule Text [Text]
  | -- | No @-m@, and the input files declare no module or several.
    -- Carries the modules the files declare.
    TypesModuleNotGiven [Text]
  | -- | @-m prelude@. Its @bool@ and @list@ are native Scheme values
    -- (@#t@, pairs, @'()@), not the records this generator emits.
    TypesPrelude
  deriving (Show, Eq)

-- | The module to generate for: the one @-m@ names, or the only module
-- the input files declare. The prelude is refused.
selectModule ::
  CompiledProgram -> [FilePath] -> Maybe Text -> Either SchemeTypesError Text
selectModule prog files requested = case requested of
  Just "prelude" -> Left TypesPrelude
  Just m
    | m `elem` loaded -> Right m
    | otherwise -> Left (TypesUnknownModule m loaded)
  Nothing -> case fromFiles of
    [m] -> Right m
    ms -> Left (TypesModuleNotGiven ms)
  where
    loaded = map (.name) prog.allModules
    fromFiles = [m.name | m <- prog.allModules, m.nameLoc.file `elem` files]

-- | @(ychr types MODULE)@, with the module name made an identifier.
defaultLibraryName :: Text -> [Text]
defaultLibraryName m = ["ychr", "types", encodeAliasComponent m]

-- ---------------------------------------------------------------------------
-- Selection
-- ---------------------------------------------------------------------------

-- | A type to generate, with the constructors that get definitions.
data Selected = Selected
  { def :: TypeDefinition,
    visible :: [DataConstructor]
  }

selectTypes :: SchemeTypesOptions -> CompiledProgram -> [Selected]
selectTypes opts prog = mapMaybe pick declared
  where
    declared =
      [ td
      | let dp :: D.Program
            dp = prog.desugaredProgram,
        td <- dp.typeDefinitions,
        Qualified m _ <- [td.name],
        m == opts.moduleName
      ]
    pick td
      | opts.allTypes = Just (Selected td (typeConstructors td))
      | otherwise = case typeExport prog td of
          NoTypeEntry -> Nothing
          AllConstructors -> Just (Selected td (typeConstructors td))
          TheseConstructors cs ->
            Just
              (Selected td [c | c <- typeConstructors td, baseName c.conName `elem` cs])

-- ---------------------------------------------------------------------------
-- Definitions
-- ---------------------------------------------------------------------------

-- | One top-level definition: its Scheme name, what it is (for
-- collision messages), and the @define@ form.
data Def = Def
  { ident :: Text,
    origin :: Text,
    form :: SExpr
  }

generateSchemeTypes ::
  SchemeTypesOptions ->
  CompiledProgram ->
  Either [SchemeTypesError] SchemeTypesOutput
generateSchemeTypes opts prog = case collisions of
  [] ->
    Right
      SchemeTypesOutput
        { library = renderLibrary opts defs,
          schema = renderSchema opts selected
        }
  errs -> Left errs
  where
    selected = selectTypes opts prog
    defs = concatMap (typeDefs opts) selected
    -- Names in first-definition order, each with every origin.
    grouped =
      Map.fromListWith (flip (++)) [(d.ident, [d.origin]) | d <- defs]
    firstLoc = Map.fromListWith (\_ old -> old) (concatMap identLocs selected)
    identLocs s = [(d.ident, s.def.loc) | d <- typeDefs opts s]
    collisions =
      [ TypesNameCollision n os (Map.findWithDefault (SourceLoc "" 0 0) n firstLoc)
      | n <- nub (map (.ident) defs),
        let os = Map.findWithDefault [] n grouped,
        length os > 1
      ]

typeDefs :: SchemeTypesOptions -> Selected -> [Def]
typeDefs opts s =
  concatMap (ctorDefs opts s.def) s.visible ++ typePredicate s

-- | @T-type?@: true for any constructor of the type, exported or not.
-- None for an opaque type, which has no constructors.
--
-- The @-type@ suffix keeps it apart from every constructor predicate:
-- an encoded constructor name never holds a @-@, so @C?@ can't be
-- @T-type?@, whatever the two are called.
typePredicate :: Selected -> [Def]
typePredicate s = case typeConstructors s.def of
  [] -> []
  cs ->
    [ Def
        { ident = tIdent <> "-type?",
          origin = "type predicate of " <> describeType s.def,
          form =
            define
              (tIdent <> "-type?")
              ["v"]
              (letDeref "v" (anyOf (map (`ctorTest` SAtom "d") cs)))
        }
    ]
  where
    tIdent = encodeAliasComponent (baseName s.def.name)
    anyOf [t] = t
    anyOf ts = rnrs "or" ts

ctorDefs :: SchemeTypesOptions -> TypeDefinition -> DataConstructor -> [Def]
ctorDefs opts td c
  | n == 0 =
      [ Def
          { ident = e,
            origin = what,
            form = SList [SAtom "rnrs:define", SAtom e, sym f]
          },
        predicate
      ]
  | otherwise =
      [ Def
          { ident = "make-" <> e,
            origin = what,
            form = define ("make-" <> e) params (build (map SAtom params))
          },
        predicate
      ]
        ++ zipWith3 accessor [0 :: Int ..] names labels
        ++ concat (zipWith update [0 :: Int ..] labels)
  where
    e = ctorIdent c
    f = (vmName c.conName).unName
    n = length (conArgs c)
    what = "constructor " <> describeCtor c <> " of type " <> describeType td
    params = ["x" <> T.pack (show i) | i <- [1 .. n]]
    labels = case c.conFields of
      Labelled fs -> map (Just . fst) (NE.toList fs)
      Positional _ -> replicate n Nothing
    names =
      [ maybe (T.pack (show i)) encodeIdentifier l
      | (i, l) <- zip [1 :: Int ..] labels
      ]
    build args
      | n <= flatMaxArity =
          SList (SAtom ("ychr:make-compound" <> T.pack (show n)) : sym f : args)
      | otherwise =
          SList [SAtom "ychr:make-compound*", sym f, rnrs "vector" args]
    predicate =
      Def
        { ident = e <> "?",
          origin = "predicate of " <> what,
          form = define (e <> "?") ["v"] (letDeref "v" (ctorTest c (SAtom "d")))
        }
    -- The raw field @i@ (0-based) of a dereferenced term @d@.
    field d i
      | n <= flatMaxArity =
          SList
            [ SAtom ("ychr:compound" <> T.pack (show n) <> "-a" <> T.pack (show (i + 1))),
              d
            ]
      | otherwise =
          rnrs
            "vector-ref"
            [SList [SAtom "ychr:compound*-args", d], SInt (fromIntegral i)]
    guarded nm body
      | opts.checked =
          rnrs
            "if"
            [ SList [SAtom (e <> "?"), SAtom "p"],
              body,
              rnrs
                "assertion-violation"
                [ sym nm,
                  SString ("not a " <> baseName c.conName),
                  SAtom "p"
                ]
            ]
      | otherwise = body
    accessor i l lab =
      let nm = e <> "-" <> l
       in Def
            { ident = nm,
              origin = case lab of
                Just t -> "label " <> t <> " of " <> what
                Nothing -> "argument " <> l <> " of " <> what,
              form =
                define
                  nm
                  ["p"]
                  (guarded nm (deref (field (deref (SAtom "p")) i)))
            }
    update :: Int -> Maybe Text -> [Def]
    update _ Nothing = []
    update i (Just l) =
      let nm = e <> "-with-" <> encodeIdentifier l
          args = [if j == i then SAtom "v" else field (SAtom "d") j | j <- [0 .. n - 1]]
       in [ Def
              { ident = nm,
                origin = "update of label " <> l <> " of " <> what,
                form =
                  define
                    nm
                    ["p", "v"]
                    (guarded nm (letDeref "p" (build args)))
              }
          ]

-- | The test that a dereferenced value @d@ is constructor @c@.
ctorTest :: DataConstructor -> SExpr -> SExpr
ctorTest c d
  | n == 0 = rnrs "eq?" [d, sym f]
  | n <= flatMaxArity =
      rnrs
        "and"
        [ SList [SAtom ("ychr:compound" <> k <> "?"), d],
          rnrs "eq?" [SList [SAtom ("ychr:compound" <> k <> "-functor"), d], sym f]
        ]
  | otherwise =
      rnrs
        "and"
        [ SList [SAtom "ychr:compound*?", d],
          rnrs "eq?" [SList [SAtom "ychr:compound*-functor", d], sym f],
          rnrs
            "="
            [ rnrs "vector-length" [SList [SAtom "ychr:compound*-args", d]],
              SInt (fromIntegral n)
            ]
        ]
  where
    n = length (conArgs c)
    k = T.pack (show n)
    f = (vmName c.conName).unName

ctorIdent :: DataConstructor -> Text
ctorIdent c = encodeAliasComponent (baseName c.conName)

-- ---------------------------------------------------------------------------
-- Rendering
-- ---------------------------------------------------------------------------

renderLibrary :: SchemeTypesOptions -> [Def] -> Text
renderLibrary opts defs =
  T.unlines $
    [ ";;;; Generated by `ychr scheme-types` from module "
        <> opts.moduleName
        <> ". Do not edit.",
      "(library " <> printSExpr (SList (map SAtom opts.libraryName)),
      "  " <> printSExpr (SList (SAtom "export" : map (SAtom . (.ident)) defs)),
      "  (import (prefix (rnrs) rnrs:) (prefix (ychr var) ychr:))"
    ]
      ++ map (("  " <>) . printSExpr . (.form)) defs
      ++ [")"]

-- | The schema: one s-expression describing the generated types.
renderSchema :: SchemeTypesOptions -> [Selected] -> Text
renderSchema opts selected =
  T.unlines . closeLast $
    [ "(ychr-schema 1",
      "  " <> printSExpr (SList [SAtom "module", schemaName opts.moduleName]),
      "  " <> printSExpr (SList [SAtom "library", SList (map SAtom opts.libraryName)])
    ]
      ++ concatMap typeEntry selected
  where
    closeLast ls = init ls ++ [last ls <> ")"]
    typeEntry s = case s.def.kind of
      Opaque ->
        [ "  "
            <> printSExpr
              ( SList
                  [ SAtom "type",
                    schemaName (baseName s.def.name),
                    params s,
                    SAtom "opaque"
                  ]
              )
        ]
      Algebraic _ ->
        let header =
              "  (type "
                <> printSExpr (schemaName (baseName s.def.name))
                <> " "
                <> printSExpr (params s)
         in case map (("    " <>) . printSExpr . ctorEntry) s.visible of
              [] -> [header <> ")"]
              ctors -> header : init ctors ++ [last ctors <> ")"]
    params s = SList (map schemaName s.def.typeVars)
    ctorEntry c =
      SList
        ( SAtom "constructor"
            : schemaName (baseName c.conName)
            : schemaName ((vmName c.conName).unName)
            : fields c
        )
    fields c = case c.conFields of
      Positional ts -> [SList [SAtom "field", SAtom "#f", typeSExpr t] | t <- ts]
      Labelled fs ->
        [SList [SAtom "field", schemaName l, typeSExpr t] | (l, t) <- NE.toList fs]

-- | A type in YCHR's type syntax as an s-expression. Built-in types and
-- the prelude's are bare; other user types are @mod:name@.
typeSExpr :: TypeExpr -> SExpr
typeSExpr (TypeVar v) = schemaName v
typeSExpr (TypeCon n []) = schemaName (typeName n)
typeSExpr (TypeCon n args) = SList (schemaName (typeName n) : map typeSExpr args)

typeName :: Name -> Text
typeName (Unqualified n) = n
typeName (Qualified "prelude" n) = n
typeName (Qualified m n) = m <> ":" <> n

-- | A name in the schema: a symbol when it is a valid identifier,
-- otherwise a string.
schemaName :: Text -> SExpr
schemaName t
  | isValidSchemeIdentifier t = SAtom t
  | otherwise = SString t

-- ---------------------------------------------------------------------------
-- Scheme helpers
-- ---------------------------------------------------------------------------

rnrs :: Text -> [SExpr] -> SExpr
rnrs f args = SList (SAtom ("rnrs:" <> f) : args)

define :: Text -> [Text] -> SExpr -> SExpr
define n ps body = rnrs "define" [SList (map SAtom (n : ps)), body]

deref :: SExpr -> SExpr
deref e = SList [SAtom "ychr:deref", e]

-- | @(let ((d (deref v))) body)@.
letDeref :: Text -> SExpr -> SExpr
letDeref v body =
  rnrs "let" [SList [SList [SAtom "d", deref (SAtom v)]], body]

-- | A quoted symbol, or @string->symbol@ when it is not a valid
-- identifier.
sym :: Text -> SExpr
sym t
  | isValidSchemeIdentifier t = rnrs "quote" [SAtom t]
  | otherwise = rnrs "string->symbol" [SString t]

baseName :: Name -> Text
baseName (Unqualified n) = n
baseName (Qualified _ n) = n

describeType :: TypeDefinition -> Text
describeType td = baseName td.name <> "/" <> T.pack (show (length td.typeVars))

describeCtor :: DataConstructor -> Text
describeCtor c = baseName c.conName <> "/" <> T.pack (show (length (conArgs c)))
