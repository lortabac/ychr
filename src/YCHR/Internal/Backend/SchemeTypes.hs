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
--
-- With 'ground' set, nothing is dereferenced: the caller promises that
-- the terms are ground. With 'checked' too, a variable where a ground
-- library reads raises instead.
module YCHR.Internal.Backend.SchemeTypes
  ( SchemeTypesOptions (..),
    SchemeTypesOutput (..),
    SchemeTypesError (..),
    selectModule,
    defaultLibraryName,
    generateSchemeTypes,
  )
where

import Data.List (nub, sortOn)
import Data.List.NonEmpty qualified as NE
import Data.Map.Strict qualified as Map
import Data.Maybe (mapMaybe)
import Data.Text (Text)
import Data.Text qualified as T
import YCHR.Internal.Backend.Scheme
  ( encodeAliasComponent,
    flatMaxArity,
    functorTypeUid,
    isValidSchemeIdentifier,
    staticFunctorType,
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
    -- | Accessors check the constructor and raise on a mismatch. With
    -- 'ground', every procedure also raises on a variable.
    checked :: Bool,
    -- | The ground variant: no @deref@ anywhere.
    ground :: Bool
  }

data SchemeTypesOutput = SchemeTypesOutput
  { -- | The @.sls@ library.
    library :: Text,
    -- | The records library it imports, @(LIBRARY records)@: the
    -- constructors' own record types, defined statically so a Scheme
    -- compiler can inline their predicates and constructors.
    records :: Text,
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

-- | @(ychr types MODULE)@, or @(ychr ground-types MODULE)@ for the
-- ground variant, with the module name made an identifier.
defaultLibraryName :: Bool -> Text -> [Text]
defaultLibraryName g m =
  ["ychr", if g then "ground-types" else "types", encodeAliasComponent m]

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
-- collision messages), and the @define@ form. With 'from', it is not
-- defined here but re-exported from the records library under 'ident'.
data Def = Def
  { ident :: Text,
    origin :: Text,
    form :: SExpr,
    from :: Maybe Text
  }

-- | A definition with a form.
mkDef :: Text -> Text -> SExpr -> Def
mkDef i o f = Def {ident = i, origin = o, form = f, from = Nothing}

-- | A re-export of @src@ from the records library.
reexport :: Text -> Text -> Text -> Def
reexport i o src = Def {ident = i, origin = o, form = SList [], from = Just src}

-- | Constructors with a static record type in the records library,
-- numbered, by functor.
type Statics = Map.Map Text Int

-- | Whether a constructor gets a static record type, and its uid: see
-- 'staticFunctorType'. The others look their type up at load.
hasStatic :: DataConstructor -> Bool
hasStatic c = staticFunctorType (vmName c.conName).unName (length (conArgs c))

staticUid :: DataConstructor -> Text
staticUid c = functorTypeUid (vmName c.conName).unName (length (conArgs c))

staticOf :: Statics -> DataConstructor -> Maybe Int
staticOf st c = Map.lookup (vmName c.conName).unName st

-- | The static constructor and predicate, as named in the main library.
staticCtor, staticPred :: Int -> Text
staticCtor k = "r:%mk" <> T.pack (show k)
staticPred k = "r:%p" <> T.pack (show k)

generateSchemeTypes ::
  SchemeTypesOptions ->
  CompiledProgram ->
  Either [SchemeTypesError] SchemeTypesOutput
generateSchemeTypes opts prog = case collisions of
  [] ->
    Right
      SchemeTypesOutput
        { library = renderLibrary opts defs,
          records = renderRecords opts staticCtors,
          schema = renderSchema opts selected
        }
  errs -> Left errs
  where
    selected = selectTypes opts prog
    statics =
      Map.fromList
        ( zip
            ( nub
                [ (vmName c.conName).unName
                | s <- selected,
                  c <- typeConstructors s.def,
                  hasStatic c
                ]
            )
            [0 ..]
        )
    staticCtors =
      [ (k, c)
      | (k, c) <-
          sortOn fst . Map.elems $
            ( Map.fromListWith
                (\_ old -> old)
                [ ((vmName c.conName).unName, (k, c))
                | s <- selected,
                  c <- typeConstructors s.def,
                  Just k <- [staticOf statics c]
                ]
            )
      ]
    defs = concatMap (typeDefs opts statics) selected
    -- Names in first-definition order, each with every origin.
    grouped =
      Map.fromListWith (flip (++)) [(d.ident, [d.origin]) | d <- defs]
    firstLoc = Map.fromListWith (\_ old -> old) (concatMap identLocs selected)
    identLocs s = [(d.ident, s.def.loc) | d <- typeDefs opts statics s]
    collisions =
      [ TypesNameCollision n os (Map.findWithDefault (SourceLoc "" 0 0) n firstLoc)
      | n <- nub (map (.ident) defs),
        let os = Map.findWithDefault [] n grouped,
        length os > 1
      ]

typeDefs :: SchemeTypesOptions -> Statics -> Selected -> [Def]
typeDefs opts st s =
  concatMap (ctorDefs opts st s.def) s.visible ++ typePredicate opts st s

-- | @T-type?@: true for any constructor of the type, exported or not.
-- None for an opaque type, which has no constructors.
--
-- The @-type@ suffix keeps it apart from every constructor predicate:
-- an encoded constructor name never holds a @-@, so @C?@ can't be
-- @T-type?@, whatever the two are called.
typePredicate :: SchemeTypesOptions -> Statics -> Selected -> [Def]
typePredicate opts st s = case typeConstructors s.def of
  [] -> []
  _ ->
    [ mkDef
        (tIdent <> "-type?")
        ("type predicate of " <> describeType s.def)
        ( defineWith
            (tIdent <> "-type?")
            [ (pn, predicateOf c)
            | (pn, c) <- named,
              length (conArgs c) > 0,
              staticOf st c == Nothing
            ]
            ["v"]
            ( varCheck opts (tIdent <> "-type?") "v" $
                letTerm opts "v" $ \d ->
                  anyOf [ctorTest c (SAtom pn) d | (pn, c) <- named]
            )
        )
    ]
  where
    tIdent = encodeAliasComponent (baseName s.def.name)
    named =
      [ (maybe ("p" <> T.pack (show i)) staticPred (staticOf st c), c)
      | (i, c) <- zip [1 :: Int ..] (typeConstructors s.def)
      ]
    anyOf [t] = t
    anyOf ts = rnrs "or" ts

ctorDefs ::
  SchemeTypesOptions -> Statics -> TypeDefinition -> DataConstructor -> [Def]
ctorDefs opts st td c
  | n == 0 =
      [ mkDef e what (SList [SAtom "rnrs:define", SAtom e, sym f]),
        predicate
      ]
  | otherwise =
      [ case static of
          Just k -> reexport ("make-" <> e) what (staticCtor k)
          Nothing -> mkDef ("make-" <> e) what ctorForm,
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
    static = staticOf st c
    build args = SList (SAtom (maybe ("make-" <> e) staticCtor static) : args)
    predicate = case static of
      -- Ground and unchecked: the record type's own predicate.
      Just k
        | opts.ground && not opts.checked ->
            reexport (e <> "?") ("predicate of " <> what) (staticPred k)
      _ -> mkDef (e <> "?") ("predicate of " <> what) predForm
    ctorForm
      | n <= flatMaxArity =
          rnrs "define" [SAtom ("make-" <> e), constructorOf c]
      | otherwise =
          defineWith
            ("make-" <> e)
            [("k", constructorOf c)]
            params
            (SList [SAtom "k", rnrs "vector" (map SAtom params)])
    predBody p = varCheck opts (e <> "?") "v" (letTerm opts "v" (ctorTest c p))
    predForm
      | n == 0 = define (e <> "?") ["v"] (predBody (SAtom "p"))
      | Just k <- static = define (e <> "?") ["v"] (predBody (SAtom (staticPred k)))
      -- Ground and unchecked: the functor's own predicate, as is.
      | opts.ground && not opts.checked && n <= flatMaxArity =
          rnrs "define" [SAtom (e <> "?"), predicateOf c]
      | otherwise =
          defineWith (e <> "?") [("p", predicateOf c)] ["v"] (predBody (SAtom "p"))
    -- The raw field @i@ (0-based) of a term @d@ that is not a variable.
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
                  ( varCheck opts nm "p" $
                      guarded nm (readField opts nm (field (termOf opts "p") i))
                  ),
              from = Nothing
            }
    update :: Int -> Maybe Text -> [Def]
    update _ Nothing = []
    update i (Just l) =
      let nm = e <> "-with-" <> encodeIdentifier l
          args d = [if j == i then SAtom "v" else field d j | j <- [0 .. n - 1]]
       in [ Def
              { ident = nm,
                origin = "update of label " <> l <> " of " <> what,
                form =
                  define
                    nm
                    ["p", "v"]
                    ( varCheck opts nm "p" $
                        guarded nm (letTerm opts "p" (build . args))
                    ),
                from = Nothing
              }
          ]

-- | The test that a value @d@ that is not a variable is constructor
-- @c@, given @p@, the functor's predicate (unused when @c@ is nullary).
ctorTest :: DataConstructor -> SExpr -> SExpr -> SExpr
ctorTest c p d
  | n == 0 = rnrs "eq?" [d, sym f]
  | n <= flatMaxArity = SList [p, d]
  | otherwise =
      rnrs
        "and"
        [ SList [p, d],
          rnrs
            "="
            [ rnrs "vector-length" [SList [SAtom "ychr:compound*-args", d]],
              SInt (fromIntegral n)
            ]
        ]
  where
    n = length (conArgs c)
    f = (vmName c.conName).unName

-- | The functor's own predicate and constructor, looked up once, when
-- the library loads. A term's functor is its record type, so a
-- constructor test is one type test.
predicateOf, constructorOf :: DataConstructor -> SExpr
predicateOf c = functorProc "ychr:compound-predicate" c
constructorOf c = functorProc "ychr:compound-constructor" c

functorProc :: Text -> DataConstructor -> SExpr
functorProc proc c =
  SList
    [ SAtom proc,
      sym (vmName c.conName).unName,
      SInt (fromIntegral (length (conArgs c)))
    ]

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
      "  " <> printSExpr (SList (SAtom "export" : map exportSpec defs)),
      "  "
        <> printSExpr
          ( SList
              [ SAtom "import",
                SList [SAtom "prefix", SList [SAtom "rnrs"], SAtom "rnrs:"],
                SList [SAtom "prefix", SList [SAtom "ychr", SAtom "var"], SAtom "ychr:"],
                SList [SAtom "prefix", SList (map SAtom (recordsLibraryName opts)), SAtom "r:"]
              ]
          )
    ]
      ++ [("  " <>) (printSExpr d.form) | d <- defs, d.from == Nothing]
      ++ [")"]
  where
    exportSpec d = case d.from of
      Nothing -> SAtom d.ident
      Just src -> SList [SAtom "rename", SList [SAtom src, SAtom d.ident]]

-- | The name of the records library: the library's, plus @records@.
recordsLibraryName :: SchemeTypesOptions -> [Text]
recordsLibraryName opts = opts.libraryName ++ ["records"]

-- | The records library: one sealed child of the arity's parent type
-- per constructor with a static type ('hasStatic'). It imports @(rnrs)@
-- without a prefix: Guile's @define-record-type@ refers to plain
-- @quote@, and Chez wants its clause keywords bound.
renderRecords :: SchemeTypesOptions -> [(Int, DataConstructor)] -> Text
renderRecords opts cs =
  T.unlines $
    [ ";;;; Generated by `ychr scheme-types` from module "
        <> opts.moduleName
        <> ". Do not edit.",
      "(library " <> printSExpr (SList (map SAtom (recordsLibraryName opts))),
      "  "
        <> printSExpr
          ( SList
              ( SAtom "export"
                  : concat [[SAtom (mk k), SAtom (pr k)] | (k, _) <- cs]
              )
          ),
      "  "
        <> printSExpr
          ( SList
              [ SAtom "import",
                SList [SAtom "rnrs"],
                SList (SAtom "only" : SList [SAtom "ychr", SAtom "var"] : map SAtom parents)
              ]
          )
    ]
      ++ map (("  " <>) . printSExpr . recordType) cs
      ++ [")"]
  where
    mk k = "%mk" <> T.pack (show k)
    pr k = "%p" <> T.pack (show k)
    arity c = length (conArgs c)
    parents = nub [parent c | (_, c) <- cs]
    parent c = "compound" <> T.pack (show (arity c))
    recordType (k, c) =
      SList
        [ SAtom "define-record-type",
          SList [SAtom (vmName c.conName).unName, SAtom (mk k), SAtom (pr k)],
          SList [SAtom "parent", SAtom (parent c)],
          SList [SAtom "sealed", SAtom "#t"],
          SList [SAtom "nongenerative", SAtom (staticUid c)]
        ]

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

-- | @(define n (let ((b e) …) (lambda ps body)))@: a procedure over
-- values computed once, at load. Plain 'define' when there are none.
defineWith :: Text -> [(Text, SExpr)] -> [Text] -> SExpr -> SExpr
defineWith n [] ps body = define n ps body
defineWith n bs ps body =
  rnrs
    "define"
    [ SAtom n,
      rnrs
        "let"
        [ SList [SList [SAtom b, e] | (b, e) <- bs],
          rnrs "lambda" [SList (map SAtom ps), body]
        ]
    ]

deref :: SExpr -> SExpr
deref e = SList [SAtom "ychr:deref", e]

-- | @(let ((d (deref v))) body)@, or @body@ over @v@ itself in ground
-- mode.
letTerm :: SchemeTypesOptions -> Text -> (SExpr -> SExpr) -> SExpr
letTerm opts v body
  | opts.ground = body (SAtom v)
  | otherwise =
      rnrs "let" [SList [SList [SAtom "d", deref (SAtom v)]], body (SAtom "d")]

-- | @(deref v)@, or @v@ in ground mode.
termOf :: SchemeTypesOptions -> Text -> SExpr
termOf opts v
  | opts.ground = SAtom v
  | otherwise = deref (SAtom v)

-- | In ground mode with 'checked': @body@, unless the argument @v@ of
-- procedure @nm@ is a variable. Otherwise just @body@.
varCheck :: SchemeTypesOptions -> Text -> Text -> SExpr -> SExpr
varCheck opts nm v body
  | opts.ground && opts.checked = notVar nm (SAtom v) (SAtom v) body
  | otherwise = body

-- | A field an accessor of procedure @nm@ returns. Normally
-- dereferenced. In ground mode returned as is, after a check that it is
-- not a variable when 'checked' is set.
readField :: SchemeTypesOptions -> Text -> SExpr -> SExpr
readField opts nm e
  | not opts.ground = deref e
  | opts.checked =
      rnrs
        "let"
        [ SList [SList [SAtom "x", e]],
          notVar nm (SAtom "x") (SAtom "p") (SAtom "x")
        ]
  | otherwise = e

-- | @body@, unless @v@ is a variable: then an @assertion-violation@ of
-- @nm@ that shows @shown@.
notVar :: Text -> SExpr -> SExpr -> SExpr -> SExpr
notVar nm v shown body =
  rnrs
    "if"
    [ SList [SAtom "ychr:var?", v],
      rnrs
        "assertion-violation"
        [sym nm, SString "variable in a ground term", shown],
      body
    ]

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
