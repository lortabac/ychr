{-# LANGUAGE OverloadedStrings #-}

-- | @ychr scheme-types@: the generated library and schema text, the
-- export selection, and the collision errors. Loading the output and
-- round trips through CHR are in @test/scheme/test_scheme_types.py@.
module YCHR.Backend.SchemeTypesTest (tests) where

import Data.List (sortOn)
import Data.Text (Text)
import Data.Text qualified as T
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertBool, assertFailure, testCase, (@?=))
import YCHR.Internal.Backend.SchemeTypes
import YCHR.TestHelpers (compileOrFail)

tests :: TestTree
tests =
  testGroup
    "YCHR.Internal.Backend.SchemeTypes"
    [ testCase "library text: labels, positions, nullary, allowlist" $ do
        out <- generate defaultOpts shapesSource
        out.library @?= T.unlines expectedLibrary,
      testCase "records library text" $ do
        out <- generate defaultOpts shapesSource
        out.records @?= T.unlines expectedRecords,
      testCase "schema text" $ do
        out <- generate defaultOpts shapesSource
        out.schema @?= T.unlines expectedSchema,
      testCase "--all adds hidden constructors and unexported types" $ do
        out <- generate defaultOpts {allTypes = True} shapesSource
        mapM_
          (assertInfix out.library)
          [ "(rename (r:%mk2 make-rect))",
            "(rnrs:define (rect-2 p) ",
            "(rnrs:define hid (rnrs:quote shapes__hid))",
            "(rnrs:define (hidden-type? v) "
          ],
      testCase "--checked accessors test the constructor" $ do
        out <- generate defaultOpts {checked = True} shapesSource
        assertInfix
          out.library
          ( "(rnrs:define (point-x p) (rnrs:if (point? p) (ychr:deref "
              <> "(ychr:compound2-a1 (ychr:deref p))) (rnrs:assertion-violation "
              <> "(rnrs:quote point-x) \"not a point\" p)))"
          ),
      testCase "arity above K uses compound*" $ do
        out <- generate defaultOpts {moduleName = "big", allTypes = True} bigSource
        assertInfix
          out.library
          ( "(rnrs:define make-nine (rnrs:let ((k (ychr:compound-constructor "
              <> "(rnrs:quote big__nine) 9))) (rnrs:lambda (x1 x2 x3 x4 x5 x6 "
              <> "x7 x8 x9) (k (rnrs:vector x1 x2 x3 x4 x5 x6 x7 x8 x9)))))"
          )
        assertInfix
          out.library
          ( "(rnrs:define (nine-9 p) (ychr:deref (rnrs:vector-ref "
              <> "(ychr:compound*-args (ychr:deref p)) 8)))"
          ),
      testCase "a parametric type: the code ignores parameters" $ do
        out <- generate defaultOpts shapesSource
        assertInfix
          out.library
          "(rename (r:%mk0 make-point))",
      testCase "names that are not identifiers" $ do
        out <- generate defaultOpts {moduleName = "odd", allTypes = True} oddSource
        -- Escaped; the functor keeps its spelling.
        assertInfix
          out.library
          ( "(rnrs:define make-x__u20__y (ychr:compound-constructor "
              <> "(rnrs:string->symbol \"odd__x y\") 1))"
          )
        assertInfix out.library "(rnrs:define (x__u20__y-a-b p) "
        assertInfix out.library "(rnrs:define (__u39__lives? v) "
        -- `:`, `/` and non-ASCII are escaped although R6RS allows them.
        assertInfix out.library "(rnrs:define (x__u3a__y-a__u2f__b p) "
        assertInfix out.library "(rnrs:define __ue9__ "
        -- The schema writes such source names as strings, and gives
        -- the escaped names.
        assertInfix
          out.schema
          ( "(constructor \"x y\" \"odd__x y\" (scheme make-x__u20__y "
              <> "x__u20__y?)\n      (field a-b int (scheme x__u20__y-a-b "
              <> "x__u20__y-with-a-b)))"
          )
        assertInfix
          out.schema
          "(constructor \"9lives\" odd__9lives (scheme __u39__lives __u39__lives?))",
      testCase "hyphens stay in names" $ do
        out <- generate defaultOpts {moduleName = "a-b", allTypes = True} hyphenSource
        mapM_
          (assertInfix out.library)
          [ "(library (ychr types a-b)",
            "(rename (r:%mk0 make-vhc-core))",
            "(rnrs:define (vhc-core? v) ",
            "(rnrs:define (vhc-core-eta-tvs p) ",
            "(rnrs:define (vhc-core-with-eta-tvs p v) ",
            "(rnrs:define n-a (rnrs:quote a-b__n-a))",
            "(rnrs:define (vhc-type-type? v) "
          ]
        assertInfix
          out.schema
          ( "    (constructor vhc-core a-b__vhc-core (scheme make-vhc-core vhc-core?)\n"
              <> "      (field eta-tvs int (scheme vhc-core-eta-tvs vhc-core-with-eta-tvs)))"
          ),
      testCase "schema names are the exported names" $
        mapM_
          ( \(o, src) -> do
              out <- generate o src
              schemaNames out `sameSet` exportLine out
          )
          [ (defaultOpts, shapesSource),
            (defaultOpts {allTypes = True}, shapesSource),
            (defaultOpts {ground = True, allTypes = True}, shapesSource),
            (defaultOpts {moduleName = "a-b", allTypes = True}, hyphenSource),
            (defaultOpts {moduleName = "odd", allTypes = True}, oddSource),
            (defaultOpts {moduleName = "big", allTypes = True}, bigSource),
            (defaultOpts {moduleName = "hid"}, hiddenSource),
            (defaultOpts {moduleName = "", allTypes = True}, emptySource)
          ],
      testCase "the empty name" $ do
        out <- generate defaultOpts {moduleName = "", allTypes = True} emptySource
        mapM_
          (assertInfix out.library)
          [ "(library (ychr types __empty__)",
            "(rename (r:%mk0 make-__empty__))",
            "(rnrs:define (__empty__-1 p) ",
            "(rnrs:define (__empty__-type? v) "
          ],
      testCase "all constructors hidden: the type predicate stays" $ do
        out <- generate defaultOpts {moduleName = "hid"} hiddenSource
        assertInfix out.library "(rnrs:define (t-type? v) "
        assertInfix out.schema "  (type t ()\n    (scheme t-type?)))",
      testCase "collision: nullary constructor and an accessor" $
        collides
          "a-b"
          "na"
          ":- module(na, []).\n:- chr_type t ---> 'a-b' ; a(b :: int).\n",
      testCase "collision: constructor T-type and the type predicate" $
        collides
          "t-type?"
          "tt"
          ":- module(tt, []).\n:- chr_type t ---> 't-type'(int).\n",
      testCase "collision: one constructor name in two types" $
        collides
          "c?"
          "dup"
          ":- module(dup, []).\n:- chr_type a ---> c(int).\n:- chr_type b ---> c(int).\n",
      testCase "a type and its constructor may share a name" $ do
        out <-
          generate
            defaultOpts {moduleName = "tq", allTypes = True}
            ":- module(tq, []).\n:- chr_type t ---> t(int) ; u.\n"
        assertInfix out.library "(rnrs:define (t? v) "
        assertInfix out.library "(rnrs:define (t-type? v) ",
      testCase "collision: label and position" $
        collides
          "c-1"
          "lp"
          ( ":- module(lp, []).\n:- chr_type a ---> c('1' :: int).\n:- "
              <> "chr_type b ---> c(int).\n"
          ),
      testCase "--ground: library text" $ do
        out <- generate defaultOpts {ground = True} shapesSource
        out.library @?= T.unlines expectedGroundLibrary,
      testCase "--ground: schema differs only in the library name" $ do
        plain <- generate defaultOpts shapesSource
        ground <- generate defaultOpts {ground = True} shapesSource
        ground.schema
          @?= T.replace
            "(library (ychr types shapes))"
            "(library (ychr ground-types shapes))"
            plain.schema,
      testCase "--ground: compound* reads the vector, no deref" $ do
        out <-
          generate
            defaultOpts {moduleName = "big", allTypes = True, ground = True}
            bigSource
        assertInfix
          out.library
          "(rnrs:define (nine-9 p) (rnrs:vector-ref (ychr:compound*-args p) 8))"
        assertBool "no deref" (not ("deref" `T.isInfixOf` out.library)),
      testCase "--ground --all: no deref" $ do
        out <- generate defaultOpts {ground = True, allTypes = True} shapesSource
        assertInfix out.library "(rnrs:define (rect-2 p) (ychr:compound2-a2 p))"
        assertBool "no deref" (not ("deref" `T.isInfixOf` out.library)),
      testCase "--ground --checked: variables raise" $ do
        out <- generate defaultOpts {ground = True, checked = True} shapesSource
        mapM_
          (assertInfix out.library)
          [ "(rnrs:define (point? v) (rnrs:if (ychr:var? v) "
              <> "(rnrs:assertion-violation (rnrs:quote point?) "
              <> "\"variable in a ground term\" v) (r:%p0 v)))",
            "(rnrs:define (point-x p) (rnrs:if (ychr:var? p) "
              <> "(rnrs:assertion-violation (rnrs:quote point-x) "
              <> "\"variable in a ground term\" p) (rnrs:if (point? p) "
              <> "(rnrs:let ((x (ychr:compound2-a1 p))) (rnrs:if "
              <> "(ychr:var? x) (rnrs:assertion-violation (rnrs:quote "
              <> "point-x) \"variable in a ground term\" p) x)) "
              <> "(rnrs:assertion-violation (rnrs:quote point-x) "
              <> "\"not a point\" p))))",
            "(rnrs:define (point-with-x p v) (rnrs:if (ychr:var? p) "
              <> "(rnrs:assertion-violation (rnrs:quote point-with-x) "
              <> "\"variable in a ground term\" p) (rnrs:if (point? p) "
              <> "(r:%mk0 v "
              <> "(ychr:compound2-a2 p)) (rnrs:assertion-violation "
              <> "(rnrs:quote point-with-x) \"not a point\" p))))",
            "(rnrs:define (shape-type? v) (rnrs:if (ychr:var? v) "
          ]
        assertBool "no deref" (not ("deref" `T.isInfixOf` out.library)),
      testCase "--ground --checked: library text" $ do
        out <-
          generate
            defaultOpts
              { moduleName = "gc",
                allTypes = True,
                checked = True,
                ground = True
              }
            ":- module(gc, []).\n:- chr_type t ---> c(a :: int) ; n.\n"
        out.library @?= T.unlines expectedGroundCheckedLibrary,
      testCase "every variant exports the same names" $
        mapM_
          ( \a -> do
              plain <- generate defaultOpts {allTypes = a} shapesSource
              mapM_
                ( \(c, g) -> do
                    out <-
                      generate
                        defaultOpts {allTypes = a, checked = c, ground = g}
                        shapesSource
                    exportLine out @?= exportLine plain
                )
                [(True, False), (False, True), (True, True)]
          )
          [False, True],
      testCase "default library names" $ do
        defaultLibraryName False "m" @?= ["ychr", "types", "m"]
        defaultLibraryName True "m" @?= ["ychr", "ground-types", "m"]
        defaultLibraryName False "a-b" @?= ["ychr", "types", "a-b"]
        defaultLibraryName False "a/b" @?= ["ychr", "types", "a__u2f__b"],
      testCase "module selection" $ do
        prog <- compileOrFail [("shapes.chr", shapesSource)]
        selectModule prog ["shapes.chr"] Nothing @?= Right "shapes"
        selectModule prog [] Nothing @?= Left (TypesModuleNotGiven [])
        selectModule prog [] (Just "prelude") @?= Left TypesPrelude
        case selectModule prog [] (Just "nope") of
          Left (TypesUnknownModule "nope" _) -> pure ()
          other -> assertFailure ("expected an unknown module, got " ++ show other)
    ]

defaultOpts :: SchemeTypesOptions
defaultOpts =
  SchemeTypesOptions
    { moduleName = "shapes",
      libraryName = defaultLibraryName False "shapes",
      allTypes = False,
      checked = False,
      ground = False
    }

generate :: SchemeTypesOptions -> Text -> IO SchemeTypesOutput
generate opts src = do
  prog <- compileOrFail [(T.unpack opts.moduleName ++ ".chr", src)]
  let lib = defaultLibraryName opts.ground opts.moduleName
  case generateSchemeTypes opts {libraryName = lib} prog of
    Left errs -> assertFailure ("generation failed: " ++ show errs)
    Right out -> pure out

collides :: Text -> Text -> Text -> IO ()
collides name m src = do
  prog <- compileOrFail [(T.unpack m ++ ".chr", src)]
  case generateSchemeTypes defaultOpts {moduleName = m, allTypes = True} prog of
    Left errs ->
      assertBool
        ("expected a collision on " ++ show name ++ ", got " ++ show errs)
        (any isIt errs)
    Right _ -> assertFailure ("expected a collision on " ++ show name)
  where
    isIt (TypesNameCollision n _ _) = n == name
    isIt _ = False

-- | The names a generated library exports, in order. A re-export
-- @(rename (r:%p0 c?))@ counts as @c?@.
exportLine :: SchemeTypesOutput -> [Text]
exportLine out = case filter ("  (export " `T.isPrefixOf`) (T.lines out.library) of
  [l] -> names (T.words (T.dropEnd 1 (T.drop (T.length "  (export ") l)))
  _ -> error "no export line"
  where
    names ("(rename" : _ : n : rest) = T.dropEnd 2 n : names rest
    names (n : rest) = n : names rest
    names [] = []

-- | Every name in a @(scheme …)@ entry of the schema.
schemaNames :: SchemeTypesOutput -> [Text]
schemaNames out = go out.schema
  where
    go t = case T.breakOn "(scheme " t of
      (_, rest)
        | T.null rest -> []
        | otherwise ->
            let (inside, after) = T.breakOn ")" (T.drop (T.length "(scheme ") rest)
             in T.words inside ++ go after

sameSet :: [Text] -> [Text] -> IO ()
sameSet a b = sortOn id a @?= sortOn id b

assertInfix :: Text -> Text -> IO ()
assertInfix hay needle =
  assertBool
    ("expected " ++ show needle ++ " in:\n" ++ T.unpack hay)
    (needle `T.isInfixOf` hay)

shapesSource :: Text
shapesSource =
  T.unlines
    [ ( ":- module(shapes, [type(point/2), type(shape/0, [circle, "
          <> "empty]), type(tag/0), type(handle/1)])."
      ),
      ":- chr_type point(X, Y) ---> point(x :: X, y :: Y).",
      ":- chr_type shape ---> circle(r :: float) ; rect(float, float) ; empty.",
      ":- chr_type tag ---> tag(int).",
      ":- chr_type hidden ---> hid.",
      ":- opaque_type handle(A)."
    ]

oddSource :: Text
oddSource =
  T.unlines
    [ ":- module(odd, []).",
      ":- chr_type t ---> 'x y'('a-b' :: int) ; '9lives'.",
      ":- chr_type u ---> 'x:y'('a/b' :: int) ; 'é'."
    ]

hiddenSource :: Text
hiddenSource =
  T.unlines [":- module(hid, [type(t/0, [])]).", ":- chr_type t ---> c(int) ; n."]

emptySource :: Text
emptySource =
  T.unlines [":- module('', []).", ":- chr_type '' ---> ''(int) ; '-x'."]

hyphenSource :: Text
hyphenSource =
  T.unlines
    [ ":- module('a-b', []).",
      ":- chr_type 'vhc-type' ---> 'vhc-core'('eta-tvs' :: int) ; 'n-a'."
    ]

bigSource :: Text
bigSource =
  T.unlines
    [ ":- module(big, []).",
      ":- chr_type nine ---> nine(int, int, int, int, int, int, int, int, int)."
    ]

expectedLibrary :: [Text]
expectedLibrary =
  [ ( ";;;; Generated by `ychr scheme-types` from module shapes. Do "
        <> "not edit."
    ),
    "(library (ychr types shapes)",
    ( "  (export (rename (r:%mk0 make-point)) point? point-x point-y "
        <> "point-with-x point-with-y point-type? (rename (r:%mk1 "
        <> "make-circle)) circle? circle-r circle-with-r empty empty? "
        <> "shape-type? (rename (r:%mk3 make-tag)) tag? tag-1 tag-type?)"
    ),
    ( "  (import (prefix (rnrs) rnrs:) (prefix (ychr var) ychr:) "
        <> "(prefix (ychr types shapes records) r:))"
    ),
    ( "  (rnrs:define (point? v) (rnrs:let ((d (ychr:deref v))) "
        <> "(r:%p0 d)))"
    ),
    ( "  (rnrs:define (point-x p) (ychr:deref (ychr:compound2-a1 "
        <> "(ychr:deref p))))"
    ),
    ( "  (rnrs:define (point-y p) (ychr:deref (ychr:compound2-a2 "
        <> "(ychr:deref p))))"
    ),
    ( "  (rnrs:define (point-with-x p v) (rnrs:let ((d (ychr:deref "
        <> "p))) (r:%mk0 v (ychr:compound2-a2 d))))"
    ),
    ( "  (rnrs:define (point-with-y p v) (rnrs:let ((d (ychr:deref "
        <> "p))) (r:%mk0 (ychr:compound2-a1 d) v)))"
    ),
    ( "  (rnrs:define (point-type? v) (rnrs:let ((d (ychr:deref v))) "
        <> "(r:%p0 d)))"
    ),
    ( "  (rnrs:define (circle? v) (rnrs:let ((d (ychr:deref v))) "
        <> "(r:%p1 d)))"
    ),
    ( "  (rnrs:define (circle-r p) (ychr:deref (ychr:compound1-a1 "
        <> "(ychr:deref p))))"
    ),
    ( "  (rnrs:define (circle-with-r p v) (rnrs:let ((d (ychr:deref "
        <> "p))) (r:%mk1 v)))"
    ),
    "  (rnrs:define empty (rnrs:quote shapes__empty))",
    ( "  (rnrs:define (empty? v) (rnrs:let ((d (ychr:deref v))) "
        <> "(rnrs:eq? d (rnrs:quote shapes__empty))))"
    ),
    ( "  (rnrs:define (shape-type? v) (rnrs:let ((d (ychr:deref v))) "
        <> "(rnrs:or (r:%p1 d) (r:%p2 d) (rnrs:eq? d (rnrs:quote "
        <> "shapes__empty)))))"
    ),
    ( "  (rnrs:define (tag? v) (rnrs:let ((d (ychr:deref v))) (r:%p3 "
        <> "d)))"
    ),
    ( "  (rnrs:define (tag-1 p) (ychr:deref (ychr:compound1-a1 "
        <> "(ychr:deref p))))"
    ),
    ( "  (rnrs:define (tag-type? v) (rnrs:let ((d (ychr:deref v))) "
        <> "(r:%p3 d)))"
    ),
    ")"
  ]

expectedGroundLibrary :: [Text]
expectedGroundLibrary =
  [ ( ";;;; Generated by `ychr scheme-types` from module shapes. Do "
        <> "not edit."
    ),
    "(library (ychr ground-types shapes)",
    ( "  (export (rename (r:%mk0 make-point)) (rename (r:%p0 point?)) "
        <> "point-x point-y point-with-x point-with-y point-type? "
        <> "(rename (r:%mk1 make-circle)) (rename (r:%p1 circle?)) "
        <> "circle-r circle-with-r empty empty? shape-type? (rename "
        <> "(r:%mk3 make-tag)) (rename (r:%p3 tag?)) tag-1 tag-type?)"
    ),
    ( "  (import (prefix (rnrs) rnrs:) (prefix (ychr var) ychr:) "
        <> "(prefix (ychr ground-types shapes records) r:))"
    ),
    "  (rnrs:define (point-x p) (ychr:compound2-a1 p))",
    "  (rnrs:define (point-y p) (ychr:compound2-a2 p))",
    ( "  (rnrs:define (point-with-x p v) (r:%mk0 v (ychr:compound2-a2 "
        <> "p)))"
    ),
    ( "  (rnrs:define (point-with-y p v) (r:%mk0 (ychr:compound2-a1 "
        <> "p) v))"
    ),
    "  (rnrs:define (point-type? v) (r:%p0 v))",
    "  (rnrs:define (circle-r p) (ychr:compound1-a1 p))",
    "  (rnrs:define (circle-with-r p v) (r:%mk1 v))",
    "  (rnrs:define empty (rnrs:quote shapes__empty))",
    ( "  (rnrs:define (empty? v) (rnrs:eq? v (rnrs:quote "
        <> "shapes__empty)))"
    ),
    ( "  (rnrs:define (shape-type? v) (rnrs:or (r:%p1 v) (r:%p2 v) "
        <> "(rnrs:eq? v (rnrs:quote shapes__empty))))"
    ),
    "  (rnrs:define (tag-1 p) (ychr:compound1-a1 p))",
    "  (rnrs:define (tag-type? v) (r:%p3 v))",
    ")"
  ]

expectedGroundCheckedLibrary :: [Text]
expectedGroundCheckedLibrary =
  [ ( ";;;; Generated by `ychr scheme-types` from module gc. Do not "
        <> "edit."
    ),
    "(library (ychr ground-types gc)",
    ( "  (export (rename (r:%mk0 make-c)) c? c-a c-with-a n n? "
        <> "t-type?)"
    ),
    ( "  (import (prefix (rnrs) rnrs:) (prefix (ychr var) ychr:) "
        <> "(prefix (ychr ground-types gc records) r:))"
    ),
    ( "  (rnrs:define (c? v) (rnrs:if (ychr:var? v) "
        <> "(rnrs:assertion-violation (rnrs:quote c?) \"variable in a "
        <> "ground term\" v) (r:%p0 v)))"
    ),
    ( "  (rnrs:define (c-a p) (rnrs:if (ychr:var? p) "
        <> "(rnrs:assertion-violation (rnrs:quote c-a) \"variable in a "
        <> "ground term\" p) (rnrs:if (c? p) (rnrs:let ((x "
        <> "(ychr:compound1-a1 p))) (rnrs:if (ychr:var? x) "
        <> "(rnrs:assertion-violation (rnrs:quote c-a) \"variable in a "
        <> "ground term\" p) x)) (rnrs:assertion-violation (rnrs:quote "
        <> "c-a) \"not a c\" p))))"
    ),
    ( "  (rnrs:define (c-with-a p v) (rnrs:if (ychr:var? p) "
        <> "(rnrs:assertion-violation (rnrs:quote c-with-a) \"variable in "
        <> "a ground term\" p) (rnrs:if (c? p) (r:%mk0 v) "
        <> "(rnrs:assertion-violation (rnrs:quote c-with-a) \"not a c\" "
        <> "p))))"
    ),
    "  (rnrs:define n (rnrs:quote gc__n))",
    ( "  (rnrs:define (n? v) (rnrs:if (ychr:var? v) "
        <> "(rnrs:assertion-violation (rnrs:quote n?) \"variable in a "
        <> "ground term\" v) (rnrs:eq? v (rnrs:quote gc__n))))"
    ),
    ( "  (rnrs:define (t-type? v) (rnrs:if (ychr:var? v) "
        <> "(rnrs:assertion-violation (rnrs:quote t-type?) \"variable in "
        <> "a ground term\" v) (rnrs:or (r:%p0 v) (rnrs:eq? v (rnrs:quote "
        <> "gc__n)))))"
    ),
    ")"
  ]

expectedRecords :: [Text]
expectedRecords =
  [ ( ";;;; Generated by `ychr scheme-types` from module shapes. Do "
        <> "not edit."
    ),
    "(library (ychr types shapes records)",
    "  (export %mk0 %p0 %mk1 %p1 %mk2 %p2 %mk3 %p3)",
    "  (import (rnrs) (only (ychr var) compound2 compound1))",
    ( "  (define-record-type (shapes__point %mk0 %p0) (parent "
        <> "compound2) (sealed #t) (nongenerative "
        <> "ychr:c2:shapes__point:1))"
    ),
    ( "  (define-record-type (shapes__circle %mk1 %p1) (parent "
        <> "compound1) (sealed #t) (nongenerative "
        <> "ychr:c1:shapes__circle:1))"
    ),
    ( "  (define-record-type (shapes__rect %mk2 %p2) (parent "
        <> "compound2) (sealed #t) (nongenerative "
        <> "ychr:c2:shapes__rect:1))"
    ),
    ( "  (define-record-type (shapes__tag %mk3 %p3) (parent "
        <> "compound1) (sealed #t) (nongenerative "
        <> "ychr:c1:shapes__tag:1))"
    ),
    ")"
  ]

expectedSchema :: [Text]
expectedSchema =
  [ "(ychr-schema 2",
    "  (module shapes)",
    "  (library (ychr types shapes))",
    "  (type point (X Y)",
    "    (scheme point-type?)",
    "    (constructor point shapes__point (scheme make-point point?)",
    "      (field x X (scheme point-x point-with-x))",
    "      (field y Y (scheme point-y point-with-y))))",
    "  (type shape ()",
    "    (scheme shape-type?)",
    "    (constructor circle shapes__circle (scheme make-circle circle?)",
    "      (field r float (scheme circle-r circle-with-r)))",
    "    (constructor empty shapes__empty (scheme empty empty?)))",
    "  (type tag ()",
    "    (scheme tag-type?)",
    "    (constructor tag shapes__tag (scheme make-tag tag?)",
    "      (field #f int (scheme tag-1))))",
    "  (type handle (A) opaque))"
  ]
