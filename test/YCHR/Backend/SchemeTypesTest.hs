{-# LANGUAGE OverloadedStrings #-}

-- | @ychr scheme-types@: the generated library and schema text, the
-- export selection, and the collision errors. Loading the output and
-- round trips through CHR are in @test/scheme/test_scheme_types.py@.
module YCHR.Backend.SchemeTypesTest (tests) where

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
      testCase "schema text" $ do
        out <- generate defaultOpts shapesSource
        out.schema @?= T.unlines expectedSchema,
      testCase "--all adds hidden constructors and unexported types" $ do
        out <- generate defaultOpts {allTypes = True} shapesSource
        mapM_
          (assertInfix out.library)
          [ "(rnrs:define (make-rect x1 x2) ",
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
          ( "(ychr:make-compound* (rnrs:quote big__nine) (rnrs:vector x1 "
              <> "x2 x3 x4 x5 x6 x7 x8 x9))"
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
          ( "(rnrs:define (make-point x1 x2) (ychr:make-compound2 "
              <> "(rnrs:quote shapes__point) x1 x2))"
          ),
      testCase "names that are not identifiers" $ do
        out <- generate defaultOpts {moduleName = "odd", allTypes = True} oddSource
        -- Escaped like constraint aliases; the functor keeps its spelling.
        assertInfix
          out.library
          ( "(rnrs:define (make-x__u20__y x1) (ychr:make-compound1 "
              <> "(rnrs:string->symbol \"odd__x y\") x1))"
          )
        assertInfix out.library "(rnrs:define (x__u20__y-a__u2d__b p) "
        assertInfix out.library "(rnrs:define (__u39__lives? v) "
        -- The schema writes such names as strings.
        assertInfix out.schema "(constructor \"x y\" \"odd__x y\" (field a-b int))",
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
      libraryName = defaultLibraryName "shapes",
      allTypes = False,
      checked = False
    }

generate :: SchemeTypesOptions -> Text -> IO SchemeTypesOutput
generate opts src = do
  prog <- compileOrFail [(T.unpack opts.moduleName ++ ".chr", src)]
  case generateSchemeTypes opts {libraryName = defaultLibraryName opts.moduleName} prog of
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
      ":- chr_type t ---> 'x y'('a-b' :: int) ; '9lives'."
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
    ( "  (export make-point point? point-x point-y point-with-x "
        <> "point-with-y point-type? make-circle circle? circle-r "
        <> "circle-with-r empty empty? shape-type? make-tag tag? tag-1 "
        <> "tag-type?)"
    ),
    "  (import (prefix (rnrs) rnrs:) (prefix (ychr var) ychr:))",
    ( "  (rnrs:define (make-point x1 x2) (ychr:make-compound2 "
        <> "(rnrs:quote shapes__point) x1 x2))"
    ),
    ( "  (rnrs:define (point? v) (rnrs:let ((d (ychr:deref v))) "
        <> "(rnrs:and (ychr:compound2? d) (rnrs:eq? "
        <> "(ychr:compound2-functor d) (rnrs:quote shapes__point)))))"
    ),
    ( "  (rnrs:define (point-x p) (ychr:deref (ychr:compound2-a1 "
        <> "(ychr:deref p))))"
    ),
    ( "  (rnrs:define (point-y p) (ychr:deref (ychr:compound2-a2 "
        <> "(ychr:deref p))))"
    ),
    ( "  (rnrs:define (point-with-x p v) (rnrs:let ((d (ychr:deref "
        <> "p))) (ychr:make-compound2 (rnrs:quote shapes__point) v "
        <> "(ychr:compound2-a2 d))))"
    ),
    ( "  (rnrs:define (point-with-y p v) (rnrs:let ((d (ychr:deref "
        <> "p))) (ychr:make-compound2 (rnrs:quote shapes__point) "
        <> "(ychr:compound2-a1 d) v)))"
    ),
    ( "  (rnrs:define (point-type? v) (rnrs:let ((d (ychr:deref v))) "
        <> "(rnrs:and (ychr:compound2? d) (rnrs:eq? "
        <> "(ychr:compound2-functor d) (rnrs:quote shapes__point)))))"
    ),
    ( "  (rnrs:define (make-circle x1) (ychr:make-compound1 "
        <> "(rnrs:quote shapes__circle) x1))"
    ),
    ( "  (rnrs:define (circle? v) (rnrs:let ((d (ychr:deref v))) "
        <> "(rnrs:and (ychr:compound1? d) (rnrs:eq? "
        <> "(ychr:compound1-functor d) (rnrs:quote shapes__circle)))))"
    ),
    ( "  (rnrs:define (circle-r p) (ychr:deref (ychr:compound1-a1 "
        <> "(ychr:deref p))))"
    ),
    ( "  (rnrs:define (circle-with-r p v) (rnrs:let ((d (ychr:deref "
        <> "p))) (ychr:make-compound1 (rnrs:quote shapes__circle) v)))"
    ),
    "  (rnrs:define empty (rnrs:quote shapes__empty))",
    ( "  (rnrs:define (empty? v) (rnrs:let ((d (ychr:deref v))) "
        <> "(rnrs:eq? d (rnrs:quote shapes__empty))))"
    ),
    ( "  (rnrs:define (shape-type? v) (rnrs:let ((d (ychr:deref v))) "
        <> "(rnrs:or (rnrs:and (ychr:compound1? d) (rnrs:eq? "
        <> "(ychr:compound1-functor d) (rnrs:quote shapes__circle))) "
        <> "(rnrs:and (ychr:compound2? d) (rnrs:eq? "
        <> "(ychr:compound2-functor d) (rnrs:quote shapes__rect))) "
        <> "(rnrs:eq? d (rnrs:quote shapes__empty)))))"
    ),
    ( "  (rnrs:define (make-tag x1) (ychr:make-compound1 (rnrs:quote "
        <> "shapes__tag) x1))"
    ),
    ( "  (rnrs:define (tag? v) (rnrs:let ((d (ychr:deref v))) "
        <> "(rnrs:and (ychr:compound1? d) (rnrs:eq? "
        <> "(ychr:compound1-functor d) (rnrs:quote shapes__tag)))))"
    ),
    ( "  (rnrs:define (tag-1 p) (ychr:deref (ychr:compound1-a1 "
        <> "(ychr:deref p))))"
    ),
    ( "  (rnrs:define (tag-type? v) (rnrs:let ((d (ychr:deref v))) "
        <> "(rnrs:and (ychr:compound1? d) (rnrs:eq? "
        <> "(ychr:compound1-functor d) (rnrs:quote shapes__tag)))))"
    ),
    ")"
  ]

expectedSchema :: [Text]
expectedSchema =
  [ "(ychr-schema 1",
    "  (module shapes)",
    "  (library (ychr types shapes))",
    "  (type point (X Y)",
    "    (constructor point shapes__point (field x X) (field y Y)))",
    "  (type shape ()",
    "    (constructor circle shapes__circle (field r float))",
    "    (constructor empty shapes__empty))",
    "  (type tag ()",
    "    (constructor tag shapes__tag (field #f int)))",
    "  (type handle (A) opaque))"
  ]
