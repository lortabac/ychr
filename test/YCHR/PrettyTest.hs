{-# LANGUAGE OverloadedStrings #-}

module YCHR.PrettyTest (tests) where

import Data.Map.Strict qualified as Map
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, (@?=))
import YCHR.Pretty (prettyBindings, prettyQueryResult, prettyTerm, renderAtom)
import YCHR.Types (Name (..), Term (..))

tests :: TestTree
tests =
  testGroup
    "YCHR.Pretty"
    [ basicTests,
      renderAtomTests,
      listRenderingTests,
      closureUnwrapTests,
      bindingsTests
    ]

basicTests :: TestTree
basicTests =
  testGroup
    "prettyTerm basics"
    [ testCase "IntTerm" $
        prettyTerm (IntTerm 42) @?= "42",
      testCase "AtomTerm" $
        prettyTerm (AtomTerm "foo") @?= "foo",
      testCase "VarTerm renders its name" $
        prettyTerm (VarTerm "X") @?= "X",
      testCase "Wildcard" $
        prettyTerm Wildcard @?= "_",
      testCase "CompoundTerm unqualified" $
        prettyTerm (CompoundTerm (Unqualified "f") [IntTerm 1, AtomTerm "a"])
          @?= "f(1, a)",
      testCase "CompoundTerm qualified" $
        prettyTerm (CompoundTerm (Qualified "m" "f") [IntTerm 1])
          @?= "m:f(1)",
      testCase "nested compound" $
        prettyTerm
          ( CompoundTerm
              (Unqualified "f")
              [CompoundTerm (Unqualified "g") [IntTerm 0]]
          )
          @?= "f(g(0))",
      -- Negative integers render with parentheses so e.g. binding output
      -- like @R = (-2)@ parses back as a single term rather than a
      -- subtraction expression. (Verified by an existing golden test,
      -- but pinned here at the unit level too.)
      testCase "negative integer is parenthesized" $
        prettyTerm (IntTerm (-2)) @?= "(-2)",
      testCase "negative float is parenthesized" $
        prettyTerm (FloatTerm (-1.5)) @?= "(-1.5)",
      testCase "TextTerm renders with surrounding quotes" $
        prettyTerm (TextTerm "hello") @?= "\"hello\"",
      testCase "TextTerm escapes embedded quotes/backslashes/newlines" $
        prettyTerm (TextTerm "a\"b\\c\n") @?= "\"a\\\"b\\\\c\\n\""
    ]

renderAtomTests :: TestTree
renderAtomTests =
  testGroup
    "renderAtom quoting"
    [ testCase "lowercase identifier stays bare" $
        renderAtom "foo" @?= "foo",
      testCase "lowercase with digits and underscore stays bare" $
        renderAtom "foo_bar2" @?= "foo_bar2",
      testCase "empty atom is quoted" $
        renderAtom "" @?= "''",
      testCase "uppercase-first is quoted" $
        renderAtom "Foo" @?= "'Foo'",
      testCase "leading underscore is quoted" $
        renderAtom "_foo" @?= "'_foo'",
      testCase "atom with embedded space is quoted" $
        renderAtom "hello world" @?= "'hello world'",
      testCase "atom with apostrophe is quoted, apostrophe doubled" $
        renderAtom "hello's" @?= "'hello''s'",
      testCase "word operator 'is' is quoted (would otherwise parse as op)" $
        renderAtom "is" @?= "'is'",
      -- The flattened-qualified marker '__' triggers quoting so that
      -- internal names like @prelude__.@ don't accidentally render as
      -- bare atoms that the parser would re-tokenize.
      testCase "atom containing '__' is quoted" $
        renderAtom "foo__bar" @?= "'foo__bar'"
    ]

listRenderingTests :: TestTree
listRenderingTests =
  testGroup
    "list canonicalization"
    [ testCase "canonical nil renders as []" $
        prettyTerm (CompoundTerm (Unqualified "prelude__[]") []) @?= "[]",
      testCase "single-element list" $
        prettyTerm (cons (IntTerm 1) nil) @?= "[1]",
      testCase "proper multi-element list" $
        prettyTerm (cons (IntTerm 1) (cons (IntTerm 2) (cons (IntTerm 3) nil)))
          @?= "[1, 2, 3]",
      testCase "nested lists" $
        prettyTerm
          ( cons
              (IntTerm 1)
              ( cons
                  (cons (IntTerm 2) (cons (IntTerm 3) nil))
                  nil
              )
          )
          @?= "[1, [2, 3]]",
      testCase "improper list with variable tail" $
        prettyTerm (cons (IntTerm 1) (VarTerm "T")) @?= "[1 | T]",
      testCase "improper list with atom tail" $
        prettyTerm (cons (IntTerm 1) (AtomTerm "foo")) @?= "[1 | foo]"
    ]
  where
    nil = CompoundTerm (Unqualified "prelude__[]") []
    cons h t = CompoundTerm (Unqualified "prelude__.") [h, t]

closureUnwrapTests :: TestTree
closureUnwrapTests =
  testGroup
    "closure unwrapping"
    [ -- A closure value is a compound @__closure(name, sourceForm, ...captures)@.
      -- prettyTerm should show the user-visible source form, not the
      -- internal closure functor.
      testCase "closure renders its source form" $
        let source =
              CompoundTerm
                (Unqualified "->")
                [ CompoundTerm (Unqualified "fun") [AtomTerm "X"],
                  CompoundTerm (Unqualified "+") [AtomTerm "X", IntTerm 1]
                ]
            closure =
              CompoundTerm
                (Unqualified "__closure")
                [AtomTerm "__lambda_0", source]
         in prettyTerm closure @?= "fun(X) -> X + 1 end",
      -- 'unquoteToPExpr' turns atoms whose name looks like a variable
      -- (uppercase-first or leading underscore) back into variables —
      -- that's how a captured variable reference inside a closure body
      -- gets rendered as a variable rather than a quoted atom.
      testCase "closure body atoms that look like vars render as vars" $
        let source =
              CompoundTerm
                (Unqualified "->")
                [ CompoundTerm (Unqualified "fun") [AtomTerm "X"],
                  AtomTerm "X"
                ]
            closure =
              CompoundTerm
                (Unqualified "__closure")
                [AtomTerm "__lambda_1", source]
         in prettyTerm closure @?= "fun(X) -> X end"
    ]

bindingsTests :: TestTree
bindingsTests =
  testGroup
    "binding-map formatting"
    [ testCase "prettyBindings sorted with trailing newline" $
        prettyBindings (Map.fromList [("R", IntTerm 55), ("X", Wildcard)])
          @?= "R = 55\nX = _\n",
      testCase "prettyBindings empty" $
        prettyBindings Map.empty @?= "",
      testCase "prettyQueryResult empty map is empty string" $
        prettyQueryResult Map.empty @?= "",
      -- Underscored names are internal/wildcard; filtering them out
      -- can leave the visible set empty even when the raw map is not.
      testCase "prettyQueryResult all-underscore map is empty string" $
        prettyQueryResult (Map.fromList [("_X", IntTerm 1), ("_Y", Wildcard)])
          @?= "",
      testCase "prettyQueryResult single binding ends with dot+newline" $
        prettyQueryResult (Map.fromList [("R", IntTerm 7)])
          @?= "R = 7.\n",
      testCase "prettyQueryResult multi-binding uses comma between, dot at end" $
        prettyQueryResult
          ( Map.fromList
              [ ("X", IntTerm 1),
                ("Y", AtomTerm "ok"),
                ("Z", Wildcard)
              ]
          )
          @?= "X = 1,\nY = ok,\nZ = _.\n",
      testCase "prettyQueryResult filters underscored names from a mixed map" $
        prettyQueryResult
          ( Map.fromList
              [ ("R", IntTerm 42),
                ("_internal", AtomTerm "hidden")
              ]
          )
          @?= "R = 42.\n"
    ]
