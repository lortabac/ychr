{-# LANGUAGE OverloadedStrings #-}

module YCHR.PrettyTest (tests) where

import Data.Map.Strict qualified as Map
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, (@?=))
import YCHR.Internal.Desugared qualified as D
import YCHR.Internal.Loc (dummyLoc)
import YCHR.Internal.Pretty
  ( DeclKind (DKFunction),
    prettyBindings,
    prettyConstraintDecl,
    prettyFunctionDecl,
    prettyQueryResult,
    prettyTerm,
    renderAtom,
  )
import YCHR.Internal.Types
  ( BoundSig (..),
    FunSignature (..),
    Name (..),
    QualifiedName (..),
    Term (..),
    TypeExpr (..),
  )

-- | Pretty-printer tests: term rendering, quoting, lists, closures, and binding maps.
tests :: TestTree
tests =
  testGroup
    "YCHR.Internal.Pretty"
    [ basicTests,
      renderAtomTests,
      listRenderingTests,
      closureUnwrapTests,
      bindingsTests,
      requiringBoundQualificationTests
    ]

basicTests :: TestTree
basicTests =
  testGroup
    "prettyTerm basics"
    [ testCase "IntTerm" $
        prettyTerm (IntTerm 42) @?= "42",
      testCase "AtomTerm" $
        prettyTerm (CompoundTerm (Unqualified "foo") []) @?= "foo",
      testCase "VarTerm renders its name" $
        prettyTerm (VarTerm "X") @?= "X",
      testCase "Wildcard" $
        prettyTerm Wildcard @?= "_",
      testCase "CompoundTerm unqualified" $
        prettyTerm
          ( CompoundTerm
              (Unqualified "f")
              [IntTerm 1, CompoundTerm (Unqualified "a") []]
          )
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
        prettyTerm (TextTerm "a\"b\\c\n") @?= "\"a\\\"b\\\\c\\n\"",
      testCase "disequality prints infix from the fixed printer table" $
        prettyTerm
          ( CompoundTerm
              (Unqualified "\\==")
              [VarTerm "X", VarTerm "Y"]
          )
          @?= "X \\== Y",
      testCase "quoted disequality functor keeps its backslash" $
        -- The pretty-printed form has to be readable again: `'\=='`
        -- decodes to `==`, so the printer must not produce that spelling
        -- for this functor.
        prettyTerm (CompoundTerm (Unqualified "\\==") [VarTerm "X"])
          @?= "'\\\\=='(X)"
    ]

renderAtomTests :: TestTree
renderAtomTests =
  testGroup
    "renderAtom quoting"
    [ testCase "lowercase with digits and underscore stays bare" $
        renderAtom "foo_bar2" @?= "foo_bar2",
      testCase "leading underscore is quoted" $
        renderAtom "_foo" @?= "'_foo'",
      testCase "atom with embedded space is quoted" $
        renderAtom "hello world" @?= "'hello world'",
      testCase "word operator 'is' is quoted (would otherwise parse as op)" $
        renderAtom "is" @?= "'is'"
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
        prettyTerm (cons (IntTerm 1) (CompoundTerm (Unqualified "foo") []))
          @?= "[1 | foo]"
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
                [ CompoundTerm (Unqualified "fun") [CompoundTerm (Unqualified "X") []],
                  CompoundTerm
                    (Unqualified "+")
                    [CompoundTerm (Unqualified "X") [], IntTerm 1]
                ]
            closure =
              CompoundTerm
                (Unqualified "__closure")
                [CompoundTerm (Unqualified "__lambda_0") [], source]
         in prettyTerm closure @?= "fun(X) -> X + 1 end",
      -- 'unquoteToPExpr' turns atoms whose name looks like a variable
      -- (uppercase-first or leading underscore) back into variables —
      -- that's how a captured variable reference inside a closure body
      -- gets rendered as a variable rather than a quoted atom.
      testCase "closure body atoms that look like vars render as vars" $
        let source =
              CompoundTerm
                (Unqualified "->")
                [ CompoundTerm (Unqualified "fun") [CompoundTerm (Unqualified "X") []],
                  CompoundTerm (Unqualified "X") []
                ]
            closure =
              CompoundTerm
                (Unqualified "__closure")
                [CompoundTerm (Unqualified "__lambda_1") [], source]
         in prettyTerm closure @?= "fun(X) -> X end"
    ]

bindingsTests :: TestTree
bindingsTests =
  testGroup
    "binding-map formatting"
    [ testCase "prettyBindings sorted with trailing newline" $
        prettyBindings (Map.fromList [("R", IntTerm 55), ("X", Wildcard)])
          @?= "R = 55\nX = _\n",
      -- Same filter as prettyQueryResult.
      testCase "prettyBindings filters underscored names" $
        prettyBindings
          ( Map.fromList
              [ ("R", IntTerm 1),
                ("_hidden", CompoundTerm (Unqualified "x") [])
              ]
          )
          @?= "R = 1\n",
      testCase "prettyBindings all-underscore map is empty string" $
        prettyBindings (Map.fromList [("_X", IntTerm 1), ("_Y", Wildcard)])
          @?= "",
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
                ("Y", CompoundTerm (Unqualified "ok") []),
                ("Z", Wildcard)
              ]
          )
          @?= "X = 1,\nY = ok,\nZ = _.\n",
      testCase "prettyQueryResult filters underscored names from a mixed map" $
        prettyQueryResult
          ( Map.fromList
              [ ("R", IntTerm 42),
                ("_internal", CompoundTerm (Unqualified "hidden") [])
              ]
          )
          @?= "R = 42.\n"
    ]

-- | A `requiring` bound prints qualified only when its module differs
-- from the declaring one.
requiringBoundQualificationTests :: TestTree
requiringBoundQualificationTests =
  testGroup
    "requiring clause qualifies a bound only when its module differs"
    [ testCase "bound declared in the same module prints bare" $
        prettyConstraintDecl
          (QualifiedName "main" "leq")
          2
          (Just [tvar, tvar])
          [bound "main" "lt"]
          @?= ":- chr_constraint leq(T, T) requiring lt(T, T) -> bool.",
      testCase "bound from a library prints module-qualified" $
        prettyConstraintDecl
          (QualifiedName "main" "leq")
          2
          (Just [tvar, tvar])
          [bound "lib" "gt"]
          @?= ":- chr_constraint leq(T, T) requiring lib:gt(T, T) -> bool.",
      testCase "bound naming a prelude operator quotes the operator" $
        prettyConstraintDecl
          (QualifiedName "main" "leq")
          2
          (Just [tvar, tvar])
          [bound "prelude" ">="]
          @?= ":- chr_constraint leq(T, T) requiring prelude:'>='(T, T) -> bool.",
      testCase "bound from a module name that needs quoting" $
        prettyConstraintDecl
          (QualifiedName "main" "leq")
          2
          (Just [tvar, tvar])
          [bound "my lib" "gt"]
          @?= ":- chr_constraint leq(T, T) requiring 'my lib':gt(T, T) -> bool.",
      -- ':info max' itself must stay unchanged: a function requiring a
      -- bound declared in its own module prints that bound bare.
      testCase "requiring on a function declaration: own-module bound stays bare" $
        prettyFunctionDecl
          D.Function
            { D.name = QualifiedName "prelude" "max",
              D.arity = 2,
              D.signatures = [FunSignature [tvar, tvar] tvar],
              D.requiring = [bound "prelude" "gt"],
              D.refining = Nothing,
              D.lambdaArity = Nothing,
              D.inline = False,
              D.equations = []
            }
          DKFunction
          @?= ":- function max(T, T) -> T requiring gt(T, T) -> bool.",
      -- `,` binds tighter than `->`, so bare bounds don't reparse.
      testCase "two or more bounds are each wrapped in parens" $
        prettyConstraintDecl
          (QualifiedName "main" "leq")
          2
          (Just [tvar, tvar])
          [bound "main" "lt", bound "main" "gt"]
          @?= ":- chr_constraint leq(T, T) requiring (lt(T, T) -> bool), (gt(T, T) -> bool)."
    ]
  where
    tvar = TypeVar "T"
    boolTy = TypeCon (Unqualified "bool") []
    bound m n =
      BoundSig
        { name = Qualified m n,
          arity = 2,
          argTypes = [tvar, tvar],
          returnType = boolTy,
          loc = dummyLoc
        }
