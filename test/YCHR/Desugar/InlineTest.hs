{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Tests for "YCHR.Internal.Desugar.Inline".
--
-- The golden tests in @test/golden/inline_basic@ and the compilation-
-- negative directories (@test/golden/inline_*@) cover the feature
-- end to end: observable behavior, and every declaration-site error.
-- What they cannot show is the one case where a wrong answer and a
-- right one look the same from outside: duplicating a non-trivial,
-- side-effect-free argument like an arithmetic expression produces
-- the same /result/ whether it is substituted twice or evaluated
-- once and reused, so a bug that duplicated it would pass unnoticed
-- there. This module asserts directly on the rewritten AST instead:
-- a single-use call becomes the host call its body names, and a
-- call whose argument would have to be duplicated keeps calling the
-- function.
module YCHR.Desugar.InlineTest (tests) where

import Data.Text (Text)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertFailure, testCase, (@?=))
import YCHR.Internal.Collect (rewriteImports)
import YCHR.Internal.Desugar (desugarProgram, liftAllLambdas)
import YCHR.Internal.Desugar.Inline (inlineFunctions)
import YCHR.Internal.Desugared qualified as D
import YCHR.Internal.Diagnostic (Diagnostic (..))
import YCHR.Internal.Display (Display (..))
import YCHR.Internal.Parsed (AnnP (..))
import YCHR.Internal.Parser (parseModule)
import YCHR.Internal.Rename (defaultRenameInputs, renameProgram)
import YCHR.Internal.Resolve (resolveProgram)
import YCHR.Internal.Resolved qualified as R
import YCHR.Internal.Types (QualifiedName (..))

-- | Parse, resolve, desugar, lift lambdas (a no-op for these
-- fixtures, which have none) and inline a single-module program.
-- Fails the test with every diagnostic's message on any error, at
-- whichever stage raised it.
inlinedProgram :: Text -> IO D.Program
inlinedProgram src = do
  (m, parseErrs) <- case parseModule "<inline-test>" src of
    Left err -> assertFailure ("parse error: " ++ show err)
    Right ok -> pure ok
  case parseErrs of
    [] -> pure ()
    errs -> assertFailure ("unexpected parse-validation errors: " ++ show errs)
  renamed <- case renameProgram defaultRenameInputs (rewriteImports [m]) of
    Right (mods, []) -> pure mods
    Right (_, warnings) ->
      assertFailure ("unexpected rename warnings: " ++ show (map diagMsg warnings))
    Left errs -> assertFailure ("unexpected rename errors: " ++ show (map diagMsg errs))
  resolved <- case resolveProgram renamed of
    Right p -> pure p
    Left errs -> assertFailure ("unexpected resolve errors: " ++ show (map diagMsg errs))
  desugared <- case desugarProgram resolved of
    Right p -> pure p
    Left errs -> assertFailure ("unexpected desugar errors: " ++ show (map diagMsg errs))
  let (lifted, liftErrs) = liftAllLambdas desugared
  case liftErrs of
    [] -> pure ()
    errs -> assertFailure ("unexpected lambda-lift errors: " ++ show (map diagMsg errs))
  let (inlined, inlineErrs) = inlineFunctions lifted
  case inlineErrs of
    [] -> pure inlined
    errs -> assertFailure ("unexpected inline errors: " ++ show (map diagMsg errs))
  where
    diagMsg :: (Display (Diagnostic e)) => Diagnostic e -> String
    diagMsg = displayMsg

qn :: Text -> QualifiedName
qn = QualifiedName "m"

tests :: TestTree
tests =
  testGroup
    "Desugar.Inline"
    [ testCase "a single-use call is replaced by the body it names" $ do
        prog <-
          inlinedProgram
            "\
            \:- module(m, []).\n\
            \:- function inc/1.\n\
            \:- inline inc/1.\n\
            \inc(X) -> host:'+'(X, 1).\n\
            \:- chr_constraint r/2.\n\
            \r(X, R) <=> R is inc(X).\n"
        case prog.rules of
          [r] ->
            r.body.node
              @?= [D.BodyIs "R" (R.HostExpr "+" [R.VarExpr "X", R.IntExpr 1])]
          rs -> assertFailure ("expected 1 rule, got " ++ show (length rs)),
      testCase "a call whose argument's parameter is used twice keeps calling it" $ do
        prog <-
          inlinedProgram
            "\
            \:- module(m, []).\n\
            \:- function dup/1.\n\
            \:- inline dup/1.\n\
            \dup(X) -> host:'+'(X, X).\n\
            \:- chr_constraint r/3.\n\
            \r(X, Y, R) <=> R is dup(host:'+'(X, Y)).\n"
        case prog.rules of
          [r] ->
            r.body.node
              @?= [ D.BodyIs
                      "R"
                      ( R.CallExpr
                          (qn "dup")
                          [R.HostExpr "+" [R.VarExpr "X", R.VarExpr "Y"]]
                      )
                  ]
          rs -> assertFailure ("expected 1 rule, got " ++ show (length rs)),
      testCase "a chain of inline calls collapses to one level" $ do
        prog <-
          inlinedProgram
            "\
            \:- module(m, []).\n\
            \:- function inc/1.\n\
            \:- function double/1.\n\
            \:- inline inc/1, double/1.\n\
            \inc(X) -> host:'+'(X, 1).\n\
            \double(X) -> host:'*'(X, 2).\n\
            \:- chr_constraint r/2.\n\
            \r(X, R) <=> R is double(inc(X)).\n"
        case prog.rules of
          [r] ->
            r.body.node
              @?= [ D.BodyIs
                      "R"
                      ( R.HostExpr
                          "*"
                          [R.HostExpr "+" [R.VarExpr "X", R.IntExpr 1], R.IntExpr 2]
                      )
                  ]
          rs -> assertFailure ("expected 1 rule, got " ++ show (length rs)),
      testCase "a candidate calling another candidate in its own body is fully expanded" $ do
        -- Unlike the previous test, where the chain is only in the
        -- rule body, 'g's own equation calls the candidate 'f'. This
        -- is what exercises 'finalCandidates's topological order: 'f'
        -- must be finalized before 'g's own body is rewritten with
        -- it, both in the standalone procedure 'g' still compiles to
        -- and at every call site that substitutes 'g'.
        prog <-
          inlinedProgram
            "\
            \:- module(m, []).\n\
            \:- function f/1.\n\
            \:- function g/1.\n\
            \:- inline f/1, g/1.\n\
            \f(X) -> host:'+'(X, 1).\n\
            \g(X) -> host:'*'(f(X), 2).\n\
            \:- chr_constraint r/2.\n\
            \r(X, R) <=> R is g(X).\n"
        let expanded =
              R.HostExpr "*" [R.HostExpr "+" [R.VarExpr "X", R.IntExpr 1], R.IntExpr 2]
        case prog.rules of
          [r] -> r.body.node @?= [D.BodyIs "R" expanded]
          rs -> assertFailure ("expected 1 rule, got " ++ show (length rs))
        case [f | f <- prog.functions, f.name == qn "g"] of
          [g] -> case g.equations of
            [eq] -> eq.node.rhs @?= expanded
            eqs -> assertFailure ("expected 1 equation for g, got " ++ show (length eqs))
          gs -> assertFailure ("expected 1 function named g, got " ++ show (length gs)),
      testCase "the function's own procedure is still emitted" $ do
        prog <-
          inlinedProgram
            "\
            \:- module(m, []).\n\
            \:- function inc/1.\n\
            \:- inline inc/1.\n\
            \inc(X) -> host:'+'(X, 1).\n\
            \:- chr_constraint r/2.\n\
            \r(X, R) <=> R is inc(X).\n"
        map (.name) prog.functions @?= [qn "inc"]
    ]
