{-# LANGUAGE OverloadedStrings #-}

-- | Unit tests for the parts of the type checker's diagnostic
-- behaviour that no other harness can observe. The golden harness
-- asserts a warning's presence or absence, and @ychr check@ exits on
-- errors before printing warnings — neither can show that a warning
-- was /dropped because its own unit erred/, which is what
-- 'TypeCheckResult' exposes directly.
module YCHR.TypeCheckTest (tests) where

import Data.Text (Text)
import Data.Text qualified as T
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertFailure, testCase, (@?=))
import YCHR.Internal.Compile.Pipeline (CompiledProgram (..), Error, compileModules)
import YCHR.Internal.Diagnostic (Diagnostic (..))
import YCHR.Internal.Parsed (AnnP (..))
import YCHR.Internal.TypeCheck (typeCheckProgram)
import YCHR.Internal.TypeCheck.Error
  ( TypeCheckResult (..),
    TypeCheckWarning (..),
  )

-- | Compile a single-module program and type-check it, returning the
-- error payloads' rendered shapes and the warning payloads.
checkModule :: Text -> IO ([String], [TypeCheckWarning])
checkModule src =
  case compileModules False [("test.chr", src)] of
    Left err -> assertFailure ("unexpected compile error: " ++ show (err :: Error))
    Right (prog, _) -> do
      result <- typeCheckProgram prog.desugaredProgram
      pure
        ( [show payload | Diagnostic _ (AnnP payload _ _) <- result.errors],
          [payload | Diagnostic _ (AnnP payload _ _) <- result.warnings]
        )

-- | A module with a @color@ type and a @tag@ constraint whose first
-- argument is @color@-typed, plus whatever rules the caller supplies.
mod_ :: [Text] -> Text
mod_ rules =
  T.unlines
    ( [ ":- module(m, []).",
        ":- use_module(library(prelude)).",
        ":- chr_type color ---> red ; green ; blue.",
        ":- chr_constraint tag(color, int), other(color, int)."
      ]
        ++ rules
    )

tests :: TestTree
tests =
  testGroup
    "TypeCheck"
    [ testCase "contradicting evidence in a clean rule warns" $ do
        (errs, ws) <- checkModule (mod_ ["dead @ tag(X, R) <=> integer(X) | R = 1."])
        errs @?= []
        ws @?= [InaccessibleBranch "int" "m:color"],
      testCase "a match against a foreign constructor warns" $ do
        -- The other emitter: constructor membership fails, so the
        -- head pattern can never match a `color`-typed value. The
        -- goldens only assert that this is no longer an error, so the
        -- payload is pinned here.
        (errs, ws) <- checkModule (mod_ ["dead @ tag([_|_], R) <=> R = 1."])
        errs @?= []
        ws @?= [InaccessibleBranch "prelude:list(_)" "m:color"],
      testCase "a variable shared between incompatible head positions warns" $ do
        -- HNF splits the shared X into two variables joined by a
        -- `GuardEqual`, whose fact is that the two positions have the
        -- same type. They never do, so the rule can never fire.
        (errs, ws) <- checkModule (mod_ ["dead @ tag(X, _), other(_, X) <=> true."])
        errs @?= []
        ws @?= [InaccessibleBranch "m:color" "int"],
      testCase "a literal parameter of the wrong type warns" $ do
        -- Same form, from an equation: HNF turns the literal pattern
        -- into a `GuardEqual` against the declared parameter type.
        (errs, ws) <-
          checkModule
            ( mod_
                [ ":- function f(int) -> int.",
                  "f(\"oops\") -> 1.",
                  "f(_) -> 0."
                ]
            )
        errs @?= []
        ws @?= [InaccessibleBranch "int" "string"],
      testCase "evidence that would build a cyclic type warns" $ do
        -- The occurs check: `f(X, X)` asserts T = list(T) at the
        -- equation's skolem. No type satisfies it, so the equation is
        -- dead — and the fact must bind nothing, or the cell would
        -- hold a cyclic term and hang every later deref.
        (errs, ws) <-
          checkModule
            ( mod_
                [ ":- function f(T, prelude:list(T)) -> int.",
                  "f(X, X) -> 1."
                ]
            )
        errs @?= []
        ws @?= [InaccessibleBranch "T#0" "prelude:list(T#0)"],
      testCase "evidence that would close a cycle across two skolems warns" $ do
        -- The occurs check has to look through an already-pinned
        -- cell: here the first equality pins one head's T to the
        -- other's, and only then does the second close the loop
        -- through `list`. Before the check, this hung the checker.
        (errs, ws) <-
          checkModule
            ( mod_
                [ ":- chr_constraint a(T, T), b(T, prelude:list(T)).",
                  "dead @ a(X, Y), b(X, Y) <=> true."
                ]
            )
        errs @?= []
        ws @?= [InaccessibleBranch "T#1" "prelude:list(T#1)"],
      testCase "a second predicate on a pinned skolem meets the pin" $ do
        -- Once evidence pins the skolem, it is no longer opaque: a
        -- second, contradicting predicate on the same variable meets
        -- the pinned type and reports the branch dead, rather than
        -- silently re-pinning to whatever came last.
        (errs, ws) <-
          checkModule
            ( mod_
                [ ":- function f(T) -> int.",
                  "f(X) | integer(X), string(X) -> 0.",
                  "f(_) -> 1."
                ]
            )
        errs @?= []
        ws @?= [InaccessibleBranch "string" "int"],
      testCase "a type that contains itself binds nothing and is accepted" $ do
        -- The occurs check on `tc_unify`'s binding rules. `W = bx(W)`
        -- would bind W's flexible slot to a type containing itself;
        -- the resulting cyclic term hangs the next deref that walks
        -- it — including the runtime's observer transfer, which is
        -- why this hung the compiler outright. The slot is flexible,
        -- so the accepting disposition is to drop the fact: no error,
        -- no warning, and no cycle.
        (errs, ws) <-
          checkModule
            ( mod_
                [ ":- chr_type box(A) ---> bx(A).",
                  ":- chr_constraint p(any).",
                  "r @ p(bx(W)) <=> W = bx(W)."
                ]
            )
        errs @?= []
        ws @?= [],
      testCase "an error in the same rule suppresses its warning" $ do
        -- `R = X` writes a color into an int-typed argument. The rule
        -- is both dead and wrong; the error is what gets reported
        -- (spec §Inaccessible branches: a warning never suppresses an
        -- error, and a dead unit that also errs omits the warning).
        (errs, ws) <- checkModule (mod_ ["dead @ tag(X, R) <=> integer(X) | R = X."])
        length errs @?= 1
        ws @?= [],
      testCase "suppression is per unit, not per program" $ do
        -- One rule errs, a different one is merely dead: the second
        -- rule's warning survives the first rule's error.
        (errs, ws) <-
          checkModule
            ( mod_
                [ "bad @ other(X, R) <=> R = X.",
                  "dead @ tag(X, R) <=> integer(X) | R = 1."
                ]
            )
        length errs @?= 1
        ws @?= [InaccessibleBranch "int" "m:color"],
      testCase "a Haskell-side error suppresses its unit's warning too" $ do
        -- Constructor-arity errors are found in Haskell, not by a CHR
        -- rule, and are recorded against the unit being checked
        -- ('recordHsDiags'). Suppression has to see them: this rule
        -- is both dead and wrong, so only the error is reported.
        (errs, ws) <-
          checkModule
            ( mod_
                [ ":- chr_constraint sink(any).",
                  "dead @ tag(X, R) <=> integer(X) | R = 1, sink(red(1))."
                ]
            )
        length errs @?= 1
        ws @?= [],
      testCase "a class equation matching no signature errs exactly once" $ do
        -- A multi-signature class contributes one declaration per
        -- signature, but its equations belong to the group, not to
        -- each declaration: an equation that checks under no declared
        -- signature reports one NoMatchingOverload, not one per
        -- signature (Resolve used to gather the equation once per
        -- declaration, multiplying every class diagnostic N-fold).
        (errs, ws) <-
          checkModule
            ( mod_
                [ ":- class (g(int) -> int), (g(string) -> int).",
                  "g(true) -> 1."
                ]
            )
        errs @?= ["NoMatchingOverload \"m:g\""]
        ws @?= [],
      testCase "a Haskell-side error does not suppress another unit" $ do
        -- The same, across units: one rule's constructor-arity error
        -- must not take a different rule's warning with it.
        (errs, ws) <-
          checkModule
            ( mod_
                [ ":- chr_constraint sink(any).",
                  "bad @ other(_, _) <=> sink(red(1)).",
                  "dead @ tag(X, R) <=> integer(X) | R = 1."
                ]
            )
        length errs @?= 1
        ws @?= [InaccessibleBranch "int" "m:color"]
    ]
