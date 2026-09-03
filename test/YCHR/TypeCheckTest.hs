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
      testCase "a self-referential equality pins the constructor, no cycle" $ do
        -- `f(X, X)` relates T with list(T). The pin never copies the
        -- partner's structure beyond the outermost constructor —
        -- T := list(beta) with a fresh rigid beta — so no cyclic
        -- term is built and nothing is reported: the equation is
        -- satisfiable (`f([], [])` fires it from gradual code).
        (errs, ws) <-
          checkModule
            ( mod_
                [ ":- function f(T, prelude:list(T)) -> int.",
                  "f(X, X) -> 1."
                ]
            )
        errs @?= []
        ws @?= [],
      testCase "a cycle-closing merge across two skolems stays finite" $ do
        -- No-hang regression: the first equality merges the two
        -- heads' skolems, the second then relates the merged skolem
        -- with `list` of itself. The parametric pin uses a fresh
        -- rigid parameter instead of the partner's structure, so no
        -- cyclic term can be built even through the alias chain.
        (errs, ws) <-
          checkModule
            ( mod_
                [ ":- chr_constraint a(T, T), b(T, prelude:list(T)).",
                  "live @ a(X, Y), b(X, Y) <=> true."
                ]
            )
        errs @?= []
        ws @?= [],
      testCase "a parameter-depth mismatch under a shared constructor stays live" $ do
        -- `box(int)` and `box(bool)` positions sharing a variable
        -- differ only inside the shared constructor, and the value
        -- `bx0` satisfies the equality — the rule can fire, so no
        -- inaccessible-branch warning is due. (The golden harness
        -- cannot assert a warning's absence; this pins it.)
        (errs, ws) <-
          checkModule
            ( mod_
                [ ":- chr_type box(A) ---> bx0 ; bx(A).",
                  ":- chr_constraint bi(box(int)), bb(box(prelude:bool)).",
                  "live @ bi(X), bb(X) <=> true."
                ]
            )
        errs @?= []
        ws @?= [],
      testCase "a parametric pin leaves the parameter rigid" $ do
        -- A skolem shared with a `list(int)` position learns only
        -- that it is a list — `T := list(beta)` with beta fresh and
        -- rigid, unrelated to `int` — so using an element at `int`
        -- is an error: the witnessing value may be `[]` at any
        -- element type.
        (errs, ws) <-
          checkModule
            ( mod_
                [ ":- chr_constraint p(T, T), q(prelude:list(int)), out(int).",
                  "bad @ p(X, [H | _]), q(X) <=> out(H)."
                ]
            )
        case errs of
          [e] | "InconsistentTypes" `T.isInfixOf` T.pack e -> pure ()
          _ -> assertFailure ("expected one InconsistentTypes error, got: " ++ show errs)
        ws @?= [],
      testCase "merge and pin commute" $ do
        -- Whether the skolem merge happens before or after one side
        -- is pinned, the result is the same shared pin. HNF emits a
        -- shared variable's GuardEqual at its /second/ occurrence,
        -- so head order forces the two evidence orders: in `mf` the
        -- X-link (skolem merge) precedes the Y-link (parametric
        -- pin); in `pf` the Y-link (pin) precedes the X-link
        -- (merge, now through the pin).
        (errsMergeFirst, wsMergeFirst) <-
          checkModule
            ( mod_
                [ ":- chr_constraint a(T, T), b(T, prelude:list(T)).",
                  "mf @ a(X, Y), b(X, Y) <=> true."
                ]
            )
        (errsPinFirst, wsPinFirst) <-
          checkModule
            ( mod_
                [ ":- chr_constraint a(T, T), b(T, prelude:list(T)).",
                  "pf @ b(X, Y), a(Y, X) <=> true."
                ]
            )
        (errsMergeFirst, wsMergeFirst) @?= ([], [])
        (errsPinFirst, wsPinFirst) @?= ([], []),
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
      testCase "a declaration-check error suppresses its unit's warning too" $ do
        -- Constructor-arity errors come from the declaration checks
        -- (@pure.chr@), not from a solver rule, and are recorded
        -- against the unit being checked. Suppression has to see them:
        -- this rule is both dead and wrong, so only the error is
        -- reported.
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
