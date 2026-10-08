{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Tests for "YCHR.Internal.VM.Closure".
--
-- The check is an assertion the compiler runs over its own output, so
-- the tests here are what proves it can fail: a program with a
-- well-formed table reports nothing, and a call, an evaluables entry or
-- a callables entry naming no procedure is reported with the name. The
-- union form @Session.withCHRExtra@ uses is covered too, because an
-- extra may call a compiled procedure and one extra may call another.
module YCHR.VM.ClosureTest (tests) where

import Control.Exception (ErrorCall (..), try)
import Data.List (isInfixOf)
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertBool, assertFailure, testCase, (@?=))
import YCHR.Internal.Parser (builtinOps)
import YCHR.Internal.Runtime.Registry (baseHostCallRegistry)
import YCHR.Internal.Runtime.Session (mkSessionInput, withCHRExtra)
import YCHR.Internal.VM
  ( ArgIndex (..),
    BoolExpr (..),
    CallArg (..),
    CallableKey (..),
    ConstraintType (..),
    EvaluableKey (..),
    IdExpr (..),
    Literal (..),
    Name,
    ProcKind (..),
    Procedure (..),
    Program (..),
    Stmt (..),
    ValExpr (..),
  )
import YCHR.Internal.VM.Closure
  ( closureFailure,
    danglingCallables,
    danglingCalls,
    danglingTargets,
    procedureNames,
  )

tests :: TestTree
tests =
  testGroup
    "YCHR.Internal.VM.Closure"
    [ closedTests,
      danglingTests,
      dispatchTableTests,
      unionTests,
      messageTests
    ]

-- ---------------------------------------------------------------------------
-- Fixtures
-- ---------------------------------------------------------------------------

mkProc :: Name -> [Stmt] -> Procedure
mkProc n body =
  Procedure
    { name = n,
      params = [],
      body = body,
      procKind = PKReactivateDispatch
    }

programWith ::
  [Procedure] ->
  [(EvaluableKey, Name)] ->
  [(CallableKey, Name)] ->
  Program
programWith procs evs cls =
  Program
    { typeNames = [],
      ruleNames = [],
      procedures = procs,
      evaluables = evs,
      callables = cls,
      inertTypes = []
    }

-- ---------------------------------------------------------------------------
-- Closed programs
-- ---------------------------------------------------------------------------

closedTests :: TestTree
closedTests =
  testGroup
    "closed programs"
    [ testCase "a call to another procedure of the program is closed" $
        danglingTargets
          ( programWith
              [ mkProc "a" [ExprStmt (CallExpr "b" [])],
                mkProc "b" []
              ]
              []
              []
          )
          @?= [],
      testCase "a call nested in a call's argument is closed" $
        danglingTargets
          ( programWith
              [ mkProc "a" [ExprStmt (CallExpr "b" [AVal (CallExpr "c" [])])],
                mkProc "b" [],
                mkProc "c" []
              ]
              []
              []
          )
          @?= [],
      testCase "evaluables and callables targets that exist are closed" $
        danglingTargets
          ( programWith
              [mkProc "f1" [], mkProc "lambda0" []]
              [(EvaluableKey "f" 1, "f1")]
              [(CallableKey "/" "f/1" 1, "lambda0")]
          )
          @?= [],
      testCase "a program with no calls at all is closed" $
        danglingTargets (programWith [mkProc "a" []] [] []) @?= []
    ]

-- ---------------------------------------------------------------------------
-- Dangling call sites
-- ---------------------------------------------------------------------------

danglingTests :: TestTree
danglingTests =
  testGroup
    "dangling call sites"
    [ testCase "a call to a name no procedure defines is reported" $
        danglingTargets (programWith [mkProc "a" [ExprStmt (CallExpr "ghost" [])]] [] [])
          @?= ["ghost"],
      testCase "a call nested in a call's argument is found" $
        danglingTargets
          ( programWith
              [ mkProc "a" [ExprStmt (CallExpr "b" [AVal (CallExpr "ghost" [])])],
                mkProc "b" []
              ]
              []
              []
          )
          @?= ["ghost"],
      testCase "a call under an If and a BoolExpr is found" $
        danglingTargets
          ( programWith
              [ mkProc
                  "a"
                  [ If
                      (BFromVal (CallExpr "ghost1" []))
                      [ExprStmt (CallExpr "ghost2" [])]
                      [Return (CallExpr "ghost3" [])]
                  ]
              ]
              []
              []
          )
          @?= ["ghost1", "ghost2", "ghost3"],
      testCase "a call in a Foreach condition and body is found" $
        danglingTargets
          ( programWith
              [ mkProc
                  "a"
                  [ Foreach
                      "l"
                      (ConstraintType 0)
                      "s"
                      [(ArgIndex 0, CallExpr "ghost1" [])]
                      [ BoolExprStmt
                          ( BAlive
                              (CreateConstraint (ConstraintType 1) [CallExpr "ghost2" []])
                          )
                      ]
                  ]
              ]
              []
              []
          )
          @?= ["ghost1", "ghost2"],
      testCase "a call in an ApplyClosure operand is found" $
        danglingTargets
          (programWith [mkProc "a" [ExprStmt (ApplyClosure (CallExpr "ghost" []) [])]] [] [])
          @?= ["ghost"],
      testCase "duplicates collapse and the first appearance wins" $
        danglingTargets
          ( programWith
              [ mkProc
                  "a"
                  [ ExprStmt (CallExpr "b" []),
                    ExprStmt (CallExpr "c" []),
                    ExprStmt (CallExpr "b" [])
                  ]
              ]
              []
              []
          )
          @?= ["b", "c"],
      testCase "a call inside a literal-only body is not invented" $
        danglingTargets (programWith [mkProc "a" [Return (Lit (IntLit 1))]] [] []) @?= []
    ]

-- ---------------------------------------------------------------------------
-- Dispatch tables
-- ---------------------------------------------------------------------------

dispatchTableTests :: TestTree
dispatchTableTests =
  testGroup
    "dispatch tables"
    [ testCase "an evaluables target no procedure defines is reported" $
        danglingTargets (programWith [] [(EvaluableKey "f" 1, "missing")] [])
          @?= ["missing"],
      testCase "a callables target no procedure defines is reported" $
        danglingTargets (programWith [] [] [(CallableKey "/" "f/1" 1, "missing")])
          @?= ["missing"],
      testCase "call-site and dispatch-table misses are reported together" $
        danglingTargets
          ( programWith
              [mkProc "a" [ExprStmt (CallExpr "ghostCall" [])]]
              [(EvaluableKey "f" 1, "ghostEval")]
              [(CallableKey "/" "g/1" 1, "ghostCallable")]
          )
          @?= ["ghostCall", "ghostEval", "ghostCallable"]
    ]

-- ---------------------------------------------------------------------------
-- Extras resolve against the union
-- ---------------------------------------------------------------------------

unionTests :: TestTree
unionTests =
  testGroup
    "query-time extras"
    [ testCase "an extra calling a compiled procedure is closed" $
        let compiled = procedureNames [mkProc "compiled" []]
            extras = [mkProc "__lambda_0" [ExprStmt (CallExpr "compiled" [])]]
            known = compiled <> procedureNames extras
         in danglingCalls known extras @?= [],
      testCase "an extra calling another extra is closed" $
        let compiled = procedureNames [mkProc "compiled" []]
            extras =
              [ mkProc "__lambda_0" [ExprStmt (CallExpr "__lambda_1" [])],
                mkProc "__lambda_1" []
              ]
            known = compiled <> procedureNames extras
         in danglingCalls known extras @?= [],
      testCase "an extra calling a name in neither set is reported" $
        let compiled = procedureNames [mkProc "compiled" []]
            extras = [mkProc "__lambda_0" [ExprStmt (CallExpr "ghost" [])]]
            known = compiled <> procedureNames extras
         in danglingCalls known extras @?= ["ghost"],
      testCase "an extra callables target must resolve in the union" $
        let compiled = procedureNames [mkProc "compiled" []]
            known = compiled <> procedureNames [mkProc "__lambda_0" []]
         in danglingCallables known [(CallableKey "__closure" "__lambda_0" 1, "ghost")]
              @?= ["ghost"],
      testCase "withCHRExtra rejects an extra that calls an unknown procedure" $ do
        -- The pure checks above can pass while the wiring that runs them
        -- is deleted; this is the one case that would notice.
        let si =
              mkSessionInput
                (programWith [] [] [])
                Map.empty
                Set.empty
                builtinOps
            extra = mkProc "__lambda_0" [ExprStmt (CallExpr "ghost" [])]
        outcome <-
          try (withCHRExtra si baseHostCallRegistry [extra] [] (pure ())) ::
            IO (Either ErrorCall ())
        case outcome of
          Left (ErrorCall msg) ->
            assertBool
              ("the message should name the target, got: " ++ msg)
              ("ghost" `isInfixOf` msg)
          Right () -> assertFailure "expected the closure check to reject the extra"
    ]

-- ---------------------------------------------------------------------------
-- Message
-- ---------------------------------------------------------------------------

messageTests :: TestTree
messageTests =
  testGroup
    "closureFailure"
    [ testCase "no report for a closed program" $
        closureFailure "compileModules" [] @?= Nothing,
      testCase "the first dangling target is named" $
        closureFailure "compileModules" ["first", "second"]
          @?= Just "compileModules: call to unknown procedure first"
    ]
