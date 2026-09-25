{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Tests for the interpreter's slot phase
-- ("YCHR.Internal.Runtime.Slots").
--
-- The properties under test are the ones the interpreter's environment
-- depends on: parameters take the first slots in order, every other
-- binder takes the next one and is visible to the statements that
-- follow it, a re-binding shadows, and the walk is total — a name that
-- is not in scope lowers to a slot nothing binds, so the runtime still
-- reports its own "unbound variable" error rather than the phase
-- failing.
module YCHR.Runtime.SlotsTest (tests) where

import Data.Map.Strict qualified as Map
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertFailure, testCase, (@?=))
import YCHR.Internal.Runtime.Slots
import YCHR.Internal.Types (ConstraintType (..), RuleId (..))
import YCHR.Internal.VM
  ( ArgIndex (..),
    BoolExpr (..),
    CallArg (..),
    IdExpr (..),
    Literal (..),
    Name,
    ProcKind (..),
    Procedure (..),
    Program (..),
    Stmt (..),
    ValExpr (..),
    mkHistoryIds,
  )

tests :: TestTree
tests =
  testGroup
    "YCHR.Internal.Runtime.Slots"
    [ slotTests,
      scopeTests,
      totalityTests,
      programTests
    ]

-- ---------------------------------------------------------------------------
-- Fixtures
-- ---------------------------------------------------------------------------

mkProc :: Name -> [Name] -> [Stmt] -> Procedure
mkProc n ps body =
  Procedure
    { name = n,
      params = ps,
      body = body,
      procKind = PKReactivateDispatch
    }

-- | The lowered body of a procedure with the given parameters and body.
lowerBody :: [Name] -> [Stmt] -> [SlotStmt]
lowerBody params body = (lowerProcedure (mkProc "p" params body)).slotProcBody

programWith :: [Procedure] -> Program
programWith procs =
  Program
    { numTypes = 1,
      typeNames = [],
      numRules = 0,
      ruleNames = [],
      procedures = procs,
      evaluables = [],
      callables = [],
      inertTypes = []
    }

-- ---------------------------------------------------------------------------
-- Slots
-- ---------------------------------------------------------------------------

slotTests :: TestTree
slotTests =
  testGroup
    "slot assignment"
    [ testCase "parameters take slots 0..n-1, reported as the arity" $ do
        let lowered =
              lowerProcedure (mkProc "p" ["a", "b"] [Return (Var "a"), Return (Var "b")])
        lowered.slotProcArity @?= 2
        lowered.slotProcBody @?= [SReturn (SVar 0 "a"), SReturn (SVar 1 "b")],
      testCase "a let binder takes the next slot and is visible afterwards" $
        lowerBody [] [LetVal "x" (Lit (IntLit 1)), Return (Var "x")]
          @?= [SLetVal 0 (SLit (IntLit 1)), SReturn (SVar 0 "x")],
      testCase "a let right-hand side is lowered before its binder is in scope" $
        -- The reference cannot see the binding being defined, so it gets
        -- slot 0 with no earlier binder and the binder takes slot 1; at
        -- run time that is the same unbound-variable error the VM
        -- produces.
        lowerBody [] [LetVal "x" (Var "x"), Return (Var "x")]
          @?= [SLetVal 1 (SVar 0 "x"), SReturn (SVar 1 "x")],
      testCase "a re-binding shadows with a fresh slot" $
        lowerBody
          []
          [ LetVal "x" (Lit (IntLit 1)),
            LetVal "x" (Lit (IntLit 2)),
            Return (Var "x")
          ]
          @?= [ SLetVal 0 (SLit (IntLit 1)),
                SLetVal 1 (SLit (IntLit 2)),
                SReturn (SVar 1 "x")
              ],
      testCase "AssignVal targets the binding in scope" $
        lowerBody [] [LetVal "x" (Lit (IntLit 1)), AssignVal "x" (Lit (IntLit 2))]
          @?= [SLetVal 0 (SLit (IntLit 1)), SAssignVal 0 (SLit (IntLit 2))],
      testCase "a Foreach binds its loop variable for the body" $
        lowerBody
          []
          [Foreach "l" (ConstraintType 0) "s" [] [BoolExprStmt (BAlive (IdVar "s"))]]
          @?= [SForeach "l" (ConstraintType 0) 0 [] [SBoolExprStmt (SBAlive (SIdVar 0 "s"))]],
      testCase "Foreach conditions are lowered in the enclosing scope" $
        lowerBody
          ["a"]
          [ Foreach
              "l"
              (ConstraintType 0)
              "s"
              [(ArgIndex 1, Var "a")]
              [Return (Lit (IntLit 0))]
          ]
          @?= [ SForeach
                  "l"
                  (ConstraintType 0)
                  1
                  [(ArgIndex 1, SVar 0 "a")]
                  [SReturn (SLit (IntLit 0))]
              ],
      testCase "DrainReactivationQueue introduces its variable" $
        lowerBody
          []
          [ DrainReactivationQueue
              "q"
              [ExprStmt (CallExpr "reactivate_dispatch" [AId (IdVar "q")])]
          ]
          @?= [ SDrainReactivationQueue
                  0
                  [SExprStmt (SCallExpr "reactivate_dispatch" [SCallId (SIdVar 0 "q")])]
              ],
      testCase "a Tell procedure's fresh id keeps its slot through the call" $
        -- The shape 'genTell' emits: create an id, pass the id to
        -- activate, then pass it again to Store.
        lowerBody
          ["X"]
          [ LetId "active" (CreateConstraint (ConstraintType 7) [Var "X"]),
            ExprStmt (CallExpr "activate_c" [AId (IdVar "active")]),
            Store (IdVar "active")
          ]
          @?= [ SLetId 1 (SCreateConstraint (ConstraintType 7) [SVar 0 "X"]),
                SExprStmt (SCallExpr "activate_c" [SCallId (SIdVar 1 "active")]),
                SStore (SIdVar 1 "active")
              ]
    ]

-- ---------------------------------------------------------------------------
-- Scoping
-- ---------------------------------------------------------------------------

scopeTests :: TestTree
scopeTests =
  testGroup
    "scoping"
    [ testCase "a binding made inside a branch is visible after it" $
        -- The interpreter's environment is one mutable map, so a
        -- binding inside a branch persists past the conditional; the
        -- phase must agree, or a reference after the branch would
        -- resolve to a different slot than the one the branch wrote.
        lowerBody
          []
          [ If (BLit True) [LetVal "x" (Lit (IntLit 1))] [],
            Return (Var "x")
          ]
          @?= [SIf (SBLit True) [SLetVal 0 (SLit (IntLit 1))] [], SReturn (SVar 0 "x")],
      testCase "an If arm's binding is in scope for the other arm" $
        -- The interpreter's environment is one flat map, so a binding an
        -- If arm makes lives on for the other arm and for what follows
        -- the If. Emitted code never binds in an else arm, which is what
        -- makes the walk's slot choice unambiguous; this case pins that
        -- reading so changing it has to be deliberate.
        lowerBody
          []
          [ If (BLit True) [LetVal "x" (Lit (IntLit 1))] [Return (Var "x")],
            Return (Var "x")
          ]
          @?= [ SIf
                  (SBLit True)
                  [SLetVal 0 (SLit (IntLit 1))]
                  [SReturn (SVar 0 "x")],
                SReturn (SVar 0 "x")
              ],
      testCase "a binding inside a loop body is visible to the rest of the body" $
        lowerBody
          []
          [ Foreach
              "l"
              (ConstraintType 0)
              "s"
              []
              [ LetVal "x" (FieldArg (IdVar "s") (ArgIndex 0)),
                Return (Var "x")
              ]
          ]
          @?= [ SForeach
                  "l"
                  (ConstraintType 0)
                  0
                  []
                  [ SLetVal 1 (SFieldArg (SIdVar 0 "s") (ArgIndex 0)),
                    SReturn (SVar 1 "x")
                  ]
              ]
    ]

-- ---------------------------------------------------------------------------
-- Totality
-- ---------------------------------------------------------------------------

totalityTests :: TestTree
totalityTests =
  testGroup
    "totality"
    [ testCase "a reference to an unbound name lowers to a never-bound slot" $ do
        let body = lowerBody [] [Return (Var "ghost")]
        body @?= [SReturn (SVar 0 "ghost")],
      testCase "an assignment to an unbound name lowers to a never-bound slot" $
        lowerBody [] [AssignVal "ghost" (Lit (IntLit 1))]
          @?= [SAssignVal 0 (SLit (IntLit 1))],
      testCase "a program with no procedures lowers to no procedures" $
        (lowerProgram (programWith [])).slotProcedures @?= Map.empty
    ]

-- ---------------------------------------------------------------------------
-- Programs
-- ---------------------------------------------------------------------------

programTests :: TestTree
programTests =
  testGroup
    "lowerProgram"
    [ testCase "keeps the procedure names as keys" $
        let prog =
              programWith
                [ mkProc "tell_c" [] [],
                  mkProc "activate_c" [] []
                ]
            lowered = lowerProgram prog
         in Map.keys lowered.slotProcedures
              @?= ["activate_c", "tell_c"],
      testCase "lowers each procedure's parameters and body independently" $ do
        -- A name reused across procedures must not share a slot: slots
        -- are per procedure, because the interpreter's environment is.
        let prog =
              programWith
                [ mkProc "p" ["a"] [Return (Var "a")],
                  mkProc "q" ["b"] [Return (Var "b")]
                ]
            lowered = lowerProgram prog
        case Map.lookup "p" lowered.slotProcedures of
          Nothing -> assertFailure "p missing"
          Just p -> do
            p.slotProcArity @?= 1
            p.slotProcBody @?= [SReturn (SVar 0 "a")]
        case Map.lookup "q" lowered.slotProcedures of
          Nothing -> assertFailure "q missing"
          Just q -> do
            q.slotProcArity @?= 1
            q.slotProcBody @?= [SReturn (SVar 0 "b")],
      testCase "carries the proc kind through unchanged" $
        let lowered = lowerProcedure (mkProc "p" [] [])
         in lowered.slotProcKind @?= PKReactivateDispatch,
      testCase "history ids keep the canonical order mkHistoryIds established" $
        -- 'mkHistoryIds' orders by head position; the phase must not
        -- reorder them, or the same match would key differently from
        -- the tuple the compiler built.
        lowerBody
          ["a", "b"]
          [ AddHistory
              (RuleId 3)
              (mkHistoryIds [(1 :: Int, IdVar "b"), (0, IdVar "a")])
          ]
          @?= [SAddHistory (RuleId 3) [SIdVar 0 "a", SIdVar 1 "b"]],
      testCase "BoolExpr keeps its shape, including the soft-guard boundary" $
        lowerBody
          ["a"]
          [ BoolExprStmt
              ( BSoftGuard
                  (BAnd (BEqual (Var "a") (Lit (IntLit 0))) (BNot (BAlive (IdVar "x"))))
              )
          ]
          @?= [ SBoolExprStmt
                  ( SBSoftGuard
                      ( SBAnd
                          (SBEqual (SVar 0 "a") (SLit (IntLit 0)))
                          (SBNot (SBAlive (SIdVar 1 "x")))
                      )
                  )
              ]
    ]
