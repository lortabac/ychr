{-# LANGUAGE OverloadedStrings #-}

module YCHR.Runtime.VarTest (tests) where

import Control.Monad.IO.Class (liftIO)
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertBool, testCase, (@?=))
import YCHR.Internal.Runtime.Monad (Chr, initSessionEnv, runChr)
import YCHR.Internal.Runtime.Types (SuspensionId (..), Value (..))
import YCHR.Internal.Runtime.Var
  ( addObserver,
    deref,
    equal,
    getArg,
    getVarId,
    makeTerm,
    matchTerm,
    newVar,
    unifiable,
    unify,
  )

tests :: TestTree
tests =
  testGroup
    "YCHR.Internal.Runtime.Var"
    [ unifyTests,
      unifiableTests,
      unifiableRollbackTests,
      equalTests,
      observerTests,
      derefTests,
      termTests,
      wildcardTests
    ]

-- ---------------------------------------------------------------------------
-- Helpers
-- ---------------------------------------------------------------------------

runVarEnv :: Chr a -> IO a
runVarEnv action = do
  env <- initSessionEnv [] [] [] Map.empty Map.empty Map.empty Map.empty Set.empty
  runChr action env

-- | Run an action and also return the observers gathered by the final 'unify'.
runWithUnify ::
  (Value -> Value -> Chr (Bool, [SuspensionId])) ->
  Value ->
  Value ->
  IO (Bool, [SuspensionId])
runWithUnify u a b = runVarEnv (u a b)

-- | Assert that unification succeeds (discards observers).
assertUnifySuccess :: Value -> Value -> Chr ()
assertUnifySuccess a b = do
  (ok, _) <- unify a b
  liftIO $ assertBool "unify should succeed" ok

-- | Assert that unification fails (discards observers).
assertUnifyFailure :: Value -> Value -> Chr ()
assertUnifyFailure a b = do
  (ok, _) <- unify a b
  liftIO $ assertBool "unify should fail" (not ok)

-- | Assert that a value dereferences to a given Integer.
assertDerefInt :: Value -> Integer -> Chr ()
assertDerefInt v expected = do
  d <- deref v
  liftIO $ case d of
    VInt n -> n @?= expected
    _ -> assertBool ("expected VInt " ++ show expected) False

unifyTests :: TestTree
unifyTests =
  testGroup
    "unify"
    [ testCase "Var = Int" $ do
        runVarEnv $ do
          x <- newVar
          assertUnifySuccess x (VInt 42)
          assertDerefInt x 42,
      testCase "Var = Var, then bind" $ do
        runVarEnv $ do
          x <- newVar
          y <- newVar
          assertUnifySuccess x y
          assertUnifySuccess y (VInt 7)
          assertDerefInt x 7
          assertDerefInt y 7,
      testCase "Var = same Var (no-op)" $ do
        (ok, obs) <- runVarEnv $ do
          x <- newVar
          unify x x
        assertBool "same var unify succeeds" ok
        obs @?= [],
      testCase "Int = Int (same)" $ do
        (ok, _) <- runWithUnify unify (VInt 5) (VInt 5)
        assertBool "same ints unify" ok,
      testCase "Int = Int (different)" $ do
        runVarEnv $ assertUnifyFailure (VInt 1) (VInt 2),
      testCase "Atom = Atom (same)" $ do
        (ok, _) <- runWithUnify unify (VAtom "foo") (VAtom "foo")
        assertBool "same atoms unify" ok,
      testCase "Atom = Atom (different)" $ do
        runVarEnv $ assertUnifyFailure (VAtom "foo") (VAtom "bar"),
      testCase "Bool = Bool (same)" $ do
        (ok, _) <- runWithUnify unify (VBool True) (VBool True)
        assertBool "same bools unify" ok,
      testCase "Bool = Bool (different)" $ do
        runVarEnv $ assertUnifyFailure (VBool True) (VBool False),
      testCase "Term = Term (matching functor/arity)" $ do
        runVarEnv $ do
          x <- newVar
          y <- newVar
          let t1 = makeTerm "f" [x, VInt 1]
              t2 = makeTerm "f" [VInt 2, y]
          assertUnifySuccess t1 t2
          assertDerefInt x 2
          assertDerefInt y 1,
      testCase "Term = Term (different functor)" $ do
        runVarEnv $ assertUnifyFailure (makeTerm "f" [VInt 1]) (makeTerm "g" [VInt 1]),
      testCase "Term = Term (different arity)" $ do
        runVarEnv $
          assertUnifyFailure
            (makeTerm "f" [VInt 1])
            (makeTerm "f" [VInt 1, VInt 2]),
      testCase "Nested terms: f(X, g(1)) = f(2, g(Y))" $ do
        runVarEnv $ do
          x <- newVar
          y <- newVar
          let t1 = makeTerm "f" [x, makeTerm "g" [VInt 1]]
              t2 = makeTerm "f" [VInt 2, makeTerm "g" [y]]
          assertUnifySuccess t1 t2
          assertDerefInt x 2
          assertDerefInt y 1,
      testCase "Int = Atom (type mismatch)" $ do
        runVarEnv $ assertUnifyFailure (VInt 1) (VAtom "one"),
      testCase "Already-bound var: unify with same value succeeds" $ do
        runVarEnv $ do
          x <- newVar
          assertUnifySuccess x (VInt 1)
          assertUnifySuccess x (VInt 1)
          assertDerefInt x 1,
      testCase "Already-bound var: unify with different value fails" $ do
        runVarEnv $ do
          x <- newVar
          assertUnifySuccess x (VInt 1)
          assertUnifyFailure x (VInt 2)
    ]

assertUnifiable :: Value -> Value -> Bool -> Chr ()
assertUnifiable a b expected = do
  r <- unifiable a b
  liftIO $ r @?= expected

unifiableTests :: TestTree
unifiableTests =
  testGroup
    "unifiable"
    [ testCase "Int = Int (same)" $ runVarEnv $ assertUnifiable (VInt 1) (VInt 1) True,
      testCase "Int = Int (different)" $
        runVarEnv $
          assertUnifiable (VInt 1) (VInt 2) False,
      testCase "Atom = Atom (same)" $
        runVarEnv $
          assertUnifiable (VAtom "a") (VAtom "a") True,
      testCase "Atom = Atom (different)" $
        runVarEnv $
          assertUnifiable (VAtom "a") (VAtom "b") False,
      testCase "Bool = Bool (same)" $
        runVarEnv $
          assertUnifiable (VBool True) (VBool True) True,
      testCase "Bool = Bool (different)" $
        runVarEnv $
          assertUnifiable (VBool True) (VBool False) False,
      testCase "Text = Text (same)" $
        runVarEnv $
          assertUnifiable (VText "x") (VText "x") True,
      testCase "Text = Text (different)" $
        runVarEnv $
          assertUnifiable (VText "x") (VText "y") False,
      testCase "Same unbound var" $ runVarEnv $ do
        x <- newVar
        assertUnifiable x x True,
      testCase "Two distinct unbound vars" $ runVarEnv $ do
        x <- newVar
        y <- newVar
        assertUnifiable x y True,
      testCase "Unbound var vs ground" $ runVarEnv $ do
        x <- newVar
        assertUnifiable x (VInt 42) True,
      testCase "Ground vs unbound var" $ runVarEnv $ do
        x <- newVar
        assertUnifiable (VInt 42) x True,
      testCase "Wildcard vs ground" $
        runVarEnv $
          assertUnifiable VWildcard (VInt 7) True,
      testCase "Compound: matching ground args" $
        runVarEnv $
          assertUnifiable (makeTerm "f" [VInt 1, VInt 2]) (makeTerm "f" [VInt 1, VInt 2]) True,
      testCase "Compound: mismatched functor" $
        runVarEnv $
          assertUnifiable (makeTerm "f" [VInt 1]) (makeTerm "g" [VInt 1]) False,
      testCase "Compound: mismatched arity" $
        runVarEnv $
          assertUnifiable (makeTerm "f" [VInt 1]) (makeTerm "f" [VInt 1, VInt 2]) False,
      testCase "Compound with var arg: f(1, X) = f(1, 2)" $ runVarEnv $ do
        x <- newVar
        assertUnifiable (makeTerm "f" [VInt 1, x]) (makeTerm "f" [VInt 1, VInt 2]) True,
      testCase "Compound nested failure: f(X, 1) = f(2, 3)" $ runVarEnv $ do
        x <- newVar
        assertUnifiable (makeTerm "f" [x, VInt 1]) (makeTerm "f" [VInt 2, VInt 3]) False,
      testCase "Transitively unifiable: f(X, X) = f(1, 1)" $ runVarEnv $ do
        x <- newVar
        assertUnifiable (makeTerm "f" [x, x]) (makeTerm "f" [VInt 1, VInt 1]) True,
      testCase "Transitively non-unifiable: f(X, X) = f(1, 2)" $ runVarEnv $ do
        x <- newVar
        assertUnifiable (makeTerm "f" [x, x]) (makeTerm "f" [VInt 1, VInt 2]) False,
      testCase "Type mismatch: Int vs Atom" $
        runVarEnv $
          assertUnifiable (VInt 1) (VAtom "a") False,
      testCase "Chained bind then unifiable ground" $ runVarEnv $ do
        x <- newVar
        y <- newVar
        _ <- unify x y
        r <- unifiable x (VInt 1)
        liftIO $ r @?= True
    ]

assertUnifiableNoMutation :: [Value] -> Value -> Value -> Bool -> Chr ()
assertUnifiableNoMutation vars a b expected = do
  before <- traverse getVarId vars
  r <- unifiable a b
  liftIO $ r @?= expected
  after <- traverse getVarId vars
  liftIO $ before @?= after

unifiableRollbackTests :: TestTree
unifiableRollbackTests =
  testGroup
    "unifiable rollback"
    [ testCase "Var-Var success: both stay unbound" $ runVarEnv $ do
        x <- newVar
        y <- newVar
        assertUnifiableNoMutation [x, y] x y True,
      testCase "Var-NonVar success: var stays unbound" $ runVarEnv $ do
        x <- newVar
        assertUnifiableNoMutation [x] x (VInt 42) True,
      testCase "NonVar-Var success (symmetric): var stays unbound" $ runVarEnv $ do
        x <- newVar
        assertUnifiableNoMutation [x] (VInt 42) x True,
      testCase "Bind then fail inside compound: var rolls back" $ runVarEnv $ do
        x <- newVar
        assertUnifiableNoMutation
          [x]
          (makeTerm "f" [x, VInt 1])
          (makeTerm "f" [VInt 2, VInt 3])
          False,
      testCase "Double-bind failure: f(X,X) vs f(1,2) rolls X back" $ runVarEnv $ do
        x <- newVar
        assertUnifiableNoMutation
          [x]
          (makeTerm "f" [x, x])
          (makeTerm "f" [VInt 1, VInt 2])
          False,
      testCase "Success inside deeper compound: all vars stay unbound" $ runVarEnv $ do
        x <- newVar
        y <- newVar
        assertUnifiableNoMutation
          [x, y]
          (makeTerm "f" [x, y])
          (makeTerm "f" [VInt 1, VInt 2])
          True,
      testCase "Failure with multiple rolled-back bindings" $ runVarEnv $ do
        x <- newVar
        y <- newVar
        assertUnifiableNoMutation
          [x, y]
          (makeTerm "f" [x, y, VInt 1])
          (makeTerm "f" [VInt 1, VInt 2, VInt 9])
          False,
      testCase "Pre-bound var stays bound after failing unifiable" $ runVarEnv $ do
        x <- newVar
        _ <- unify x (VInt 7)
        r <- unifiable x (VInt 8)
        liftIO $ r @?= False
        mid <- getVarId x
        liftIO $ mid @?= Nothing
        eq <- equal x (VInt 7)
        liftIO $ eq @?= True
    ]

equalTests :: TestTree
equalTests =
  testGroup
    "equal"
    [ testCase "Same unbound var" $ do
        runVarEnv $ do
          x <- newVar
          r <- equal x x
          liftIO $ r @?= True,
      testCase "Distinct unbound vars" $ do
        runVarEnv $ do
          x <- newVar
          y <- newVar
          r <- equal x y
          liftIO $ r @?= False,
      testCase "Unbound var vs ground" $ do
        runVarEnv $ do
          x <- newVar
          r <- equal x (VInt 1)
          liftIO $ r @?= False,
      testCase "Ground vs unbound var" $ do
        runVarEnv $ do
          x <- newVar
          r <- equal (VInt 1) x
          liftIO $ r @?= False,
      testCase "Same int" $ do
        r <- runVarEnv $ equal (VInt 42) (VInt 42)
        r @?= True,
      testCase "Different int" $ do
        r <- runVarEnv $ equal (VInt 1) (VInt 2)
        r @?= False,
      testCase "Same atom" $ do
        r <- runVarEnv $ equal (VAtom "x") (VAtom "x")
        r @?= True,
      testCase "Same term structure" $ do
        r <-
          runVarEnv $
            equal
              (makeTerm "f" [VInt 1, VAtom "a"])
              (makeTerm "f" [VInt 1, VAtom "a"])
        r @?= True,
      testCase "Different term structure" $ do
        r <- runVarEnv $ equal (makeTerm "f" [VInt 1]) (makeTerm "f" [VInt 2])
        r @?= False,
      testCase "After unification: var bound to int" $ do
        runVarEnv $ do
          x <- newVar
          _ <- unify x (VInt 5)
          r <- equal x (VInt 5)
          liftIO $ r @?= True,
      testCase "Two vars bound to same value" $ do
        runVarEnv $ do
          x <- newVar
          y <- newVar
          _ <- unify x (VInt 3)
          _ <- unify y (VInt 3)
          r <- equal x y
          liftIO $ r @?= True,
      testCase "Var bound to var, both equal after binding" $ do
        runVarEnv $ do
          x <- newVar
          y <- newVar
          _ <- unify x y
          _ <- unify y (VAtom "hello")
          r <- equal x (VAtom "hello")
          liftIO $ r @?= True
    ]

observerTests :: TestTree
observerTests =
  testGroup
    "observers"
    [ testCase "No observers: unify returns empty list" $ do
        obs <- runVarEnv $ do
          x <- newVar
          (_, obs) <- unify x (VInt 1)
          pure obs
        obs @?= [],
      testCase "Single observer returned on bind" $ do
        (ok, obs) <- runVarEnv $ do
          x <- newVar
          addObserver (SuspensionId 10) x
          unify x (VInt 1)
        assertBool "unify succeeds" ok
        obs @?= [SuspensionId 10],
      testCase "Multiple observers all returned" $ do
        (ok, obs) <- runVarEnv $ do
          x <- newVar
          addObserver (SuspensionId 1) x
          addObserver (SuspensionId 2) x
          addObserver (SuspensionId 3) x
          unify x (VInt 1)
        assertBool "unify succeeds" ok
        length obs @?= 3,
      testCase "Var-Var merge: observers from bound var collected" $ do
        (ok, obs) <- runVarEnv $ do
          x <- newVar
          y <- newVar
          addObserver (SuspensionId 1) x
          addObserver (SuspensionId 2) y
          unify x y
        assertBool "unify succeeds" ok
        obs @?= [SuspensionId 1],
      testCase "addObserver on ground value is no-op" $ do
        runVarEnv $ do
          addObserver (SuspensionId 99) (VInt 42)
          pure (),
      testCase "Observers transfer onto newly reachable vars" $ do
        -- Observation is over the unbound variables *reachable* from a
        -- suspension's arguments, and binding X to a term changes that
        -- set: A becomes reachable, X stops being. Without the
        -- transfer, binding A later would wake nobody and the omega-r
        -- Reactivate step would be silently skipped.
        (ok, obs) <- runVarEnv $ do
          x <- newVar
          a <- newVar
          addObserver (SuspensionId 7) x
          _ <- unify x (VTerm "g" [a])
          unify a (VInt 1)
        assertBool "unify succeeds" ok
        obs @?= [SuspensionId 7],
      testCase "Transfer reaches a var nested in a compound" $ do
        -- The transfer walks the term it binds to, so a variable
        -- several levels down is observed too.
        (ok, obs) <- runVarEnv $ do
          x <- newVar
          a <- newVar
          addObserver (SuspensionId 8) x
          _ <- unify x (VTerm "outer" [VTerm "inner" [a]])
          unify a (VInt 1)
        assertBool "unify succeeds" ok
        obs @?= [SuspensionId 8]
    ]

derefTests :: TestTree
derefTests =
  testGroup
    "deref"
    [ testCase "Unbound var derefs to itself" $ do
        runVarEnv $ do
          x <- newVar
          d <- deref x
          r <- equal d x
          liftIO $ r @?= True,
      testCase "Single binding: var→int" $ do
        runVarEnv $ do
          x <- newVar
          _ <- unify x (VInt 10)
          assertDerefInt x 10,
      testCase "Chain: var→var→var→int" $ do
        runVarEnv $ do
          x <- newVar
          y <- newVar
          z <- newVar
          _ <- unify x y
          _ <- unify y z
          _ <- unify z (VInt 100)
          assertDerefInt x 100
          assertDerefInt y 100
          assertDerefInt z 100
    ]

termTests :: TestTree
termTests =
  testGroup
    "terms"
    [ testCase "matchTerm: correct functor/arity" $ do
        r <- runVarEnv $ matchTerm (makeTerm "f" [VInt 1, VInt 2]) "f" 2
        r @?= True,
      testCase "matchTerm: wrong functor" $ do
        r <- runVarEnv $ matchTerm (makeTerm "f" [VInt 1]) "g" 1
        r @?= False,
      testCase "matchTerm: wrong arity" $ do
        r <- runVarEnv $ matchTerm (makeTerm "f" [VInt 1]) "f" 2
        r @?= False,
      testCase "matchTerm: non-term" $ do
        r <- runVarEnv $ matchTerm (VInt 42) "f" 0
        r @?= False,
      testCase "matchTerm through var" $ do
        runVarEnv $ do
          x <- newVar
          _ <- unify x (makeTerm "g" [VInt 1, VInt 2, VInt 3])
          r <- matchTerm x "g" 3
          liftIO $ r @?= True,
      testCase "getArg: correct index" $ do
        let t = makeTerm "f" [VInt 10, VAtom "b", VInt 30]
        (a0, a1, a2) <- runVarEnv $ do
          a0 <- getArg t 0
          a1 <- getArg t 1
          a2 <- getArg t 2
          pure (a0, a1, a2)
        case a0 of VInt 10 -> pure (); _ -> assertBool "arg 0" False
        case a1 of VAtom "b" -> pure (); _ -> assertBool "arg 1" False
        case a2 of VInt 30 -> pure (); _ -> assertBool "arg 2" False,
      testCase "getArg through var" $ do
        runVarEnv $ do
          x <- newVar
          _ <- unify x (makeTerm "h" [VInt 5])
          a <- getArg x 0
          liftIO $ case a of
            VInt 5 -> pure ()
            _ -> assertBool "expected VInt 5" False
    ]

wildcardTests :: TestTree
wildcardTests =
  testGroup
    "wildcard"
    [ testCase "Wildcard unifies with Int" $ do
        (ok, _) <- runVarEnv $ unify VWildcard (VInt 42)
        ok @?= True,
      testCase "Int unifies with Wildcard" $ do
        (ok, _) <- runVarEnv $ unify (VInt 42) VWildcard
        ok @?= True,
      testCase "Wildcard does not bind Var" $ do
        runVarEnv $ do
          x <- newVar
          _ <- unify VWildcard x
          d <- deref x
          liftIO $ case d of
            VVar _ -> pure ()
            _ -> assertBool "var should remain unbound" False,
      testCase "Wildcard equal to Int is False" $ do
        r <- runVarEnv $ equal VWildcard (VInt 42)
        r @?= False
    ]
