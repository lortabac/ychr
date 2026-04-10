{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}

module YCHR.Runtime.VarTest (tests) where

import Effectful
import Effectful.Writer.Static.Local (Writer, runWriter)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertBool, testCase, (@?=))
import YCHR.Runtime.Types (SuspensionId (..), Value (..))
import YCHR.Runtime.Var (Unify, addObserver, deref, equal, getArg, getVarId, makeTerm, matchTerm, newVar, runUnify, unifiable, unify)

tests :: TestTree
tests =
  testGroup
    "YCHR.Runtime.Var"
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

-- | Run an Eff computation that uses Unify and Writer [SuspensionId].
runTestEnv :: Eff [Writer [SuspensionId], Unify, IOE] a -> IO (a, [SuspensionId])
runTestEnv = runEff . runUnify . runWriter @[SuspensionId]

-- | Like 'runLogic' but discards the collected observers.
runTestEnv_ :: Eff [Writer [SuspensionId], Unify, IOE] a -> IO a
runTestEnv_ m = fst <$> runTestEnv m

-- | Assert that unification succeeds.
assertUnifySuccess :: (Writer [SuspensionId] :> es, Unify :> es, IOE :> es) => Value -> Value -> Eff es ()
assertUnifySuccess a b = do
  ok <- unify a b
  liftIO $ assertBool "unify should succeed" ok

-- | Assert that unification fails.
assertUnifyFailure :: (Writer [SuspensionId] :> es, Unify :> es, IOE :> es) => Value -> Value -> Eff es ()
assertUnifyFailure a b = do
  ok <- unify a b
  liftIO $ assertBool "unify should fail" (not ok)

-- | Assert that a value dereferences to a given Int.
assertDerefInt :: (Unify :> es, IOE :> es) => Value -> Int -> Eff es ()
assertDerefInt v expected = do
  d <- deref v
  liftIO $ case d of
    VInt n -> n @?= expected
    _ -> assertBool ("expected VInt " ++ show expected) False

-- ---------------------------------------------------------------------------
-- Unify tests
-- ---------------------------------------------------------------------------

unifyTests :: TestTree
unifyTests =
  testGroup
    "unify"
    [ testCase "Var = Int" $ do
        runTestEnv_ $ do
          x <- newVar
          assertUnifySuccess x (VInt 42)
          assertDerefInt x 42,
      testCase "Var = Var, then bind" $ do
        runTestEnv_ $ do
          x <- newVar
          y <- newVar
          assertUnifySuccess x y
          assertUnifySuccess y (VInt 7)
          assertDerefInt x 7
          assertDerefInt y 7,
      testCase "Var = same Var (no-op)" $ do
        (ok, obs) <- runTestEnv $ do
          x <- newVar
          ok <- unify x x
          pure ok
        assertBool "same var unify succeeds" ok
        obs @?= [],
      testCase "Int = Int (same)" $ do
        (ok, _) <- runTestEnv $ unify (VInt 5) (VInt 5)
        assertBool "same ints unify" ok,
      testCase "Int = Int (different)" $ do
        runTestEnv_ $ assertUnifyFailure (VInt 1) (VInt 2),
      testCase "Atom = Atom (same)" $ do
        (ok, _) <- runTestEnv $ unify (VAtom "foo") (VAtom "foo")
        assertBool "same atoms unify" ok,
      testCase "Atom = Atom (different)" $ do
        runTestEnv_ $ assertUnifyFailure (VAtom "foo") (VAtom "bar"),
      testCase "Bool = Bool (same)" $ do
        (ok, _) <- runTestEnv $ unify (VBool True) (VBool True)
        assertBool "same bools unify" ok,
      testCase "Bool = Bool (different)" $ do
        runTestEnv_ $ assertUnifyFailure (VBool True) (VBool False),
      testCase "Term = Term (matching functor/arity)" $ do
        runTestEnv_ $ do
          x <- newVar
          y <- newVar
          let t1 = makeTerm "f" [x, VInt 1]
              t2 = makeTerm "f" [VInt 2, y]
          assertUnifySuccess t1 t2
          assertDerefInt x 2
          assertDerefInt y 1,
      testCase "Term = Term (different functor)" $ do
        runTestEnv_ $ assertUnifyFailure (makeTerm "f" [VInt 1]) (makeTerm "g" [VInt 1]),
      testCase "Term = Term (different arity)" $ do
        runTestEnv_ $ assertUnifyFailure (makeTerm "f" [VInt 1]) (makeTerm "f" [VInt 1, VInt 2]),
      testCase "Nested terms: f(X, g(1)) = f(2, g(Y))" $ do
        runTestEnv_ $ do
          x <- newVar
          y <- newVar
          let t1 = makeTerm "f" [x, makeTerm "g" [VInt 1]]
              t2 = makeTerm "f" [VInt 2, makeTerm "g" [y]]
          assertUnifySuccess t1 t2
          assertDerefInt x 2
          assertDerefInt y 1,
      testCase "Binding chain: X→Y→Z→42" $ do
        runTestEnv_ $ do
          x <- newVar
          y <- newVar
          z <- newVar
          assertUnifySuccess x y
          assertUnifySuccess y z
          assertUnifySuccess z (VInt 42)
          assertDerefInt x 42,
      testCase "Int = Atom (type mismatch)" $ do
        runTestEnv_ $ assertUnifyFailure (VInt 1) (VAtom "one"),
      testCase "Already-bound var: unify with same value succeeds" $ do
        runTestEnv_ $ do
          x <- newVar
          assertUnifySuccess x (VInt 1)
          assertUnifySuccess x (VInt 1)
          assertDerefInt x 1,
      testCase "Already-bound var: unify with different value fails" $ do
        runTestEnv_ $ do
          x <- newVar
          assertUnifySuccess x (VInt 1)
          assertUnifyFailure x (VInt 2)
    ]

-- ---------------------------------------------------------------------------
-- Unifiable tests: return-value agreement with unify
-- ---------------------------------------------------------------------------

-- | Run a 'unifiable'-based test without needing a Writer layer.
runUnifiableEnv :: Eff '[Unify, IOE] a -> IO a
runUnifiableEnv = runEff . runUnify

-- | Assert that 'unifiable' on two values returns the expected boolean.
assertUnifiable :: (Unify :> es, IOE :> es) => Value -> Value -> Bool -> Eff es ()
assertUnifiable a b expected = do
  r <- unifiable a b
  liftIO $ r @?= expected

unifiableTests :: TestTree
unifiableTests =
  testGroup
    "unifiable"
    [ testCase "Int = Int (same)" $ runUnifiableEnv $ assertUnifiable (VInt 1) (VInt 1) True,
      testCase "Int = Int (different)" $ runUnifiableEnv $ assertUnifiable (VInt 1) (VInt 2) False,
      testCase "Atom = Atom (same)" $ runUnifiableEnv $ assertUnifiable (VAtom "a") (VAtom "a") True,
      testCase "Atom = Atom (different)" $ runUnifiableEnv $ assertUnifiable (VAtom "a") (VAtom "b") False,
      testCase "Bool = Bool (same)" $ runUnifiableEnv $ assertUnifiable (VBool True) (VBool True) True,
      testCase "Bool = Bool (different)" $ runUnifiableEnv $ assertUnifiable (VBool True) (VBool False) False,
      testCase "Text = Text (same)" $ runUnifiableEnv $ assertUnifiable (VText "x") (VText "x") True,
      testCase "Text = Text (different)" $ runUnifiableEnv $ assertUnifiable (VText "x") (VText "y") False,
      testCase "Same unbound var" $ runUnifiableEnv $ do
        x <- newVar
        assertUnifiable x x True,
      testCase "Two distinct unbound vars" $ runUnifiableEnv $ do
        x <- newVar
        y <- newVar
        assertUnifiable x y True,
      testCase "Unbound var vs ground" $ runUnifiableEnv $ do
        x <- newVar
        assertUnifiable x (VInt 42) True,
      testCase "Ground vs unbound var" $ runUnifiableEnv $ do
        x <- newVar
        assertUnifiable (VInt 42) x True,
      testCase "Wildcard vs ground" $ runUnifiableEnv $ assertUnifiable VWildcard (VInt 7) True,
      testCase "Wildcard vs unbound var" $ runUnifiableEnv $ do
        x <- newVar
        assertUnifiable VWildcard x True,
      testCase "Wildcard vs compound" $
        runUnifiableEnv $
          assertUnifiable VWildcard (makeTerm "f" [VInt 1, VInt 2]) True,
      testCase "Compound: matching ground args" $
        runUnifiableEnv $
          assertUnifiable (makeTerm "f" [VInt 1, VInt 2]) (makeTerm "f" [VInt 1, VInt 2]) True,
      testCase "Compound: mismatched functor" $
        runUnifiableEnv $
          assertUnifiable (makeTerm "f" [VInt 1]) (makeTerm "g" [VInt 1]) False,
      testCase "Compound: mismatched arity" $
        runUnifiableEnv $
          assertUnifiable (makeTerm "f" [VInt 1]) (makeTerm "f" [VInt 1, VInt 2]) False,
      testCase "Compound with var arg: f(1, X) = f(1, 2)" $ runUnifiableEnv $ do
        x <- newVar
        assertUnifiable (makeTerm "f" [VInt 1, x]) (makeTerm "f" [VInt 1, VInt 2]) True,
      testCase "Compound nested failure: f(X, 1) = f(2, 3)" $ runUnifiableEnv $ do
        x <- newVar
        assertUnifiable (makeTerm "f" [x, VInt 1]) (makeTerm "f" [VInt 2, VInt 3]) False,
      testCase "Transitively unifiable: f(X, X) = f(1, 1)" $ runUnifiableEnv $ do
        x <- newVar
        assertUnifiable (makeTerm "f" [x, x]) (makeTerm "f" [VInt 1, VInt 1]) True,
      testCase "Transitively non-unifiable: f(X, X) = f(1, 2)" $ runUnifiableEnv $ do
        x <- newVar
        assertUnifiable (makeTerm "f" [x, x]) (makeTerm "f" [VInt 1, VInt 2]) False,
      testCase "Type mismatch: Int vs Atom" $
        runUnifiableEnv $
          assertUnifiable (VInt 1) (VAtom "a") False,
      testCase "Chained bind then unifiable ground" $ runTestEnv_ $ do
        x <- newVar
        y <- newVar
        _ <- unify x y
        r <- unifiable x (VInt 1)
        liftIO $ r @?= True
    ]

-- ---------------------------------------------------------------------------
-- Unifiable rollback tests: bindings must not leak
-- ---------------------------------------------------------------------------

-- | Assert that calling 'unifiable' on two terms returns the expected
-- boolean and leaves the given list of variables with unchanged state
-- (i.e. still unbound with the same 'VarId').
assertUnifiableNoMutation ::
  (Unify :> es, IOE :> es) => [Value] -> Value -> Value -> Bool -> Eff es ()
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
    [ testCase "Var-Var success: both stay unbound" $ runUnifiableEnv $ do
        x <- newVar
        y <- newVar
        assertUnifiableNoMutation [x, y] x y True,
      testCase "Var-NonVar success: var stays unbound" $ runUnifiableEnv $ do
        x <- newVar
        assertUnifiableNoMutation [x] x (VInt 42) True,
      testCase "NonVar-Var success (symmetric): var stays unbound" $ runUnifiableEnv $ do
        x <- newVar
        assertUnifiableNoMutation [x] (VInt 42) x True,
      testCase "Bind then fail inside compound: var rolls back" $ runUnifiableEnv $ do
        x <- newVar
        assertUnifiableNoMutation
          [x]
          (makeTerm "f" [x, VInt 1])
          (makeTerm "f" [VInt 2, VInt 3])
          False,
      testCase "Double-bind failure: f(X,X) vs f(1,2) rolls X back" $ runUnifiableEnv $ do
        x <- newVar
        assertUnifiableNoMutation
          [x]
          (makeTerm "f" [x, x])
          (makeTerm "f" [VInt 1, VInt 2])
          False,
      testCase "Success inside deeper compound: all vars stay unbound" $ runUnifiableEnv $ do
        x <- newVar
        y <- newVar
        assertUnifiableNoMutation
          [x, y]
          (makeTerm "f" [x, y])
          (makeTerm "f" [VInt 1, VInt 2])
          True,
      testCase "Failure with multiple rolled-back bindings" $ runUnifiableEnv $ do
        x <- newVar
        y <- newVar
        assertUnifiableNoMutation
          [x, y]
          (makeTerm "f" [x, y, VInt 1])
          (makeTerm "f" [VInt 1, VInt 2, VInt 9])
          False,
      testCase "Pre-bound var stays bound after failing unifiable" $ runTestEnv_ $ do
        x <- newVar
        _ <- unify x (VInt 7)
        r <- unifiable x (VInt 8)
        liftIO $ r @?= False
        -- X must still be bound to 7, not unbound.
        mid <- getVarId x
        liftIO $ mid @?= Nothing
        eq <- equal x (VInt 7)
        liftIO $ eq @?= True
    ]

-- ---------------------------------------------------------------------------
-- Equal tests
-- ---------------------------------------------------------------------------

equalTests :: TestTree
equalTests =
  testGroup
    "equal"
    [ testCase "Same unbound var" $ do
        runTestEnv_ $ do
          x <- newVar
          r <- equal x x
          liftIO $ r @?= True,
      testCase "Distinct unbound vars" $ do
        runTestEnv_ $ do
          x <- newVar
          y <- newVar
          r <- equal x y
          liftIO $ r @?= False,
      testCase "Unbound var vs ground" $ do
        runTestEnv_ $ do
          x <- newVar
          r <- equal x (VInt 1)
          liftIO $ r @?= False,
      testCase "Ground vs unbound var" $ do
        runTestEnv_ $ do
          x <- newVar
          r <- equal (VInt 1) x
          liftIO $ r @?= False,
      testCase "Same int" $ do
        r <- runTestEnv_ $ equal (VInt 42) (VInt 42)
        r @?= True,
      testCase "Different int" $ do
        r <- runTestEnv_ $ equal (VInt 1) (VInt 2)
        r @?= False,
      testCase "Same atom" $ do
        r <- runTestEnv_ $ equal (VAtom "x") (VAtom "x")
        r @?= True,
      testCase "Same term structure" $ do
        r <- runTestEnv_ $ equal (makeTerm "f" [VInt 1, VAtom "a"]) (makeTerm "f" [VInt 1, VAtom "a"])
        r @?= True,
      testCase "Different term structure" $ do
        r <- runTestEnv_ $ equal (makeTerm "f" [VInt 1]) (makeTerm "f" [VInt 2])
        r @?= False,
      testCase "After unification: var bound to int" $ do
        runTestEnv_ $ do
          x <- newVar
          _ <- unify x (VInt 5)
          r <- equal x (VInt 5)
          liftIO $ r @?= True,
      testCase "Two vars bound to same value" $ do
        runTestEnv_ $ do
          x <- newVar
          y <- newVar
          _ <- unify x (VInt 3)
          _ <- unify y (VInt 3)
          r <- equal x y
          liftIO $ r @?= True,
      testCase "Var bound to var, both equal after binding" $ do
        runTestEnv_ $ do
          x <- newVar
          y <- newVar
          _ <- unify x y
          _ <- unify y (VAtom "hello")
          r <- equal x (VAtom "hello")
          liftIO $ r @?= True
    ]

-- ---------------------------------------------------------------------------
-- Observer tests
-- ---------------------------------------------------------------------------

observerTests :: TestTree
observerTests =
  testGroup
    "observers"
    [ testCase "No observers: unify returns empty list" $ do
        (_, obs) <- runTestEnv $ do
          x <- newVar
          _ <- unify x (VInt 1)
          pure ()
        obs @?= [],
      testCase "Single observer returned on bind" $ do
        (ok, obs) <- runTestEnv $ do
          x <- newVar
          addObserver (SuspensionId 10) x
          unify x (VInt 1)
        assertBool "unify succeeds" ok
        obs @?= [SuspensionId 10],
      testCase "Multiple observers all returned" $ do
        (ok, obs) <- runTestEnv $ do
          x <- newVar
          addObserver (SuspensionId 1) x
          addObserver (SuspensionId 2) x
          addObserver (SuspensionId 3) x
          unify x (VInt 1)
        assertBool "unify succeeds" ok
        length obs @?= 3,
      testCase "Var-Var merge: observers from bound var collected" $ do
        (ok, obs) <- runTestEnv $ do
          x <- newVar
          y <- newVar
          addObserver (SuspensionId 1) x
          addObserver (SuspensionId 2) y
          unify x y
        assertBool "unify succeeds" ok
        -- Observers from x (the one that gets bound) are returned
        obs @?= [SuspensionId 1],
      testCase "addObserver on ground value is no-op" $ do
        runTestEnv_ $ do
          addObserver (SuspensionId 99) (VInt 42)
          -- No crash, no effect — just verifying it doesn't error
          pure ()
    ]

-- ---------------------------------------------------------------------------
-- Deref / path compression tests
-- ---------------------------------------------------------------------------

derefTests :: TestTree
derefTests =
  testGroup
    "deref"
    [ testCase "Unbound var derefs to itself" $ do
        runTestEnv_ $ do
          x <- newVar
          d <- deref x
          r <- equal d x
          liftIO $ r @?= True,
      testCase "Ground value derefs to itself" $ do
        d <- runTestEnv_ $ deref (VInt 99)
        case d of
          VInt 99 -> pure ()
          _ -> assertBool "expected VInt 99" False,
      testCase "Single binding: var→int" $ do
        runTestEnv_ $ do
          x <- newVar
          _ <- unify x (VInt 10)
          assertDerefInt x 10,
      testCase "Chain: var→var→var→int" $ do
        runTestEnv_ $ do
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

-- ---------------------------------------------------------------------------
-- Term operations tests
-- ---------------------------------------------------------------------------

termTests :: TestTree
termTests =
  testGroup
    "terms"
    [ testCase "makeTerm constructs VTerm" $ do
        let t = makeTerm "f" [VInt 1, VAtom "a"]
        case t of
          VTerm "f" [VInt 1, VAtom "a"] -> pure ()
          _ -> assertBool "expected VTerm f [1, a]" False,
      testCase "matchTerm: correct functor/arity" $ do
        r <- runTestEnv_ $ matchTerm (makeTerm "f" [VInt 1, VInt 2]) "f" 2
        r @?= True,
      testCase "matchTerm: wrong functor" $ do
        r <- runTestEnv_ $ matchTerm (makeTerm "f" [VInt 1]) "g" 1
        r @?= False,
      testCase "matchTerm: wrong arity" $ do
        r <- runTestEnv_ $ matchTerm (makeTerm "f" [VInt 1]) "f" 2
        r @?= False,
      testCase "matchTerm: non-term" $ do
        r <- runTestEnv_ $ matchTerm (VInt 42) "f" 0
        r @?= False,
      testCase "matchTerm through var" $ do
        runTestEnv_ $ do
          x <- newVar
          _ <- unify x (makeTerm "g" [VInt 1, VInt 2, VInt 3])
          r <- matchTerm x "g" 3
          liftIO $ r @?= True,
      testCase "getArg: correct index" $ do
        let t = makeTerm "f" [VInt 10, VAtom "b", VInt 30]
        (a0, a1, a2) <- runTestEnv_ $ do
          a0 <- getArg t 0
          a1 <- getArg t 1
          a2 <- getArg t 2
          pure (a0, a1, a2)
        case a0 of VInt 10 -> pure (); _ -> assertBool "arg 0" False
        case a1 of VAtom "b" -> pure (); _ -> assertBool "arg 1" False
        case a2 of VInt 30 -> pure (); _ -> assertBool "arg 2" False,
      testCase "getArg through var" $ do
        runTestEnv_ $ do
          x <- newVar
          _ <- unify x (makeTerm "h" [VInt 5])
          a <- getArg x 0
          liftIO $ case a of
            VInt 5 -> pure ()
            _ -> assertBool "expected VInt 5" False
    ]

-- ---------------------------------------------------------------------------
-- Wildcard tests
-- ---------------------------------------------------------------------------

wildcardTests :: TestTree
wildcardTests =
  testGroup
    "wildcard"
    [ testCase "Wildcard unifies with Int" $ do
        r <- runTestEnv_ $ unify VWildcard (VInt 42)
        r @?= True,
      testCase "Int unifies with Wildcard" $ do
        r <- runTestEnv_ $ unify (VInt 42) VWildcard
        r @?= True,
      testCase "Wildcard unifies with Wildcard" $ do
        r <- runTestEnv_ $ unify VWildcard VWildcard
        r @?= True,
      testCase "Wildcard unifies with unbound Var" $ do
        runTestEnv_ $ do
          x <- newVar
          ok <- unify VWildcard x
          liftIO $ ok @?= True,
      testCase "Wildcard does not bind Var" $ do
        runTestEnv_ $ do
          x <- newVar
          _ <- unify VWildcard x
          d <- deref x
          liftIO $ case d of
            VVar _ -> pure ()
            _ -> assertBool "var should remain unbound" False,
      testCase "Wildcard equal to Int is False" $ do
        r <- runTestEnv_ $ equal VWildcard (VInt 42)
        r @?= False,
      testCase "Int equal to Wildcard is False" $ do
        r <- runTestEnv_ $ equal (VInt 42) VWildcard
        r @?= False,
      testCase "Wildcard equal to Wildcard is False" $ do
        r <- runTestEnv_ $ equal VWildcard VWildcard
        r @?= False
    ]
