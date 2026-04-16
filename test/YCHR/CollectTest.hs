{-# LANGUAGE OverloadedStrings #-}

module YCHR.CollectTest (tests) where

import Data.Map.Strict qualified as Map
import Data.Text (Text)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, (@?=))
import YCHR.Collect
import YCHR.Diagnostic (Diagnostic (..), noDiag)
import YCHR.PExpr (PExpr (Atom))
import YCHR.Parsed

tests :: TestTree
tests =
  testGroup
    "Collect"
    [ testCase "no seeds, no closure" $
        resolveLibraryClosure False Map.empty [] @?= Right [],
      testCase "resolves a single library import" $
        let libs = Map.fromList [("foo", libMod "foo")]
         in case resolveLibraryClosure False libs [noAnnP "foo"] of
              Right mods -> length mods @?= 1
              Left errs -> fail (show errs),
      testCase "library imports rewritten to module imports" $
        let userMod_ = userMod [noAnnP (LibraryImport "foo" Nothing)]
            rewritten = rewriteImports [userMod_]
         in all (all (isModuleImport . (.node)) . (.imports)) rewritten @?= True,
      testCase "transitive library imports resolved" $
        let libA = (libMod "a") {imports = [noAnnP (LibraryImport "b" Nothing)]}
            libB = libMod "b"
            libs = Map.fromList [("a", libA), ("b", libB)]
         in case resolveLibraryClosure False libs [noAnnP "a"] of
              Right mods -> length mods @?= 2
              Left errs -> fail (show errs),
      testCase "unknown library reports error" $
        resolveLibraryClosure False Map.empty [noAnnP "missing"]
          @?= Left [noDiag (AnnP (UnknownLibrary "missing") dummyLoc (Atom ""))],
      testCase "prelude not auto-included when includeStdlib is False" $
        let libs = Map.fromList [("prelude", libMod "prelude")]
         in resolveLibraryClosure False libs [] @?= Right [],
      testCase "stdlib included when includeStdlib is True" $
        let libs = Map.fromList [("prelude", libMod "prelude")]
         in case resolveLibraryClosure True libs [] of
              Right mods -> length mods @?= 1
              Left errs -> fail (show errs),
      testCase "circular import reports error" $
        let libA = (libMod "a") {imports = [noAnnP (LibraryImport "b" Nothing)]}
            libB = (libMod "b") {imports = [noAnnP (LibraryImport "a" Nothing)]}
            libs = Map.fromList [("a", libA), ("b", libB)]
         in case resolveLibraryClosure False libs [noAnnP "a"] of
              Left errs ->
                any isCircularError errs @?= True
              Right _ -> fail "expected circular import error",
      testCase "addLibraryPrelude prepends prelude to non-prelude libraries" $
        case addLibraryPrelude [libMod "foo", libMod "prelude"] of
          [foo, prelude] -> do
            length foo.imports @?= 1
            length prelude.imports @?= 0
          mods -> fail $ "expected 2 modules, got " ++ show (length mods)
    ]

userMod :: [AnnP Import] -> Module
userMod imps = Module "user" imps [] [] [] [] Nothing

libMod :: Text -> Module
libMod name = Module name [] [] [] [] [] Nothing

isModuleImport :: Import -> Bool
isModuleImport (ModuleImport _ _) = True
isModuleImport _ = False

isCircularError :: Diagnostic CollectError -> Bool
isCircularError (Diagnostic _ (AnnP (CircularLibraryImport _) _ _)) = True
isCircularError _ = False
