{-# LANGUAGE OverloadedStrings #-}

module YCHR.CollectTest (tests) where

import Data.Map.Strict qualified as Map
import Data.Text (Text)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, (@?=))
import YCHR.Collect
import YCHR.PExpr (PExpr (Atom))
import YCHR.Parsed

tests :: TestTree
tests =
  testGroup
    "Collect"
    [ testCase "no library imports passes through" $
        collectLibraries False Map.empty [userMod []] @?= Right [userMod []],
      testCase "resolves a single library import" $
        let libs = Map.fromList [("foo", libMod "foo")]
            user = userMod [noAnnP (LibraryImport "foo")]
         in case collectLibraries False libs [user] of
              Right mods -> length mods @?= 2
              Left errs -> fail (show errs),
      testCase "library imports rewritten to module imports" $
        let libs = Map.fromList [("foo", libMod "foo")]
            user = userMod [noAnnP (LibraryImport "foo")]
         in case collectLibraries False libs [user] of
              Right mods ->
                all (all (isModuleImport . (.node)) . (.imports)) mods @?= True
              Left errs -> fail (show errs),
      testCase "transitive library imports resolved" $
        let libA = (libMod "a") {imports = [noAnnP (LibraryImport "b")]}
            libB = libMod "b"
            libs = Map.fromList [("a", libA), ("b", libB)]
            user = userMod [noAnnP (LibraryImport "a")]
         in case collectLibraries False libs [user] of
              Right mods -> length mods @?= 3
              Left errs -> fail (show errs),
      testCase "unknown library reports error" $
        collectLibraries False Map.empty [userMod [noAnnP (LibraryImport "missing")]]
          @?= Left [AnnP (UnknownLibrary "missing") dummyLoc (Atom "")],
      testCase "builtins not auto-included when includeStdlib is False" $
        let libs = Map.fromList [("builtins", libMod "builtins")]
            user = userMod []
         in collectLibraries False libs [user] @?= Right [user],
      testCase "builtins included when includeStdlib is True" $
        let libs = Map.fromList [("builtins", libMod "builtins")]
            user = userMod []
         in case collectLibraries True libs [user] of
              Right mods -> length mods @?= 2
              Left errs -> fail (show errs),
      testCase "circular import reports error" $
        let libA = (libMod "a") {imports = [noAnnP (LibraryImport "b")]}
            libB = (libMod "b") {imports = [noAnnP (LibraryImport "a")]}
            libs = Map.fromList [("a", libA), ("b", libB)]
            user = userMod [noAnnP (LibraryImport "a")]
         in case collectLibraries False libs [user] of
              Left errs ->
                any isCircularError errs @?= True
              Right _ -> fail "expected circular import error"
    ]

userMod :: [AnnP Import] -> Module
userMod imps = Module "user" imps [] [] [] [] Nothing

libMod :: Text -> Module
libMod name = Module name [] [] [] [] [] Nothing

isModuleImport :: Import -> Bool
isModuleImport (ModuleImport _) = True
isModuleImport _ = False

isCircularError :: AnnP CollectError -> Bool
isCircularError (AnnP (CircularLibraryImport _) _ _) = True
isCircularError _ = False
