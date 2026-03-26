{-# LANGUAGE OverloadedStrings #-}

module YCHR.CollectTest (tests) where

import Data.Map.Strict qualified as Map
import Data.Text (Text)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, (@?=))
import YCHR.Collect
import YCHR.Parsed

tests :: TestTree
tests =
  testGroup
    "Collect"
    [ testCase "no library imports passes through" $
        collectLibraries Map.empty [userMod []] @?= Right [userMod []],
      testCase "resolves a single library import" $
        let libs = Map.fromList [("foo", libMod "foo")]
            user = userMod [LibraryImport "foo"]
         in case collectLibraries libs [user] of
              Right mods -> length mods @?= 2
              Left errs -> fail (show errs),
      testCase "library imports rewritten to module imports" $
        let libs = Map.fromList [("foo", libMod "foo")]
            user = userMod [LibraryImport "foo"]
         in case collectLibraries libs [user] of
              Right mods ->
                all (all isModuleImport . modImports) mods @?= True
              Left errs -> fail (show errs),
      testCase "transitive library imports resolved" $
        let libA = (libMod "a") {modImports = [LibraryImport "b"]}
            libB = libMod "b"
            libs = Map.fromList [("a", libA), ("b", libB)]
            user = userMod [LibraryImport "a"]
         in case collectLibraries libs [user] of
              Right mods -> length mods @?= 3
              Left errs -> fail (show errs),
      testCase "unknown library reports error" $
        collectLibraries Map.empty [userMod [LibraryImport "missing"]]
          @?= Left [UnknownLibrary "missing"],
      testCase "builtins auto-included when present in stdlib" $
        let libs = Map.fromList [("builtins", libMod "builtins")]
            user = userMod []
         in case collectLibraries libs [user] of
              Right mods -> length mods @?= 2
              Left errs -> fail (show errs),
      testCase "builtins not included when absent from stdlib" $
        collectLibraries Map.empty [userMod []] @?= Right [userMod []],
      testCase "circular import reports error" $
        let libA = (libMod "a") {modImports = [LibraryImport "b"]}
            libB = (libMod "b") {modImports = [LibraryImport "a"]}
            libs = Map.fromList [("a", libA), ("b", libB)]
            user = userMod [LibraryImport "a"]
         in case collectLibraries libs [user] of
              Left errs ->
                any isCircularError errs @?= True
              Right _ -> fail "expected circular import error"
    ]

userMod :: [Import] -> Module
userMod imps = Module "user" imps [] [] Nothing

libMod :: Text -> Module
libMod name = Module name [] [] [] Nothing

isModuleImport :: Import -> Bool
isModuleImport (ModuleImport _) = True
isModuleImport _ = False

isCircularError :: CollectError -> Bool
isCircularError (CircularLibraryImport _) = True
isCircularError _ = False
