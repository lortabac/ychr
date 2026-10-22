{-# LANGUAGE OverloadedStrings #-}

module YCHR.CollectTest (tests) where

import Data.Map.Strict qualified as Map
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, (@?=))
import YCHR.DSL (module')
import YCHR.Internal.Collect
import YCHR.Internal.Collected qualified as C
import YCHR.Internal.Diagnostic (Diagnostic (..), noDiag)
import YCHR.Internal.PExpr (PExpr (Atom))
import YCHR.Internal.Parsed

-- | Library-import resolution: transitive imports, stdlib inclusion, and error cases.
tests :: TestTree
tests =
  testGroup
    "Collect"
    [ testCase "resolves a single library import" $
        let libs = Map.fromList [("foo", module' "foo")]
         in case resolveLibraryClosure False libs [noAnnP "foo"] of
              Right mods -> length mods @?= 1
              Left errs -> fail (show errs),
      testCase "library imports collapse into CollectedImport, name preserved" $
        let userMod_ = (module' "user") {imports = [noAnnP (LibraryImport "foo" Nothing)]}
            rewritten = rewriteImports [userMod_]
            -- The library/module distinction is erased at the type level
            -- (every import is a CollectedImport); assert the conversion
            -- preserves the source module name.
            names = [imp.node.importModule | m <- rewritten, imp <- m.imports]
         in names @?= ["foo"],
      testCase "transitive library imports resolved" $
        let libA = (module' "a") {imports = [noAnnP (LibraryImport "b" Nothing)]}
            libB = module' "b"
            libs = Map.fromList [("a", libA), ("b", libB)]
         in case resolveLibraryClosure False libs [noAnnP "a"] of
              Right mods -> length mods @?= 2
              Left errs -> fail (show errs),
      testCase "unknown library reports error" $
        resolveLibraryClosure False Map.empty [noAnnP "missing"]
          @?= Left [noDiag (AnnP (UnknownLibrary "missing") dummyLoc (Atom ""))],
      testCase "prelude not auto-included when includeStdlib is False" $
        let libs = Map.fromList [("prelude", module' "prelude")]
         in resolveLibraryClosure False libs [] @?= Right [],
      testCase "stdlib included when includeStdlib is True" $
        let libs = Map.fromList [("prelude", module' "prelude")]
         in case resolveLibraryClosure True libs [] of
              Right mods -> length mods @?= 1
              Left errs -> fail (show errs),
      testCase "circular import reports error" $
        let libA = (module' "a") {imports = [noAnnP (LibraryImport "b" Nothing)]}
            libB = (module' "b") {imports = [noAnnP (LibraryImport "a" Nothing)]}
            libs = Map.fromList [("a", libA), ("b", libB)]
         in case resolveLibraryClosure False libs [noAnnP "a"] of
              Left errs ->
                any isCircularError errs @?= True
              Right _ -> fail "expected circular import error",
      testCase "addLibraryPrelude prepends prelude to non-prelude libraries" $
        case addLibraryPrelude [module' "foo", module' "prelude"] of
          [foo, prelude] -> do
            length foo.imports @?= 1
            length prelude.imports @?= 0
          mods -> fail $ "expected 2 modules, got " ++ show (length mods)
    ]

-- | Is this a 'CircularLibraryImport'?
isCircularError :: Diagnostic CollectError -> Bool
isCircularError (Diagnostic _ (AnnP (CircularLibraryImport _) _ _) _) = True
isCircularError _ = False
