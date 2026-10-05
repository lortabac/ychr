{-# LANGUAGE OverloadedStrings #-}

-- |
-- Module      : YCHR.GenerateTest
-- Description : The resource code generator's emitter.
--
-- Covers the three layers of the @make resources@ step
-- (@dev-docs\/MICROHS_PERFORMANCE.md@, option B): 'renderCode' on each
-- form of 'Code', 'toCode' for the representative leaf and container
-- types, and 'hoist' — the pass that splits the generated modules into
-- many small bindings so MicroHs can compile them.
--
-- The last group is an end-to-end smoke test: it emits both modules from
-- the compile-time-embedded resources and checks the shape of the
-- result. What it cannot check here is that MicroHs compiles the output;
-- that is what @make resources@ followed by @mcabal build@ verifies.
module YCHR.GenerateTest (tests) where

import Control.Exception (ErrorCall, evaluate, try)
import Data.Char (isDigit)
import Data.IntMap.Strict qualified as IntMap
import Data.IntSet qualified as IntSet
import Data.List (isInfixOf, isPrefixOf)
import Data.List.NonEmpty (NonEmpty ((:|)))
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as T
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (Assertion, assertBool, assertFailure, testCase, (@?=))
import YCHR.Embedded qualified as Embedded
import YCHR.Embedded.Generate.Code
import YCHR.Embedded.Generate.Emit
import YCHR.Embedded.Generate.Instances ()
import YCHR.Embedded.Generate.ToCode (toCode)
import YCHR.Internal.Loc (SourceLoc (..))
import YCHR.Internal.PExpr (PExpr (..))
import YCHR.Internal.StdLib (StdLib (..))

tests :: TestTree
tests =
  testGroup
    "YCHR.Embedded.Generate"
    [ testGroup
        "renderCode"
        [ testCase "integers, including negative ones" $ do
            renderCode (CInt 42) @?= "42"
            renderCode (CInt (-7)) @?= "-7",
          testCase "doubles are plain decimal literals, not GHC's 3.5##" $
            renderCode (CDouble 3.5) @?= "3.5",
          testCase "a non-finite double is rejected, not rendered" $ do
            result <-
              try (evaluate (length (renderCode (CDouble (1 / 0))))) ::
                IO (Either ErrorCall Int)
            case result of
              Left _ -> pure ()
              Right _ -> assertFailure "expected a non-finite Double to be rejected",
          testCase "strings and characters are escaped by show" $ do
            renderCode (CString "a\"b\n") @?= show ("a\"b\n" :: String)
            renderCode (CChar 'x') @?= "'x'",
          testCase "arguments are parenthesised only where needed" $ do
            renderCode (CApp (CName "f") [CName "x"]) @?= "f x"
            renderCode (CApp (CName "f") [CInt (-1)]) @?= "f (-1)"
            renderCode (CApp (CName "f") [CApp (CName "g") [CInt 1]]) @?= "f (g 1)"
            renderCode (CApp (CName "f") [CList [CInt 1, CInt 2]]) @?= "f [1, 2]",
          testCase "lists, tuples and explicit parentheses" $ do
            renderCode (CList [CInt 1, CInt 2]) @?= "[1, 2]"
            renderCode (CTuple [CInt 1, CName "True"]) @?= "(1, True)"
            renderCode (CParens (CName "++")) @?= "(++)"
        ],
      testGroup
        "toCode"
        [ testCase "scalars" $ do
            toCode (42 :: Int) @?= CInt 42
            toCode (42 :: Integer) @?= CInt 42
            toCode True @?= CName "True"
            toCode (3.5 :: Double) @?= CDouble 3.5
            toCode 'x' @?= CChar 'x',
          testCase "String and Text are one string literal" $ do
            toCode ("x" :: String) @?= CString "x"
            toCode ("x" :: Text) @?= CString "x",
          testCase "Maybe and NonEmpty" $ do
            toCode (Just (1 :: Int)) @?= CApp (CName "Just") [CInt 1]
            toCode (Nothing :: Maybe Int) @?= CName "Nothing"
            toCode (1 :| [2 :: Int]) @?= CApp (CName "NE.fromList") [CList [CInt 1, CInt 2]],
          testCase "containers rebuild through fromList" $ do
            toCode (Map.fromList [("a" :: Text, 1 :: Int)])
              @?= CApp (CName "Map.fromList") [CList [CTuple [CString "a", CInt 1]]]
            toCode (Set.fromList [1 :: Int])
              @?= CApp (CName "Set.fromList") [CList [CInt 1]]
            toCode (IntMap.fromList [(1 :: Int, True)])
              @?= CApp (CName "IntMap.fromList") [CList [CTuple [CInt 1, CName "True"]]]
            toCode (IntSet.fromList [1 :: Int])
              @?= CApp (CName "IntSet.fromList") [CList [CInt 1]],
          testCase "generic instances qualify constructors with an alias" $ do
            toCode (SourceLoc "f" 1 2)
              @?= CApp (CName "Loc.SourceLoc") [CString "f", CInt 1, CInt 2]
            toCode (Atom "x" :: PExpr)
              @?= CApp (CName "PExpr.Atom") [CString "x"]
        ],
      testGroup
        "hoist"
        [ testCase "splits a list longer than the chunk size" $ do
            let (body, bindings) =
                  hoist
                    (EmitOptions {chunkSize = 2, maxBindingBytes = 1000000})
                    (CList [CInt 1, CInt 2, CInt 3, CInt 4, CInt 5])
            length bindings @?= 3
            renderCode body @?= "concat [generated_0, generated_1, generated_2]",
          testCase "lifts an oversized expression to its own binding" $ do
            let (body, bindings) =
                  hoist
                    (EmitOptions {chunkSize = 100, maxBindingBytes = 5})
                    (CApp (CName "f") [CString "abcdef"])
            length bindings @?= 1
            body @?= CName "generated_0",
          testCase "leaves an empty list in place" $ do
            let (body, bindings) =
                  hoist defaultEmitOptions (CList [])
            length bindings @?= 0
            body @?= CList []
        ],
      testGroup
        "emitted modules"
        [ testCase "the standard library module names every library" $ do
            let StdLib modules = Embedded.stdlib
                emitted = emitStdLib defaultEmitOptions Embedded.stdlib
            emitted.modulePath @?= "YCHR/Embedded/Generated/StdLib.hs"
            assertContains
              (emitted.moduleSource)
              "module YCHR.Embedded.Generated.StdLib (stdlib) where"
            assertContains (emitted.moduleSource) "stdlib :: StdLib"
            mapM_
              ( \name ->
                  assertContains
                    (emitted.moduleSource)
                    (renderCode (CString (T.unpack name)))
              )
              (Map.keys modules)
            assertBool "the module is substantial" (length (emitted.moduleSource) > 100000),
          testCase "the type-checker module rebuilds through mkSessionInput" $ do
            let emitted = emitTypeChecker defaultEmitOptions Embedded.typeCheckerProgram
            emitted.modulePath @?= "YCHR/Embedded/Generated/TypeCheck.hs"
            assertContains
              (emitted.moduleSource)
              "module YCHR.Embedded.Generated.TypeCheck (typeCheckerProgram) where"
            assertContains (emitted.moduleSource) "typeCheckerProgram :: SessionInput"
            assertContains (emitted.moduleSource) "Session.mkSessionInput"
            assertContains (emitted.moduleSource) "VM.Program"
            assertBool "the module is substantial" (length (emitted.moduleSource) > 100000)
        ],
      testGroup
        "hoisted bindings"
        [ -- A dangling reference is the one way 'hoist' could emit a
          -- module that does not compile, and the MicroHs build that
          -- would otherwise catch it is not part of CI.
          testCase "every generated_ reference has a definition" $ do
            mapM_ checkDangling emittedModules,
          -- The budget is what keeps a binding small enough for MicroHs
          -- to compile; 'hoist' documents the one node shape (a
          -- literal-only application) that may exceed it.
          testCase "every binding body fits the budget" $ do
            let budget = defaultEmitOptions.maxBindingBytes
            mapM_ (checkBudget budget) emittedModules
        ]
    ]

emittedModules :: [GeneratedModule]
emittedModules =
  [ emitStdLib defaultEmitOptions Embedded.stdlib,
    emitTypeChecker defaultEmitOptions Embedded.typeCheckerProgram
  ]

checkBudget :: Int -> GeneratedModule -> Assertion
checkBudget budget emitted =
  assertBool
    ( "binding bodies over the "
        ++ show budget
        ++ "-character budget: "
        ++ show (take 5 oversized)
        ++ " in "
        ++ emitted.modulePath
    )
    (null oversized)
  where
    oversized = filter (> budget) (bindingBodyLengths emitted.moduleSource)

-- | The rendered length of every top-level binding body, which
-- 'YCHR.Embedded.Generate.Emit' writes as one line indented by two
-- spaces.
bindingBodyLengths :: String -> [Int]
bindingBodyLengths source =
  [length line - 2 | line <- lines source, "  " `isPrefixOf` line]

checkDangling :: GeneratedModule -> Assertion
checkDangling emitted = do
  let definitions = definedNames emitted.moduleSource
      references = generatedNamesIn emitted.moduleSource
      dangling = filter (`notElem` definitions) references
  assertBool
    ("referenced but never defined: " ++ show (take 5 dangling))
    (null dangling)
  assertBool "the module defines hoisted bindings" (not (null definitions))

-- | The @generated_N@ names a module defines at the top level.
definedNames :: String -> [String]
definedNames source =
  [ name
  | line <- lines source,
    let name = takeWhile (/= ' ') line,
    isGeneratedName name,
    drop (length name) line == " ="
  ]

-- | Every @generated_N@ occurrence in the source, definition lines
-- included.
generatedNamesIn :: String -> [String]
generatedNamesIn source
  | null source = []
  | "generated_" `isPrefixOf` source =
      let (digits, rest) = span isDigit (drop (length ("generated_" :: String)) source)
       in if null digits
            then generatedNamesIn (drop 1 source)
            else ("generated_" ++ digits) : generatedNamesIn rest
  | otherwise = generatedNamesIn (drop 1 source)

isGeneratedName :: String -> Bool
isGeneratedName name =
  "generated_" `isPrefixOf` name
    && let digits = drop (length ("generated_" :: String)) name
        in not (null digits) && all isDigit digits

assertContains :: String -> String -> IO ()
assertContains haystack needle =
  assertBool
    ("expected the generated module to contain: " ++ take 80 needle)
    (needle `isInfixOf` haystack)
