{-# LANGUAGE OverloadedStrings #-}

module YCHR.MetaTest (tests) where

import Data.IntMap.Strict qualified as IntMap
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Data.Text (Text)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertBool, assertFailure, testCase)
import YCHR.Embedded (stdlib, typeCheckerProgram)
import YCHR.Internal.Compile.Names (vmName)
import YCHR.Internal.Compile.Pipeline (CompiledProgram (..))
import YCHR.Internal.Meta (metaHostCallRegistry, valueToTerm)
import YCHR.Internal.PExpr (OpTable, OpType (..))
import YCHR.Internal.Parsed (OpDecl (..))
import YCHR.Internal.Parser (builtinOps, mergeOps)
import YCHR.Internal.Runtime.Interpreter
  ( HostCallFn (..),
    HostCallRegistry,
    baseHostCallRegistry,
  )
import YCHR.Internal.Runtime.Monad (Chr, initSessionEnv, runChr)
import YCHR.Internal.Runtime.Types (Value (..))
import YCHR.Internal.Runtime.Var (deref, equal)
import YCHR.Internal.Types (Term (..))
import YCHR.Internal.Types qualified as Types
import YCHR.Internal.VM (Name (..))
import YCHR.Run (compileModules, runProgramWithQuery)

tests :: TestTree
tests =
  testGroup
    "YCHR.Internal.Meta"
    [ readTermTests,
      vmNameRoundTripTests
    ]

hostCalls :: HostCallRegistry
hostCalls = baseHostCallRegistry <> metaHostCallRegistry

-- | A session whose operator table is the given one. The reader's table
-- is a per-session input, so two sessions may differ.
runChrWith :: OpTable -> Chr a -> IO a
runChrWith table action = do
  env <-
    initSessionEnv
      []
      []
      []
      IntMap.empty
      table
      Map.empty
      baseHostCallRegistry
      Map.empty
      Map.empty
      Map.empty
      Set.empty
  runChr action env

-- | The hand-built session every direct reader test uses: no program, so
-- the built-in operator table.
runChrBase :: Chr a -> IO a
runChrBase = runChrWith builtinOps

-- | Invoke the read_term_from_string host call directly and return the Value.
readTerm :: Text -> IO Value
readTerm = readTermWith builtinOps

-- | Invoke the read_term_from_string host call in a session carrying the
-- given operator table.
readTermWith :: OpTable -> Text -> IO Value
readTermWith table s = case Map.lookup (Name "read_term_from_string") metaHostCallRegistry of
  Nothing -> assertFailure "read_term_from_string not found in registry"
  Just (HostCallFn f) -> runChrWith table (f [VText s])

compileOrFail :: [(FilePath, Text)] -> IO CompiledProgram
compileOrFail inputs = case compileModules stdlib False inputs of
  Left err -> assertFailure $ show err
  Right (cp, _) -> pure cp

readTermTests :: TestTree
readTermTests =
  testGroup
    "read_term_from_string"
    [ testCase "integer" $ do
        v <- readTerm "42"
        case v of
          VInt 42 -> pure ()
          _ -> assertFailure "expected VInt 42",
      testCase "negative integer" $ do
        v <- readTerm "-7"
        case v of
          VInt (-7) -> pure ()
          _ -> assertFailure "expected VInt (-7)",
      testCase "atom" $ do
        v <- readTerm "hello"
        case v of
          VAtom "hello" -> pure ()
          _ -> assertFailure "expected VAtom hello",
      testCase "quoted atom" $ do
        v <- readTerm "'hello world'"
        case v of
          VAtom "hello world" -> pure ()
          _ -> assertFailure "expected VAtom 'hello world'",
      testCase "string" $ do
        v <- readTerm "\"hello\""
        case v of
          VText "hello" -> pure ()
          _ -> assertFailure "expected VText hello",
      testCase "wildcard is a fresh unbound var" $ do
        v <- readTerm "_"
        v' <- runChrBase (deref v)
        case v' of
          VVar _ -> pure ()
          _ -> assertFailure "expected unbound variable",
      testCase "each wildcard occurrence is distinct" $ do
        v <- readTerm "f(_, _)"
        eq <- runChrBase $ case v of
          VTerm "f" [a, b] -> equal a b
          _ -> pure True
        assertBool "the two _ args should be different variables" (not eq),
      testCase "compound term" $ do
        v <- readTerm "f(1, hello)"
        case v of
          VTerm "f" [VInt 1, VAtom "hello"] -> pure ()
          _ -> assertFailure "unexpected result for f(1, hello)",
      testCase "nested compound term" $ do
        v <- readTerm "f(g(1), h(2, 3))"
        case v of
          VTerm "f" [VTerm "g" [VInt 1], VTerm "h" [VInt 2, VInt 3]] -> pure ()
          _ -> assertFailure "unexpected result for f(g(1), h(2, 3))",
      testCase "variable produces a fresh unbound var" $ do
        v <- readTerm "X"
        v' <- runChrBase (deref v)
        case v' of
          VVar _ -> pure ()
          _ -> assertFailure "expected unbound variable",
      testCase "same variable name maps to same var" $ do
        v <- readTerm "f(X, X)"
        eq <- runChrBase $ case v of
          VTerm "f" [a, b] -> equal a b
          _ -> pure False
        assertBool "both X args should be the same variable" eq,
      testCase "different variable names map to different vars" $ do
        v <- readTerm "f(X, Y)"
        eq <- runChrBase $ case v of
          VTerm "f" [a, b] -> equal a b
          _ -> pure True
        assertBool "X and Y should be different variables" (not eq),
      testCase "list syntax" $ do
        v <- readTerm "[1, 2, 3]"
        case v of
          VTerm "." [VInt 1, VTerm "." [VInt 2, VTerm "." [VInt 3, VAtom "[]"]]] -> pure ()
          _ -> assertFailure "unexpected result for [1, 2, 3]",
      testCase "infix operator <=> parses as compound term" $ do
        v <- readTerm "a <=> b"
        case v of
          VTerm "<=>" [VAtom "a", VAtom "b"] -> pure ()
          _ -> assertFailure "unexpected result for a <=> b",
      testCase "infix operator = parses as compound term" $ do
        v <- readTerm "a = b"
        case v of
          VTerm "=" [VAtom "a", VAtom "b"] -> pure ()
          _ -> assertFailure "unexpected result for a = b",
      testCase "a session operator outside builtinOps parses as a compound term" $ do
        table <- case mergeOps builtinOps [OpDecl 500 Yfx "+++"] of
          Right t -> pure t
          Left name -> assertFailure ("operator conflict: " ++ show name)
        v <- readTermWith table "a +++ b"
        case v of
          VTerm "+++" [VAtom "a", VAtom "b"] -> pure ()
          _ -> assertFailure "unexpected result for a +++ b",
      -- The prelude declares `+` at 500 yfx, so a program that has the
      -- prelude can read it. A session with only builtinOps cannot.
      testCase "the prelude's + is readable once the session table has it" $ do
        table <- case mergeOps builtinOps [OpDecl 500 Yfx "+"] of
          Right t -> pure t
          Left name -> assertFailure ("operator conflict: " ++ show name)
        v <- readTermWith table "1 + 1"
        case v of
          VTerm "+" [VInt 1, VInt 1] -> pure ()
          _ -> assertFailure "unexpected result for 1 + 1",
      endToEndReadTermTest,
      endToEndPreludeOperatorTest,
      endToEndDeclaredOperatorTest
    ]

endToEndReadTermTest :: TestTree
endToEndReadTermTest =
  testCase "end-to-end: read_term_from_string in CHR query" $ do
    let src =
          ":- module(m, [check/2]).\n\
          \:- chr_constraint check/2.\n\
          \\n\
          \check(X, X) <=> true.\n"
    prog <- compileOrFail [("m.chr", src)]
    bindings <-
      runProgramWithQuery
        typeCheckerProgram
        prog
        hostCalls
        "T is host:read_term_from_string(\"f(1, hello)\"), check(T, f(1, hello))."
    case Map.lookup "T" bindings of
      Just
        ( CompoundTerm
            (Types.Unqualified "f")
            [IntTerm 1, CompoundTerm (Types.Unqualified "hello") []]
          ) -> pure ()
      other -> assertFailure $ "Expected T = f(1, hello), got: " ++ show other

-- | The user-facing case: a program that has the prelude can read a
-- string spelling a prelude operator. The reader takes the table from
-- the session, which 'toSessionInput' fills from
-- 'CompiledProgram.opTable' exactly as the goal parser does.
endToEndPreludeOperatorTest :: TestTree
endToEndPreludeOperatorTest =
  testCase "end-to-end: the prelude's operators are readable" $ do
    let src =
          ":- module(m, [check/2]).\n\
          \:- chr_constraint check/2.\n\
          \\n\
          \check(X, X) <=> true.\n"
    prog <- compileOrFail [("m.chr", src)]
    bindings <-
      runProgramWithQuery
        typeCheckerProgram
        prog
        hostCalls
        "T is host:read_term_from_string(\"1 + 1\"), check(T, quote(1 + 1))."
    case Map.lookup "T" bindings of
      Just (CompoundTerm (Types.Unqualified "+") [IntTerm 1, IntTerm 1]) -> pure ()
      other -> assertFailure $ "Expected T = 1 + 1, got: " ++ show other

-- | An operator the program itself declares -- not a prelude one -- is
-- readable too. This is what separates "the session's table" from a
-- hard-coded built-ins-plus-arithmetic table.
endToEndDeclaredOperatorTest :: TestTree
endToEndDeclaredOperatorTest =
  testCase "end-to-end: an operator the program declares is readable" $ do
    let src =
          ":- module(m, [check/2, op(500, yfx, '++')]).\n\
          \:- chr_constraint check/2.\n\
          \\n\
          \check(X, X) <=> true.\n"
    prog <- compileOrFail [("m.chr", src)]
    bindings <-
      runProgramWithQuery
        typeCheckerProgram
        prog
        hostCalls
        "T is host:read_term_from_string(\"a ++ b\"), check(T, quote(a ++ b))."
    case Map.lookup "T" bindings of
      Just
        ( CompoundTerm
            (Types.Unqualified "++")
            [ CompoundTerm (Types.Unqualified "a") [],
              CompoundTerm (Types.Unqualified "b") []
              ]
          ) -> pure ()
      other -> assertFailure $ "Expected T = a ++ b, got: " ++ show other

-- | Property: 'YCHR.Internal.Meta.valueToTerm' (run on a 'VAtom' whose payload
-- comes from 'YCHR.Internal.Compile.Names.vmName') recovers the original
-- 'Types.Name' as a qualified or unqualified 'CompoundTerm'. This
-- pins the injectivity of the mangling pair @encodeText@\/@%%u@
-- escape ↔ @decodeMangled@\/@decodeEscapes@.
vmNameRoundTripTests :: TestTree
vmNameRoundTripTests =
  testGroup
    "vmName round-trip"
    [ roundTrip "ASCII qualified" (Types.Qualified "mymodule" "foo"),
      roundTrip "non-ASCII base" (Types.Qualified "m" "naïve"),
      roundTrip "non-ASCII module" (Types.Qualified "naïve" "foo"),
      roundTrip "non-ASCII both" (Types.Qualified "café" "naïve"),
      -- Previously broken: base whose encoded form follows a non-ASCII
      -- escape with literal "u<hex>" chars, which the old "__u<HEX>__"
      -- decoder mis-split.
      roundTrip "uffï base" (Types.Qualified "mymodule" "uffï"),
      -- Previously broken: module ending in non-ASCII + literal
      -- "u<hex>". With the old encoding this collided with another
      -- (m, n) pair; the new "%%u<6 hex>" encoding is injective.
      roundTrip "fooáue module" (Types.Qualified "fooáue" "b"),
      -- Base that LOOKS like a stale "__u<HEX>__" escape but is just
      -- ASCII content past the separator.
      roundTrip "uaafoo base" (Types.Qualified "mymodule" "uaafoo"),
      -- 0-arity 'Unqualified' atoms go through 'VAtom' too.
      roundTripUnqualified "ASCII unqualified" "foo",
      roundTripUnqualified "unicode unqualified" "naïve"
    ]
  where
    roundTrip label name = testCase label $ do
      let mangled = (vmName name).unName
      t <- runChrBase (valueToTerm Map.empty (VAtom mangled))
      case t of
        CompoundTerm n [] | n == name -> pure ()
        other ->
          assertFailure $
            "Round-trip failed for "
              ++ show name
              ++ "\n  mangled = "
              ++ show mangled
              ++ "\n  got     = "
              ++ show other
    roundTripUnqualified label n = testCase label $ do
      let mangled = (vmName (Types.Unqualified n)).unName
      t <- runChrBase (valueToTerm Map.empty (VAtom mangled))
      case t of
        CompoundTerm (Types.Unqualified n') [] | n' == n -> pure ()
        other ->
          assertFailure $
            "Round-trip failed for unqualified "
              ++ show n
              ++ "\n  mangled = "
              ++ show mangled
              ++ "\n  got     = "
              ++ show other
