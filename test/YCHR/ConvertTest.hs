{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

module YCHR.ConvertTest (tests) where

-- 'try' comes from the shim so its type variables keep GHC's order
-- (dev-docs/MICROHS_GAPS.md, gap 7).
import Control.Exception.Shim (SomeException, try)
import Control.Monad.IO.Class (liftIO)
import Data.List (isInfixOf, sort)
import Data.Map.Strict qualified as Map
import Data.Text (Text)
import Data.Text qualified as T
import GHC.Generics (Generic)
import Hedgehog (Gen, Property, forAll, property, (===))
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertBool, assertFailure, testCase, (@?=))
import Test.Tasty.Hedgehog (testProperty)
import YCHR.Convert
import YCHR.Convert.Generic (genericFromTerm, genericToTerm)
import YCHR.DSL
  ( declaring,
    defining,
    exporting,
    hostCall,
    int,
    is,
    module',
    term,
    text,
    var,
    (.*),
    (.=.),
    (//),
    (<=>),
    (|-),
  )
import YCHR.Embedded (stdlib)
import YCHR.Internal.Parsed (Module)
import YCHR.Internal.Types (Name (..), Term (..))
import YCHR.Run (compileModules, compileParsedModules)

tests :: TestTree
tests =
  testGroup
    "YCHR.Convert"
    [ roundTripTests,
      encodingTests,
      acceptanceTests,
      errorTests,
      endToEndTests,
      canonicalizationTests,
      hostFunctionTests
    ]

-- ---------------------------------------------------------------------------
-- A generic-derived fixture type
-- ---------------------------------------------------------------------------

data Shape = Dot | Circle Int | Rect Int Int
  deriving (Eq, Show, Generic)

instance ToTerm Shape where
  toTerm = genericToTerm

instance FromTerm Shape where
  fromTerm = genericFromTerm

-- | Type-pinned 'fromTerm' at 'Shape', to keep the error-case tests short.
decodeShape :: Term -> Either ConvertError Shape
decodeShape = fromTerm

-- ---------------------------------------------------------------------------
-- Generators
-- ---------------------------------------------------------------------------

genInt :: Gen Int
genInt = Gen.int (Range.linearFrom 0 (-100000) 100000)

genInteger :: Gen Integer
genInteger = Gen.integral (Range.linearFrom 0 (-1000000000) 1000000000)

genDouble :: Gen Double
genDouble = Gen.double (Range.linearFracFrom 0 (-1000000) 1000000)

genText :: Gen Text
genText = Gen.text (Range.linear 0 12) Gen.unicode

genShape :: Gen Shape
genShape =
  Gen.choice
    [ pure Dot,
      Circle <$> genInt,
      Rect <$> genInt <*> genInt
    ]

-- ---------------------------------------------------------------------------
-- Round-trip properties
-- ---------------------------------------------------------------------------

roundTrip :: (ToTerm a, FromTerm a, Eq a, Show a) => Gen a -> Property
roundTrip gen = property $ do
  x <- forAll gen
  fromTerm (toTerm x) === Right x

roundTripTests :: TestTree
roundTripTests =
  testGroup
    "round-trip"
    [ testProperty "Int" (roundTrip genInt),
      testProperty "Integer" (roundTrip genInteger),
      testProperty "Double" (roundTrip genDouble),
      testProperty "Bool" (roundTrip Gen.bool),
      testProperty "Text" (roundTrip genText),
      testProperty "()" (roundTrip (pure ())),
      testProperty "Maybe Int" (roundTrip (Gen.maybe genInt)),
      testProperty
        "Either Int Text"
        (roundTrip (Gen.choice [Left <$> genInt, Right <$> genText]) :: Property),
      testProperty "[Int]" (roundTrip (Gen.list (Range.linear 0 10) genInt)),
      testProperty "(Int, Text)" (roundTrip ((,) <$> genInt <*> genText)),
      testProperty
        "(Int, Text, Bool)"
        (roundTrip ((,,) <$> genInt <*> genText <*> Gen.bool)),
      testProperty "Shape (generic)" (roundTrip genShape)
    ]

-- ---------------------------------------------------------------------------
-- Exact-encoding unit tests
-- ---------------------------------------------------------------------------

encodingTests :: TestTree
encodingTests =
  testGroup
    "encoding"
    [ testCase "True" $
        toTerm True @?= CompoundTerm (Unqualified "true") [],
      testCase "False" $
        toTerm False @?= CompoundTerm (Unqualified "false") [],
      testCase "Nothing" $
        toTerm (Nothing :: Maybe Int) @?= CompoundTerm (Unqualified "nothing") [],
      testCase "Just 1" $
        toTerm (Just (1 :: Int)) @?= CompoundTerm (Unqualified "just") [IntTerm 1],
      testCase "[]" $
        toTerm ([] :: [Int]) @?= CompoundTerm (Unqualified "[]") [],
      testCase "[1]" $
        toTerm [1 :: Int]
          @?= CompoundTerm (Unqualified ".") [IntTerm 1, CompoundTerm (Unqualified "[]") []],
      testCase "(1, \"a\")" $
        toTerm (1 :: Int, "a" :: Text)
          @?= CompoundTerm (Unqualified "tuple") [IntTerm 1, TextTerm "a"],
      testCase "()" $
        toTerm () @?= CompoundTerm (Unqualified "()") [],
      testCase "Dot (generic nullary)" $
        toTerm Dot @?= CompoundTerm (Unqualified "dot") [],
      testCase "Circle 3 (generic product)" $
        toTerm (Circle 3) @?= CompoundTerm (Unqualified "circle") [IntTerm 3],
      testCase "quote wraps a Term in quote/1 unchanged" $
        quote (compound "plus" [int 2, int 3])
          @?= CompoundTerm
            (Unqualified "quote")
            [CompoundTerm (Unqualified "plus") [IntTerm 2, IntTerm 3]],
      testCase "quote routes a non-Term through toTerm" $
        quote (Circle 3)
          @?= CompoundTerm
            (Unqualified "quote")
            [CompoundTerm (Unqualified "circle") [IntTerm 3]]
    ]

-- ---------------------------------------------------------------------------
-- Decode acceptance: result-shaped inputs (prelude-qualified / mangled forms)
-- ---------------------------------------------------------------------------

acceptanceTests :: TestTree
acceptanceTests =
  testGroup
    "decode acceptance"
    [ testCase "prelude:true decodes to True" $
        (fromTerm (CompoundTerm (Qualified "prelude" "true") []) :: Either ConvertError Bool)
          @?= Right True,
      testCase "prelude:[] decodes to []" $
        (fromTerm (CompoundTerm (Qualified "prelude" "[]") []) :: Either ConvertError [Int])
          @?= Right []
    ]

-- ---------------------------------------------------------------------------
-- Decode error cases
-- ---------------------------------------------------------------------------

errorTests :: TestTree
errorTests =
  testGroup
    "decode errors"
    [ testCase "unknown functor" $
        case decodeShape (CompoundTerm (Unqualified "square") [IntTerm 1]) of
          Left (UnknownFunctor names found) -> do
            found @?= Unqualified "square"
            sort names @?= ["circle", "dot", "rect"]
          other -> assertFailure ("expected UnknownFunctor, got: " <> show other),
      testCase "arity mismatch" $
        decodeShape (CompoundTerm (Unqualified "circle") [IntTerm 1, IntTerm 2])
          @?= Left (ArityMismatch (Unqualified "circle") 1 2),
      testCase "unbound value" $
        (fromTerm (VarTerm "X") :: Either ConvertError Int)
          @?= Left (UnboundValue (VarTerm "X")),
      testCase "type mismatch" $
        (fromTerm (IntTerm 1) :: Either ConvertError Text)
          @?= Left (TypeMismatch "Text" (IntTerm 1)),
      testCase "missing binding" $
        (decodeVar "missing" Map.empty :: Either ConvertError Int)
          @?= Left (MissingBinding "missing")
    ]

-- ---------------------------------------------------------------------------
-- End-to-end typed queries (compile + run + decode)
-- ---------------------------------------------------------------------------

endToEndTests :: TestTree
endToEndTests =
  testGroup
    "end-to-end"
    [ e2eScalar,
      e2eList,
      e2eRecord,
      e2eMalformedGoal,
      e2eCompiled
    ]

-- | 'runQueryCompiled' compiles a program once and drives several
-- independent queries against it, each decoded with 'FromTerm'.
e2eCompiled :: TestTree
e2eCompiled =
  testCase "runQueryCompiled: compile once, query twice" $ do
    let m =
          module' "conv_double_c"
            `exporting` ["double" // 2]
            `declaring` ["double" // 2]
            `defining` [ [term "double" [var "X", var "R"]]
                           <=> [var "R" `is` (var "X" .* int 2)]
                       ]
    cp <- case compileParsedModules stdlib True [m] of
      Left err -> assertFailure ("compile failed: " ++ show err)
      Right (cp, _warnings) -> pure cp
    r1 <- runQueryCompiled cp (term "double" [int 21, var "R"]) "R"
    r1 @?= (Right 42 :: Either ConvertError Int)
    r2 <- runQueryCompiled cp (term "double" [int 50, var "R"]) "R"
    r2 @?= (Right 100 :: Either ConvertError Int)

-- | A non-compound goal is reported as a 'ConvertError', not a crash.
e2eMalformedGoal :: TestTree
e2eMalformedGoal =
  testCase "runQuery: non-compound goal -> Left MalformedGoal" $ do
    let m = module' "conv_noop" `declaring` ["p" // 1]
    r <- runQuery stdlib [m] (int 5) "R"
    r @?= (Left (MalformedGoal (IntTerm 5)) :: Either ConvertError Int)

-- | A numeric result decoded as an 'Int'.
e2eScalar :: TestTree
e2eScalar =
  testCase "runQuery: double(21, R) -> R = 42 :: Int" $ do
    let m =
          module' "conv_double"
            `exporting` ["double" // 2]
            `declaring` ["double" // 2]
            `defining` [ [term "double" [var "X", var "R"]]
                           <=> [var "R" `is` (var "X" .* int 2)]
                       ]
    r <- runQuery stdlib [m] (term "double" [int 21, var "R"]) "R"
    r @?= (Right 42 :: Either ConvertError Int)

-- | A structural list result decoded as @[Int]@. The list term built by
-- 'toTerm' round-trips through unification and the runtime binding.
e2eList :: TestTree
e2eList =
  testCase "runQuery: pack(R) -> R = [1,2,3] :: [Int]" $ do
    let m =
          module' "conv_pack"
            `exporting` ["pack" // 1]
            `declaring` ["pack" // 1]
            `defining` [ [term "pack" [var "R"]]
                           <=> [var "R" .=. toTerm ([1, 2, 3] :: [Int])]
                       ]
    r <- runQuery stdlib [m] (term "pack" [var "R"]) "R"
    r @?= (Right [1, 2, 3] :: Either ConvertError [Int])

-- | 'runQueryWith' decoding several goal variables into a tuple.
e2eRecord :: TestTree
e2eRecord =
  testCase "runQueryWith: pair(X, Y) -> (1, 2)" $ do
    let m =
          module' "conv_pair"
            `exporting` ["pair" // 2]
            `declaring` ["pair" // 2]
            `defining` [ [term "pair" [var "X", var "Y"]]
                           <=> [var "X" .=. int 1, var "Y" .=. int 2]
                       ]
    r <-
      runQueryWith
        stdlib
        [m]
        (term "pair" [var "X", var "Y"])
        (\bs -> (,) <$> decodeVar "X" bs <*> decodeVar "Y" bs)
    r @?= (Right (1, 2) :: Either ConvertError (Int, Int))

-- ---------------------------------------------------------------------------
-- Goal-argument canonicalization
-- ---------------------------------------------------------------------------

-- | A host-built goal argument is renamed exactly like a rule-head
-- argument: a bare reference to a declared, exported data constructor is
-- canonicalized to its qualified form, which is what the compiled head
-- patterns were compiled to. Without that step the goal reaches the
-- runtime as a different functor and the rule silently never fires.
canonicalizationTests :: TestTree
canonicalizationTests =
  testGroup
    "goal-argument canonicalization"
    [ canonBareConstructor,
      canonNestedConstructor,
      canonQualifiedConstructor,
      canonListArgument
    ]

-- | The program a canonicalization case is run against. @col@ and
-- @node@ are exported so their constructors are visible to the
-- synthetic query module.
canonSource :: Text
canonSource =
  T.unlines
    [ ":- module(canon, [classify/2, describe/2, total/2,",
      "                  type(col/0), type(node/0)]).",
      ":- chr_type col ---> red ; green.",
      ":- chr_type node ---> ref(string) ; app(node, node).",
      ":- chr_constraint classify(col, any), describe(node, any),",
      "    total(list(int), int).",
      "classify(red, R) <=> R = \"warm\".",
      "classify(green, R) <=> R = \"cool\".",
      "describe(ref(N), R) <=> R = N.",
      "describe(app(_, _), R) <=> R = \"application\".",
      "total([], R) <=> R = 0.",
      "total([X | Xs], R) <=> total(Xs, Rest), R is X + Rest."
    ]

canonProgram :: IO CompiledProgram
canonProgram = case compileModules stdlib True [("canon.chr", canonSource)] of
  Left err -> assertFailure ("compile failed: " ++ show err)
  Right (cp, _warnings) -> pure cp

canonBareConstructor :: TestTree
canonBareConstructor =
  testCase "bare constructor in a goal argument matches the head pattern" $ do
    cp <- canonProgram
    r <- runQueryCompiled cp (term "classify" [term "red" [], var "R"]) "R"
    r @?= (Right "warm" :: Either ConvertError Text)

-- | The STLC case: an object-language node built by the host, whose
-- constructor carries an argument. Canonicalization has to reach the
-- compound head, not just bare atoms.
canonNestedConstructor :: TestTree
canonNestedConstructor =
  testCase "constructor with arguments in a goal argument matches" $ do
    cp <- canonProgram
    r <- runQueryCompiled cp (term "describe" [term "ref" [text "x"], var "R"]) "R"
    r @?= (Right "x" :: Either ConvertError Text)

-- | The everyday case: a list argument. 'toTerm' builds the bare @.@ \/
-- @[]@ constructors, while the head patterns were compiled against the
-- prelude's exported @list@ type, so the goal only matches once the
-- arguments are canonicalized.
canonListArgument :: TestTree
canonListArgument =
  testCase "list argument matches the prelude's list constructors" $ do
    cp <- canonProgram
    r <- runQueryCompiled cp (term "total" [toTerm ([1, 2, 3] :: [Int]), var "R"]) "R"
    r @?= (Right 6 :: Either ConvertError Int)

-- | A host that qualifies the constructor itself gets the same result;
-- canonicalization leaves an already-qualified name alone.
canonQualifiedConstructor :: TestTree
canonQualifiedConstructor =
  testCase "already-qualified constructor is left alone" $ do
    cp <- canonProgram
    r <-
      runQueryCompiled
        cp
        (term "classify" [CompoundTerm (Qualified "canon" "green") [], var "R"])
        "R"
    r @?= (Right "cool" :: Either ConvertError Text)

-- ---------------------------------------------------------------------------
-- Custom host functions
-- ---------------------------------------------------------------------------

-- | A program exercising every adapter. Compilation does not resolve
-- @host:@ names, so all custom functions are supplied at run time by the
-- registry; each rule binds @R@ to the result of one host call.
hostProgram :: Module
hostProgram =
  module' "conv_host"
    `exporting` [ "compute_add" // 2,
                  "compute_shout" // 2,
                  "compute_eff" // 2,
                  "compute_now" // 1,
                  "compute_sum" // 1,
                  "compute_add3" // 1,
                  "compute_add3m" // 1,
                  "compute_raw" // 2,
                  "compute_nested" // 1,
                  "bad_arity" // 1,
                  "bad_type" // 1,
                  "bad_unbound" // 2,
                  "ov" // 1,
                  "use_builtin" // 1,
                  "bool_result" // 2,
                  "bool_native" // 2,
                  "guard_unbound" // 1,
                  "guard_never" // 1
                ]
    `declaring` [ "compute_add" // 2,
                  "compute_shout" // 2,
                  "compute_eff" // 2,
                  "compute_now" // 1,
                  "compute_sum" // 1,
                  "compute_add3" // 1,
                  "compute_add3m" // 1,
                  "compute_raw" // 2,
                  "compute_nested" // 1,
                  "bad_arity" // 1,
                  "bad_type" // 1,
                  "bad_unbound" // 2,
                  "ov" // 1,
                  "use_builtin" // 1,
                  "bool_result" // 2,
                  "bool_native" // 2,
                  "guard_unbound" // 1,
                  "guard_never" // 1,
                  "gu_c" // 1,
                  "gu_later" // 1,
                  "gu_gather" // 1,
                  "gu_out" // 1
                ]
    `defining` [ [term "compute_add" [var "X", var "R"]]
                   <=> [var "R" `is` hostCall "my_add" [var "X", int 3]],
                 [term "compute_shout" [var "X", var "R"]]
                   <=> [var "R" `is` hostCall "shout" [var "X"]],
                 [term "compute_eff" [var "X", var "R"]]
                   <=> [var "R" `is` hostCall "effectful_add" [var "X", int 10]],
                 [term "compute_now" [var "R"]]
                   <=> [var "R" `is` hostCall "now" []],
                 [term "compute_sum" [var "R"]]
                   <=> [var "R" `is` hostCall "sum_all" [int 1, int 2, int 3, int 4]],
                 [term "compute_add3" [var "R"]]
                   <=> [var "R" `is` hostCall "add3" [int 1, int 2, int 3]],
                 [term "compute_add3m" [var "R"]]
                   <=> [var "R" `is` hostCall "add3m" [int 1, int 2, int 3]],
                 [term "compute_raw" [var "X", var "R"]]
                   <=> [var "R" `is` hostCall "raw_inc" [var "X"]],
                 [term "compute_nested" [var "R"]]
                   <=> [ var "X" .=. int 5,
                         var "R" `is` hostCall "echo" [term "wrap" [var "X", int 2]]
                       ],
                 [term "bad_arity" [var "R"]]
                   <=> [var "R" `is` hostCall "my_add" [int 1]],
                 [term "bad_type" [var "R"]]
                   <=> [var "R" `is` hostCall "my_add" [text "hi", int 3]],
                 -- Y is a head variable left unbound by the goal, so it is an
                 -- unbound logical variable at run time (not a compile-time
                 -- singleton), which the argument marshalling must reject.
                 [term "bad_unbound" [var "Y", var "R"]]
                   <=> [var "R" `is` hostCall "my_add" [var "Y", int 3]],
                 [term "ov" [var "R"]]
                   <=> [var "R" `is` hostCall "+" [int 1, int 1]],
                 [term "use_builtin" [var "R"]]
                   <=> [var "R" `is` hostCall "-" [int 10, int 3]],
                 [term "bool_result" [var "X", var "R"]]
                   <=> [var "R" `is` hostCall "is_even" [var "X"]],
                 -- Asks the runtime directly whether the Bool result is
                 -- a native boolean: an atom-shaped @true@ answers
                 -- @false@ here.
                 [term "bool_native" [var "X", var "R"]]
                   <=> [var "R" `is` hostCall "boolean" [hostCall "is_even" [var "X"]]],
                 -- Soft guard failure across the host-function boundary.
                 -- `gu_c` is stored while its argument is unbound, so
                 -- `is_even`'s Int marshalling reports UnboundValue --
                 -- an instantiation failure, which a rule guard catches.
                 [term "guard_unbound" [var "R"]]
                   <=> [ term "gu_c" [var "E"],
                         term "gu_later" [var "E"],
                         term "gu_gather" [var "R"]
                       ],
                 -- Same, but nothing ever binds the variable.
                 [term "guard_never" [var "R"]]
                   <=> [term "gu_c" [var "E"], term "gu_gather" [var "R"]],
                 [term "gu_later" [var "E"]] <=> [var "E" .=. int 4],
                 [term "gu_c" [var "N"]]
                   <=> [term "gu_out" [var "N"]]
                   |- [hostCall "is_even" [var "N"]],
                 [term "gu_gather" [var "R"], term "gu_out" [var "V"]]
                   <=> [var "R" .=. var "V"],
                 [term "gu_gather" [var "R"], term "gu_c" [var "_X"]]
                   <=> [var "R" .=. int 0]
               ]

-- | The default registry extended with one function per adapter kind.
hostRegistry :: HostCallRegistry
hostRegistry =
  withDefaultHostFunctions
    [ ("my_add", hostFn2 ((+) :: Int -> Int -> Int)),
      ("shout", hostFn1 T.toUpper),
      -- effectful (Chr / IO) binary adapter
      ("effectful_add", hostFn2M (\a b -> liftIO (pure ((a + b) :: Int)))),
      -- nullary effectful adapter
      ("now", hostFn0M (liftIO (pure (7 :: Int)))),
      -- variadic, Term-marshalled
      ("sum_all", hostFnN sumTerms),
      -- ternary, pure and effectful
      ("add3", hostFn3 (\a b c -> (a + b + c) :: Int)),
      ("add3m", hostFn3M (\a b c -> pure ((a + b + c) :: Int))),
      -- raw escape hatch: no Term marshalling, operates on Value directly
      ( "raw_inc",
        hostFnValues $ \vals -> case vals of
          [VInt n] -> pure (VInt (n + 1))
          _ -> pure (VInt 0)
      ),
      -- identity over Term, to observe deep dereferencing
      ("echo", hostFn1 (id :: Term -> Term)),
      -- Bool result: must reach the runtime as a native boolean
      ("is_even", hostFn1 (even :: Int -> Bool))
    ]
  where
    sumTerms :: [Term] -> Either ConvertError Term
    sumTerms ts = toTerm . sum <$> (traverse fromTerm ts :: Either ConvertError [Int])

runHost :: (FromTerm a) => HostCallRegistry -> Term -> IO (Either ConvertError a)
runHost reg goal = runQueryWithHostCallRegistry stdlib reg [hostProgram] goal (decodeVar "R")

-- | Assert that running @goal@ raises a runtime error whose message
-- contains @needle@.
expectHostError :: String -> Term -> IO ()
expectHostError needle goal = do
  outcome <- try @SomeException (runHost hostRegistry goal :: IO (Either ConvertError Term))
  case outcome of
    Left exc ->
      assertBool
        ("expected error containing " ++ show needle ++ ", got: " ++ show exc)
        (needle `isInfixOf` show exc)
    Right r -> assertFailure ("expected an error, got success: " ++ show r)

hostFunctionTests :: TestTree
hostFunctionTests =
  testGroup
    "host functions"
    [ testCase "hostFn2: host:my_add(2, 3) -> 5" $ do
        r <- runHost hostRegistry (term "compute_add" [int 2, var "R"])
        r @?= (Right 5 :: Either ConvertError Int),
      testCase "hostFn1: host:shout(\"hi\") -> \"HI\"" $ do
        r <- runHost hostRegistry (term "compute_shout" [text "hi", var "R"])
        r @?= (Right "HI" :: Either ConvertError Text),
      testCase "hostFn2M: effectful binary adapter runs in Chr/IO" $ do
        r <- runHost hostRegistry (term "compute_eff" [int 5, var "R"])
        r @?= (Right 15 :: Either ConvertError Int),
      testCase "hostFn0M: nullary effectful host:now() -> 7" $ do
        r <- runHost hostRegistry (term "compute_now" [var "R"])
        r @?= (Right 7 :: Either ConvertError Int),
      testCase "hostFnN: variadic host:sum_all(1,2,3,4) -> 10" $ do
        r <- runHost hostRegistry (term "compute_sum" [var "R"])
        r @?= (Right 10 :: Either ConvertError Int),
      testCase "hostFn3: host:add3(1,2,3) -> 6" $ do
        r <- runHost hostRegistry (term "compute_add3" [var "R"])
        r @?= (Right 6 :: Either ConvertError Int),
      testCase "hostFn3M: effectful ternary adapter -> 6" $ do
        r <- runHost hostRegistry (term "compute_add3m" [var "R"])
        r @?= (Right 6 :: Either ConvertError Int),
      testCase "hostFnValues: raw Value adapter host:raw_inc(41) -> 42" $ do
        r <- runHost hostRegistry (term "compute_raw" [int 41, var "R"])
        r @?= (Right 42 :: Either ConvertError Int),
      testCase "arg marshalling deep-derefs a variable nested in a compound" $ do
        r <- runHost hostRegistry (term "compute_nested" [var "R"])
        case (r :: Either ConvertError Term) of
          Right (CompoundTerm _ args) ->
            assertBool
              ("nested variable not resolved to 5: " ++ show args)
              (IntTerm 5 `elem` args)
          other -> assertFailure ("unexpected result: " ++ show other),
      testCase "arity mismatch raises a runtime error" $
        expectHostError "expected 2 argument" (term "bad_arity" [var "R"]),
      testCase "type mismatch raises a runtime error" $
        expectHostError "TypeMismatch" (term "bad_type" [var "R"]),
      testCase "unbound argument raises a runtime error" $
        expectHostError "UnboundValue" (term "bad_unbound" [var "Y", var "R"]),
      -- The same UnboundValue failure, raised in a rule guard instead of
      -- an `is`, is caught there: the rule delays rather than aborting
      -- the query, and reactivation retries it once the variable is
      -- bound. This is the host-function face of soft guard failure
      -- (docs/reference/convert.md), and the only thing that
      -- distinguishes it from a general failure -- which would still
      -- abort -- is the error's kind.
      testCase "UnboundValue in a rule guard delays, then fires on retry" $ do
        r <- runHost hostRegistry (term "guard_unbound" [var "R"])
        r @?= (Right 4 :: Either ConvertError Int),
      testCase "a guard that is never decidable delays for ever, silently" $ do
        r <- runHost hostRegistry (term "guard_never" [var "R"])
        r @?= (Right 0 :: Either ConvertError Int),
      testCase "withDefaultHostFunctions: a custom entry overrides a builtin" $ do
        let overrideReg =
              withDefaultHostFunctions
                [("+", hostFn2 (\a b -> (a * 100 + b) :: Int))]
        r <- runHost overrideReg (term "ov" [var "R"])
        r @?= (Right 101 :: Either ConvertError Int),
      testCase "hostFunctions <> base still resolves builtins" $ do
        let composed = hostFunctions [] <> baseHostCallRegistry
        r <- runHost composed (term "use_builtin" [var "R"])
        r @?= (Right 7 :: Either ConvertError Int),
      testCase "Bool result decodes as a Bool" $ do
        r <- runHost hostRegistry (term "bool_result" [int 4, var "R"])
        r @?= (Right True :: Either ConvertError Bool)
        r' <- runHost hostRegistry (term "bool_result" [int 3, var "R"])
        r' @?= (Right False :: Either ConvertError Bool),
      testCase "Bool result is a native boolean, not an atom" $ do
        -- Decoding alone would pass even if the result reached the
        -- runtime as the atom @true@; @boolean/1@ tells them apart.
        r <- runHost hostRegistry (term "bool_native" [int 4, var "R"])
        r @?= (Right True :: Either ConvertError Bool)
    ]
