{-# LANGUAGE OverloadedStrings #-}

module YCHR.GoldenTest (tests) where

-- 'try' comes from the shim so its type variables keep GHC's order
-- (dev-docs/MICROHS_GAPS.md, gap 7).
import Control.Exception.Shim (SomeException, fromException, try)
import Control.Monad (filterM)
import Data.Char (isSpace)
import Data.Foldable (traverse_)
import Data.List (isInfixOf, partition, sort, sortOn)
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text qualified as T
import Data.Text.IO qualified as TIO
import System.Directory (doesDirectoryExist, listDirectory)
import System.FilePath (dropExtension, takeExtension, (<.>), (</>))
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertBool, assertFailure, testCase, (@?=))
import YCHR.Embedded (stdlib, typeCheckerProgram)
import YCHR.Internal.Compile.Pipeline (CompiledProgram (..))
import YCHR.Internal.Display (Display (..))
import YCHR.Internal.Pretty (prettyBindings)
import YCHR.Internal.Runtime.Search (defaultHostCallRegistry)
import YCHR.Internal.TypeCheck (TypeCheckResult (..), typeCheckProgram)
import YCHR.Run
  ( Error,
    Warning (..),
    compileFiles,
    prepareGoal,
    runPreparedGoal,
  )

-- | Test directories whose @.chr@ programs or goals deliberately
-- reference bare atoms that the renamer cannot resolve — typically
-- because the test exists to verify the renamer's behaviour on
-- unexported or unknown constructors, or because the test uses bare
-- sentinel atoms as RHS of @=@ (where @quote/1@ no longer strips,
-- per the spec). Warnings emitted by these tests are part of what
-- they exercise, not a failure mode.
--
-- @nonexhaustive_color@ and @nonexhaustive_nested@ deliberately define
-- functions that do not cover every constructor of a declared algebraic
-- type, so they emit the exhaustiveness warning (YCHR-20103) on purpose.
--
-- @typecheck_goal_ctor_arity@'s failing goal applies a declared
-- constructor at the wrong arity, which the renamer reports as
-- YCHR-20102 on the way to the type error the case is about.
expectsWarnings :: Set String
expectsWarnings =
  Set.fromList
    [ "arity_overload",
      "nonexhaustive_color",
      "nonexhaustive_nested",
      "bare_atom_canonicalization",
      "bare_vs_qualified",
      "bare_vs_qualified_swapped",
      "comments_and_whitespace",
      "comparisons",
      "copy_term_sharing",
      "cross_module_function_leak",
      "false_guard",
      "function_reference_dispatch",
      "graph_test",
      "hnf_compound_head",
      "hnf_list_head",
      "hnf_literal_in_head",
      "hnf_repeated_var_across_partners",
      "hnf_repeated_var_within_head",
      "hnf_wildcard_in_head",
      "lambda_curried_adder",
      "quoted_constraint_name",
      "short_alias_collision",
      "term_variables",
      "type_export_constructor_allowlist",
      "type_export_constructor_empty",
      "type_import_constructor_narrowing",
      "type_predicates",
      "typecheck_goal_ctor_arity",
      "typecheck_polymorphic_constraint",
      "typecheck_qualified_in_head",
      -- These are permitted to emit the inaccessible-branch warning
      -- (YCHR-20104): a guard whose typing fact contradicts a known
      -- type marks a rule or equation that can never fire — dead
      -- code, not a type error. This list is an allowlist and pins
      -- nothing; the warnings themselves are asserted by
      -- @test/typecheck/test_typecheck.py@ (rendered text, per
      -- directory) and by "YCHR.TypeCheckTest" (payloads).
      "refining_user_dead_rule",
      "typecheck_evidence_bool_rule",
      "typecheck_evidence_dead_rule",
      "typecheck_list_pattern_dead",
      "typecheck_open_function_dead_equation",
      "typecheck_qualified_in_head_dead",
      "typecheck_shared_var_dead",
      "unicode_atoms_strings",
      "unifiable"
    ]

data Case
  = Positive String FilePath FilePath
  | Negative String FilePath
  | -- | Compilation and program-level type-checking succeed, but running
    -- the goal must throw an error whose displayed message contains the
    -- given error code. Encoded by colocating @<basename>.goal@ and
    -- @<basename>.error@ in the same test directory.
    GoalNegative String FilePath FilePath

data TestSpec = TestSpec
  { testName :: String,
    chrFiles :: [FilePath],
    cases :: [Case]
  }

tests :: IO TestTree
tests = do
  let root = "test/golden"
  entries <- sort <$> listDirectory root
  dirs <- filterM (doesDirectoryExist . (root </>)) entries
  trees <- mapM (makeGoldenTest root) dirs
  pure (testGroup "Golden" trees)

makeGoldenTest :: FilePath -> String -> IO TestTree
makeGoldenTest root name = do
  let dir = root </> name
  files <- sort <$> listDirectory dir
  let chrs = [dir </> f | f <- files, takeExtension f == ".chr"]
      goals = [f | f <- files, takeExtension f == ".goal"]
      expecteds = [f | f <- files, takeExtension f == ".expected"]
      errors = [f | f <- files, takeExtension f == ".error"]
  pure $ case validate dir name chrs goals expecteds errors of
    Left msg -> testCase name (assertFailure msg)
    Right spec -> testGroup spec.testName (map (makeCase spec) spec.cases)

validate ::
  FilePath ->
  String ->
  [FilePath] ->
  [FilePath] ->
  [FilePath] ->
  [FilePath] ->
  Either String TestSpec
validate dir name chrs goals expecteds errors
  | null chrs =
      Left ("No .chr files in " ++ dir)
  | null goals && null errors =
      Left ("No .goal or .error files in " ++ dir)
  | not (null goals) && not (null errors) = do
      -- Mixed-mode directory: each .goal must be paired with either a
      -- .expected (positive) or a .error (goal-negative). A bare .error
      -- (with no matching .goal) in the same directory is rejected
      -- because we'd otherwise have to disambiguate it from a regular
      -- compilation-negative case.
      let goalNames = sort (map dropExtension goals)
          expectedNames = map dropExtension expecteds
          errorNames = map dropExtension errors
          (positiveMatched, unmatchedAfterExpected) =
            partition (`elem` expectedNames) goalNames
          (goalNegMatched, orphanGoals) =
            partition (`elem` errorNames) unmatchedAfterExpected
          orphanExpecteds = filter (`notElem` goalNames) expectedNames
          orphanErrors = filter (`notElem` goalNames) errorNames
      case (orphanGoals, orphanExpecteds, orphanErrors) of
        ([], [], []) ->
          let pcases =
                [ Positive c (dir </> c <.> "goal") (dir </> c <.> "expected")
                | c <- positiveMatched
                ]
              gncases =
                [ GoalNegative c (dir </> c <.> "goal") (dir </> c <.> "error")
                | c <- goalNegMatched
                ]
           in Right (TestSpec name chrs (sortCases (pcases ++ gncases)))
        (gs, es, ers) ->
          Left
            ( "Orphan files in "
                ++ dir
                ++ ":"
                ++ concatMap (("\n  missing .expected or .error for " ++) . (<.> "goal")) gs
                ++ concatMap (("\n  missing .goal for " ++) . (<.> "expected")) es
                ++ concatMap
                  ( ("\n  bare .error not paired with a .goal in mixed dir for " ++)
                      . (<.> "error")
                  )
                  ers
            )
  | not (null errors) =
      let ecases =
            [ Negative (dropExtension e) (dir </> e)
            | e <- sort errors
            ]
       in Right (TestSpec name chrs ecases)
  | otherwise = do
      let goalNames = sort (map dropExtension goals)
          expectedNames = sort (map dropExtension expecteds)
          (matched, orphanGoals) =
            partition (`elem` expectedNames) goalNames
          orphanExpecteds = filter (`notElem` goalNames) expectedNames
      case (orphanGoals, orphanExpecteds) of
        ([], []) ->
          let pcases =
                [ Positive c (dir </> c <.> "goal") (dir </> c <.> "expected")
                | c <- matched
                ]
           in Right (TestSpec name chrs pcases)
        (gs, es) ->
          Left
            ( "Orphan files in "
                ++ dir
                ++ ":"
                ++ concatMap (("\n  missing .expected for " ++) . (<.> "goal")) gs
                ++ concatMap (("\n  missing .goal for " ++) . (<.> "expected")) es
            )

sortCases :: [Case] -> [Case]
sortCases = sortOn caseName
  where
    caseName (Positive n _ _) = n
    caseName (Negative n _) = n
    caseName (GoalNegative n _ _) = n

makeCase :: TestSpec -> Case -> TestTree
makeCase spec c = case c of
  Positive cname gf ef -> testCase cname (runPositive spec gf ef)
  Negative cname ef -> testCase cname (runNegative spec ef)
  GoalNegative cname gf ef -> testCase cname (runGoalNegative spec gf ef)

runPositive :: TestSpec -> FilePath -> FilePath -> IO ()
runPositive spec goalFile expectedFile = do
  (prog, ws) <-
    compileFiles stdlib False spec.chrFiles
      >>= either (assertFailure . show) pure
  checkWarnings spec "compile" ws
  typeCheckOrFail spec prog
  query <- TIO.readFile goalFile
  expected <- readFile expectedFile
  (constraint, goalWs) <- prepareGoal prog (T.strip query)
  checkWarnings spec "goal" goalWs
  bindings <-
    runPreparedGoal
      typeCheckerProgram
      prog
      defaultHostCallRegistry
      constraint
  prettyBindings bindings @?= expected

-- | Compile + program-typecheck must succeed; running the goal must throw
-- an 'Error' whose displayed message contains every non-empty line of
-- the '.error' file (each line is an independent substring assertion).
-- The first line is conventionally the @YCHR-NNNNN@ code, but the code
-- alone is often too generic — @YCHR-60001@ covers every runtime error,
-- so a typo could satisfy the assertion accidentally. Subsequent lines
-- pin a phrase from the actual error text to anchor the test against
-- the intended failure path. Any other outcome (success, non-'Error'
-- exception, missing substring) fails the test.
runGoalNegative :: TestSpec -> FilePath -> FilePath -> IO ()
runGoalNegative spec goalFile errorFile = do
  (prog, ws) <-
    compileFiles stdlib False spec.chrFiles
      >>= either (assertFailure . show) pure
  checkWarnings spec "compile" ws
  typeCheckOrFail spec prog
  query <- TIO.readFile goalFile
  expectedSubstrings <- nonEmptyLines <$> readFile errorFile
  (constraint, goalWs) <- prepareGoal prog (T.strip query)
  checkWarnings spec "goal" goalWs
  outcome <-
    try @SomeException $
      runPreparedGoal
        typeCheckerProgram
        prog
        defaultHostCallRegistry
        constraint
  case outcome of
    Right _ ->
      assertFailure
        ( "Expected goal to fail with "
            ++ show expectedSubstrings
            ++ " but it succeeded"
        )
    Left exc -> case fromException exc of
      Just (err :: Error) -> do
        let msg = displayMsg err
        traverse_
          ( \sub ->
              assertBool
                ("Expected substring " ++ show sub ++ " in:\n" ++ msg)
                (sub `isInfixOf` msg)
          )
          expectedSubstrings
      Nothing ->
        assertFailure
          ( "Expected an Error matching "
              ++ show expectedSubstrings
              ++ " but got: "
              ++ show exc
          )
  where
    trim = reverse . dropWhile isSpace . reverse . dropWhile isSpace
    nonEmptyLines = filter (not . null) . map trim . lines

runNegative :: TestSpec -> FilePath -> IO ()
runNegative spec errorFile = do
  result <- compileFiles stdlib False spec.chrFiles
  expectedSubstrings <- nonEmptyLines <$> readFile errorFile
  case result of
    Left err -> assertAllPresent (displayMsg err) expectedSubstrings
    Right (prog, _ws) -> do
      typeResult <- typeCheckProgram typeCheckerProgram prog.desugaredProgram
      case typeResult.errors of
        [] -> assertFailure "Expected compilation or type checking to fail, but it succeeded"
        errs -> assertAllPresent (unlines (map displayMsg errs)) expectedSubstrings
  where
    trim = reverse . dropWhile isSpace . reverse . dropWhile isSpace
    nonEmptyLines = filter (not . null) . map trim . lines
    assertAllPresent msg =
      traverse_
        ( \sub ->
            assertBool
              ("Expected substring " ++ show sub ++ " in:\n" ++ msg)
              (sub `isInfixOf` msg)
        )

-- | Type-check a positive test's program: any type error fails the
-- test, and type-check warnings go through the same allowlist as
-- compile-time warnings.
typeCheckOrFail :: TestSpec -> CompiledProgram -> IO ()
typeCheckOrFail spec prog = do
  result <- typeCheckProgram typeCheckerProgram prog.desugaredProgram
  case result.errors of
    [] -> pure ()
    errs ->
      assertFailure
        ("Type errors in " ++ spec.testName ++ ":\n" ++ unlines (map displayMsg errs))
  checkWarnings
    spec
    "typecheck"
    [TypeCheckWarnings result.warnings | not (null result.warnings)]

-- | Assert no warnings unless the test is on the allowlist. The
-- @phase@ label distinguishes compile-time warnings from goal-time
-- ones in the failure message.
checkWarnings :: TestSpec -> String -> [Warning] -> IO ()
checkWarnings spec phase ws
  | Set.member spec.testName expectsWarnings = pure ()
  | null ws = pure ()
  | otherwise =
      assertFailure
        ( spec.testName
            ++ ": "
            ++ phase
            ++ ": unexpected warnings\n"
            ++ unlines (map displayMsg ws)
        )
