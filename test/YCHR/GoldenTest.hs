{-# LANGUAGE OverloadedStrings #-}

module YCHR.GoldenTest (tests) where

import Control.Exception (SomeException, fromException, try)
import Control.Monad (filterM, join)
import Data.Char (isSpace)
import Data.Foldable (traverse_)
import Data.List (isInfixOf, partition, sort, sortOn)
import Data.Map.Strict (Map)
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
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
import YCHR.Internal.ProgramCheck (ProgramCheck (..), checkProgram)
import YCHR.Internal.Runtime.Search (defaultHostCallRegistry)
import YCHR.Run
  ( Error,
    PreparedGoal (..),
    Warning (..),
    compileFiles,
    prepareGoal,
    runPreparedGoal,
  )
import YCHR.Types (Term)

-- | Test directories whose @.chr@ programs or goals deliberately
-- reference bare atoms that the renamer cannot resolve — typically
-- because the test exists to verify the renamer's behaviour on
-- unexported or unknown constructors, or because the test uses bare
-- sentinel atoms as RHS of @=@ (where @quote/1@ does not strip,
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
      -- Every rule's `= …` right-hand side is an undeclared sentinel
      -- atom, so each emits YCHR-20101; the cases pin how those atoms print.
      "atom_quoting",
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
      "unifiable",
      -- The goal hands over undeclared constructors (@f@, @hello@) so
      -- the pinned @write_term_to_string@ output keeps their
      -- unqualified spelling; a declared one would print as
      -- @write_term_test:f@.
      "write_term_test"
    ]

-- | One case of a golden test directory.
data Case
  = -- | A @.goal@ / @.expected@ pair: the goal's bindings must match.
    Positive PositiveCase
  | -- | A bare @.error@: compilation or type checking must fail.
    Negative NegativeCase
  | -- | Compilation and program-level type-checking succeed, but running
    -- the goal must throw an error whose message contains every non-empty
    -- line of the @.error@ file. Encoded by colocating @<basename>.goal@
    -- and @<basename>.error@ in the same test directory.
    GoalNegative GoalNegativeCase

-- | The files of a 'Positive' case.
data PositiveCase = PositiveCase
  { name :: String,
    goalFile :: FilePath,
    expectedFile :: FilePath
  }

-- | The file of a 'Negative' case.
data NegativeCase = NegativeCase
  { name :: String,
    errorFile :: FilePath
  }

-- | The files of a 'GoalNegative' case.
data GoalNegativeCase = GoalNegativeCase
  { name :: String,
    goalFile :: FilePath,
    errorFile :: FilePath
  }

-- | The files of a test directory, by extension. The @.chr@ paths
-- include the directory; the others are bare file names.
data DirFiles = DirFiles
  { chrs :: [FilePath],
    goals :: [FilePath],
    expecteds :: [FilePath],
    errors :: [FilePath]
  }

-- | A validated golden test directory.
data TestSpec = TestSpec
  { testName :: String,
    chrFiles :: [FilePath],
    cases :: [Case]
  }

-- | One test group per directory under @test/golden@.
tests :: IO TestTree
tests = do
  let root = "test/golden"
  entries <- sort <$> listDirectory root
  dirs <- filterM (doesDirectoryExist . (root </>)) entries
  trees <- mapM (makeGoldenTest root) dirs
  pure (testGroup "Golden" trees)

-- | Build the test tree for one directory, or a failing test when the
-- directory's files do not follow the discovery rules.
makeGoldenTest :: FilePath -> String -> IO TestTree
makeGoldenTest root name = do
  let dir = root </> name
  files <- sort <$> listDirectory dir
  let dirFiles =
        DirFiles
          { chrs = [dir </> f | f <- files, takeExtension f == ".chr"],
            goals = [f | f <- files, takeExtension f == ".goal"],
            expecteds = [f | f <- files, takeExtension f == ".expected"],
            errors = [f | f <- files, takeExtension f == ".error"]
          }
  pure $ case validate dir name dirFiles of
    Left msg -> testCase name (assertFailure msg)
    Right spec -> testGroup spec.testName (map (makeCase spec) spec.cases)

-- | Check the discovery rules (see PROJECT.md, "Golden Tests") and pair
-- up the case files.
validate :: FilePath -> String -> DirFiles -> Either String TestSpec
validate dir name files
  | null files.chrs =
      Left ("No .chr files in " ++ dir)
  | null files.goals && null files.errors =
      Left ("No .goal or .error files in " ++ dir)
  | not (null files.goals) && not (null files.errors) = do
      -- Mixed-mode directory: each .goal must be paired with either a
      -- .expected (positive) or a .error (goal-negative). A bare .error
      -- (with no matching .goal) in the same directory is rejected
      -- because we'd otherwise have to disambiguate it from a regular
      -- compilation-negative case.
      let goalNames = sort (map dropExtension files.goals)
          expectedNames = map dropExtension files.expecteds
          errorNames = map dropExtension files.errors
          (positiveMatched, unmatchedAfterExpected) =
            partition (`elem` expectedNames) goalNames
          (goalNegMatched, orphanGoals) =
            partition (`elem` errorNames) unmatchedAfterExpected
          orphanExpecteds = filter (`notElem` goalNames) expectedNames
          orphanErrors = filter (`notElem` goalNames) errorNames
      case (orphanGoals, orphanExpecteds, orphanErrors) of
        ([], [], []) ->
          let pcases =
                [ positiveCase dir c
                | c <- positiveMatched
                ]
              gncases =
                [ GoalNegative
                    GoalNegativeCase
                      { name = c,
                        goalFile = dir </> c <.> "goal",
                        errorFile = dir </> c <.> "error"
                      }
                | c <- goalNegMatched
                ]
           in Right (TestSpec name files.chrs (sortCases (pcases ++ gncases)))
        (gs, es, ers) ->
          Left
            ( "Orphan files in "
                ++ dir
                ++ ":"
                ++ concatMap
                  (("\n  missing .expected or .error for " ++) . (<.> "goal"))
                  gs
                ++ concatMap (("\n  missing .goal for " ++) . (<.> "expected")) es
                ++ concatMap
                  ( ("\n  bare .error not paired with a .goal in mixed dir for " ++)
                      . (<.> "error")
                  )
                  ers
            )
  | not (null files.errors) =
      let ecases =
            [ Negative NegativeCase {name = dropExtension e, errorFile = dir </> e}
            | e <- sort files.errors
            ]
       in Right (TestSpec name files.chrs ecases)
  | otherwise = do
      let goalNames = sort (map dropExtension files.goals)
          expectedNames = sort (map dropExtension files.expecteds)
          (matched, orphanGoals) =
            partition (`elem` expectedNames) goalNames
          orphanExpecteds = filter (`notElem` goalNames) expectedNames
      case (orphanGoals, orphanExpecteds) of
        ([], []) ->
          let pcases =
                [ positiveCase dir c
                | c <- matched
                ]
           in Right (TestSpec name files.chrs pcases)
        (gs, es) ->
          Left
            ( "Orphan files in "
                ++ dir
                ++ ":"
                ++ concatMap (("\n  missing .expected for " ++) . (<.> "goal")) gs
                ++ concatMap (("\n  missing .goal for " ++) . (<.> "expected")) es
            )

-- | The positive case @c@ of directory @dir@.
positiveCase :: FilePath -> String -> Case
positiveCase dir c =
  Positive
    PositiveCase
      { name = c,
        goalFile = dir </> c <.> "goal",
        expectedFile = dir </> c <.> "expected"
      }

-- | Sort cases by name.
sortCases :: [Case] -> [Case]
sortCases = sortOn caseName
  where
    caseName (Positive c) = c.name
    caseName (Negative c) = c.name
    caseName (GoalNegative c) = c.name

-- | Turn a case into a tasty test.
makeCase :: TestSpec -> Case -> TestTree
makeCase spec c = case c of
  Positive pc -> testCase pc.name (runPositive spec pc)
  Negative nc -> testCase nc.name (runNegative spec nc)
  GoalNegative gc -> testCase gc.name (runGoalNegative spec gc)

-- | Compile and type-check the program, then read and prepare the goal
-- in @goalFile@. Warnings fail the test unless allowed. Returns the
-- action that runs the goal.
prepareCaseGoal :: TestSpec -> FilePath -> IO (IO (Map Text Term))
prepareCaseGoal spec goalFile = do
  (prog, ws) <-
    compileFiles stdlib False spec.chrFiles
      >>= either (assertFailure . show) pure
  checkWarnings spec "compile" ws
  typeCheckOrFail spec prog
  query <- TIO.readFile goalFile
  prepared <- prepareGoal prog (T.strip query)
  checkWarnings spec "goal" prepared.warnings
  pure $
    runPreparedGoal
      typeCheckerProgram
      prog
      defaultHostCallRegistry
      prepared.constraint

-- | Compile, type-check and run the goal; compare the printed bindings
-- with the @.expected@ file.
runPositive :: TestSpec -> PositiveCase -> IO ()
runPositive spec c = do
  runGoal <- prepareCaseGoal spec c.goalFile
  expected <- readFile c.expectedFile
  bindings <- runGoal
  prettyBindings bindings @?= expected

-- | Compile + program-typecheck must succeed; preparing or running the
-- goal must throw an 'Error' whose displayed message contains every
-- non-empty line of the '.error' file (each line is an independent
-- substring assertion).
-- The first line is conventionally the @YCHR-NNNNN@ code, but the code
-- alone is often too generic — @YCHR-60001@ covers every runtime error,
-- so a typo could satisfy the assertion accidentally. Subsequent lines
-- pin a phrase from the actual error text to anchor the test against
-- the intended failure path. Any other outcome (success, non-'Error'
-- exception, missing substring) fails the test.
runGoalNegative :: TestSpec -> GoalNegativeCase -> IO ()
runGoalNegative spec c = do
  expectedSubstrings <- nonEmptyLines <$> readFile c.errorFile
  outcome <- try @SomeException (join (prepareCaseGoal spec c.goalFile))
  case outcome of
    Right _ ->
      assertFailure
        ( "Expected goal to fail with "
            ++ show expectedSubstrings
            ++ " but it succeeded"
        )
    Left exc -> case fromException exc of
      Just (err :: Error) -> do
        assertAllPresent (displayMsg err) expectedSubstrings
      Nothing ->
        assertFailure
          ( "Expected an Error matching "
              ++ show expectedSubstrings
              ++ " but got: "
              ++ show exc
          )

-- | Compilation, or else type checking, must fail with a message that
-- contains every non-empty line of the @.error@ file.
runNegative :: TestSpec -> NegativeCase -> IO ()
runNegative spec c = do
  result <- compileFiles stdlib False spec.chrFiles
  expectedSubstrings <- nonEmptyLines <$> readFile c.errorFile
  case result of
    Left err -> assertAllPresent (displayMsg err) expectedSubstrings
    Right (prog, _ws) -> do
      check <- checkProgram typeCheckerProgram prog.desugaredProgram
      case check.errors of
        [] ->
          assertFailure "Expected compilation or type checking to fail, but it succeeded"
        errs -> assertAllPresent (unlines errs) expectedSubstrings

-- | The trimmed, non-empty lines of an @.error@ file.
nonEmptyLines :: String -> [String]
nonEmptyLines = filter (not . null) . map trim . lines
  where
    trim = reverse . dropWhile isSpace . reverse . dropWhile isSpace

-- | Assert that the message contains every given substring.
assertAllPresent :: String -> [String] -> IO ()
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
  check <- checkProgram typeCheckerProgram prog.desugaredProgram
  case check.errors of
    [] -> pure ()
    errs ->
      assertFailure
        ("Type errors in " ++ spec.testName ++ ":\n" ++ unlines errs)
  checkWarnings spec "typecheck" check.warnings

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
