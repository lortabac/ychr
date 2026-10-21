{-# LANGUAGE OverloadedStrings #-}

-- | Tests for declaration macros (@:- macro_decls@): expansion through
-- the compile pipeline, the diagnostics it raises, and expansion in the
-- standard library. See docs/reference/macros.md.
module YCHR.DeclMacroTest (tests) where

import Control.Exception (try)
import Data.List (isInfixOf)
import Data.Map.Strict qualified as Map
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.IO qualified as TIO
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (Assertion, assertBool, assertFailure, testCase, (@?=))
import YCHR.Embedded (stdlib)
import YCHR.Internal.Collected (CollectedModule (..))
import YCHR.Internal.Compile.Pipeline
  ( CompiledProgram (..),
    Error (..),
    ModuleSplices (..),
    Warning (..),
  )
import YCHR.Internal.DeclMacro (DeclMacroError (..))
import YCHR.Internal.Diagnostic (Diagnostic (..))
import YCHR.Internal.Display (Display (..), renderSplices)
import YCHR.Internal.Parsed
  ( Ann (..),
    AnnP (..),
    ConstraintDeclBody (..),
    Declaration (..),
    ExpansionStep (..),
    FunctionEquation (..),
    Module (..),
    Rule (..),
  )
import YCHR.Internal.Parser (ParseValidationError (..))
import YCHR.Internal.Rename (RenameError (..), RenameWarning (..))
import YCHR.Internal.StdLib (StdLib (..), parseStdLib)
import YCHR.Internal.Types (QualifiedName (..))
import YCHR.Run (compileModules, prepareGoal)

-- | Compile one module, expecting success.
compileOk :: Text -> IO CompiledProgram
compileOk source = case compileModules stdlib False [("m.chr", source)] of
  Right (cp, _) -> pure cp
  Left e -> assertFailure ("compile failed:\n" ++ displayMsg e)

-- | A module's source from its lines.
src :: [Text] -> Text
src = T.unlines

-- | Compile several modules, expecting success.
compileAllOk :: [(FilePath, Text)] -> IO (CompiledProgram, [Warning])
compileAllOk inputs = case compileModules stdlib False inputs of
  Right r -> pure r
  Left e -> assertFailure ("compile failed:\n" ++ displayMsg e)

-- | The module of a given name in a compiled program.
moduleNamed :: Text -> CompiledProgram -> IO CollectedModule
moduleNamed n cp = case [m | m <- cp.allModules, m.name == n] of
  (m : _) -> pure m
  [] -> assertFailure ("module " ++ T.unpack n ++ " not found")

-- | Compile modules, expecting rename errors.
renameErrors :: [(FilePath, Text)] -> IO [RenameError]
renameErrors inputs = case compileModules stdlib False inputs of
  Left (RenameErrors es) -> pure [d.annotation.node | d <- es]
  Left e -> assertFailure ("unexpected error:\n" ++ displayMsg e)
  Right _ -> assertFailure "expected a rename error"

-- | Compile modules, expecting plain parse-validation errors.
validationErrors :: [(FilePath, Text)] -> IO [ParseValidationError]
validationErrors inputs = case compileModules stdlib False inputs of
  Left (ParseValidationErrors es) -> pure [e.node | e <- es]
  Left e -> assertFailure ("unexpected error:\n" ++ displayMsg e)
  Right _ -> assertFailure "expected a parse-validation error"

-- | Compile modules, expecting declaration-macro errors.
declErrors :: [(FilePath, Text)] -> IO [Diagnostic DeclMacroError]
declErrors inputs = case compileModules stdlib False inputs of
  Left (DeclMacroErrors es) -> pure es
  Left e -> assertFailure ("unexpected error:\n" ++ displayMsg e)
  Right _ -> assertFailure "expected a declaration-macro error"

errNodes :: [Diagnostic DeclMacroError] -> [DeclMacroError]
errNodes = map (\d -> d.annotation.node)

-- | The user module @m@ of a compiled program.
userModule :: CompiledProgram -> IO CollectedModule
userModule cp = case [m | m <- cp.allModules, m.name == "m"] of
  (m : _) -> pure m
  [] -> assertFailure "module m not found"

constraintNames :: CollectedModule -> [(Text, Int)]
constraintNames m = [(cd.name, cd.arity) | Ann (ConstraintDecl cd) _ <- m.decls]

assertContains :: String -> String -> Assertion
assertContains needle hay =
  assertBool ("expected " ++ show needle ++ " in:\n" ++ hay) (needle `isInfixOf` hay)

tests :: TestTree
tests =
  testGroup
    "DeclMacro"
    [ expansionTests,
      diagnosticTests,
      spliceTests,
      stdlibTests
    ]

expansionTests :: TestTree
expansionTests =
  testGroup
    "expansion"
    [ testCase "generated rules take the directive's place in rule order" $ do
        cp <-
          compileOk
            ( src
                [ ":- module(m).",
                  ":- chr_constraint a/0, b/0, c/0.",
                  "first @ a ==> b.",
                  ":- macro_decls gen ---> [(middle @ b ==> c)].",
                  ":- gen.",
                  "last @ c ==> a."
                ]
            )
        m <- userModule cp
        [(.node) <$> r.name | r <- m.rules]
          @?= [Just "first", Just "middle", Just "last"],
      testCase "a goal macro and a declaration macro from two modules don't clash" $ do
        let p1 =
              src
                [ ":- module(p1).",
                  ":- chr_constraint a/1.",
                  ":- macro foo(X) ---> [a(X)]."
                ]
            p2 =
              src
                [ ":- module(p2).",
                  ":- macro_decls foo(N) ---> [(:- chr_constraint N/0)]."
                ]
            user =
              src
                [ ":- module(m).",
                  ":- use_module(p1).",
                  ":- use_module(p2).",
                  ":- foo(on).",
                  "on ==> foo(1)."
                ]
        (cp, _) <- compileAllOk [("p1.chr", p1), ("p2.chr", p2), ("m.chr", user)]
        m <- userModule cp
        constraintNames m @?= [("on", 0)]
        length m.rules @?= 1,
      testCase "a user module uses a bundled library's declaration macro" $ do
        prelude <- TIO.readFile "libraries/prelude.chr"
        let libSrc =
              src
                [ ":- module(flags, [macro(flag/1)]).",
                  ":- macro_decls flag(N) ---> [(:- chr_constraint N/0)]."
                ]
        lib <- case parseStdLib [("prelude.chr", prelude), ("flags.chr", libSrc)] of
          Right l -> pure l
          Left e -> assertFailure (show e)
        let user = src [":- module(m).", ":- use_module(library(flags)).", ":- flag(on)."]
        case compileModules lib False [("m.chr", user)] of
          Right (cp, _) -> userModule cp >>= \m -> constraintNames m @?= [("on", 0)]
          Left e -> assertFailure (displayMsg e),
      testCase "counter example declares and generates a rule" $ do
        cp <-
          compileOk
            ( T.unlines
                [ ":- module(m).",
                  ":- macro_decls counter(Name) --->",
                  "    [ (:- chr_constraint Name/1, '$atom'([inc_, Name])/0),",
                  "      ('$compound'(Name, [N]), '$atom'([inc_, Name])",
                  "         <=> M is N + 1, '$compound'(Name, [M])) ].",
                  ":- counter(clicks)."
                ]
            )
        m <- userModule cp
        constraintNames m @?= [("clicks", 1), ("inc_clicks", 0)]
        length m.rules @?= 1,
      testCase "recursive nested uses splice in list order" $ do
        cp <-
          compileOk
            ( T.unlines
                [ ":- module(m).",
                  ":- unary_constraints([red, green, blue]).",
                  ":- macro_decls unary_constraints/1.",
                  "unary_constraints([]) ---> [].",
                  "unary_constraints([C|Cs]) --->",
                  "    [ (:- chr_constraint C/1), (:- unary_constraints(Cs)) ]."
                ]
            )
        m <- userModule cp
        constraintNames m @?= [("red", 1), ("green", 1), ("blue", 1)],
      testCase "a generated rule records its expansion chain" $ do
        cp <-
          compileOk
            ( T.unlines
                [ ":- module(m).",
                  ":- chr_constraint a/0, b/0.",
                  ":- macro_decls outer ---> [(:- inner)].",
                  ":- macro_decls inner ---> [(a ==> b)].",
                  ":- outer."
                ]
            )
        m <- userModule cp
        [map (.macroName) r.expansion | r <- m.rules] @?= [["inner", "outer"]],
      testCase "nullary uses, unqualified and qualified" $ do
        let provider =
              T.unlines
                [ ":- module(p, [macro(both/0)]).",
                  ":- macro_decls both ---> [(:- chr_constraint a/0, b/0)]."
                ]
            user =
              src
                [ ":- module(m).",
                  ":- use_module(p).",
                  ":- p:both.",
                  ":- local.",
                  ":- macro_decls local ---> [(:- chr_constraint c/0)]."
                ]
        (cp, _) <- compileAllOk [("p.chr", provider), ("m.chr", user)]
        m <- userModule cp
        constraintNames m @?= [("a", 0), ("b", 0), ("c", 0)],
      testCase "a header-less module defines and uses a declaration macro" $ do
        (cp, _) <-
          compileAllOk
            [ ( "hl.chr",
                ":- macro_decls flag(N) ---> [(:- chr_constraint N/0)].\n:- flag(on).\n"
              )
            ]
        m <- moduleNamed "<hl>" cp
        constraintNames m @?= [("on", 0)],
      testCase "a user module shadowing a library supplies the macros" $ do
        -- A user module named like a library replaces it, macros and all:
        -- the library's macros must not be visible through the import.
        es <-
          declErrors
            [ ("lists.chr", ":- module(lists).\n"),
              ("m.chr", ":- module(m).\n:- use_module(lists).\n:- nothing_here.\n")
            ]
        errNodes es @?= [UnknownDirective "nothing_here" 0],
      testCase "a generated equation records its chain" $ do
        cp <-
          compileOk
            ( T.unlines
                [ ":- module(m).",
                  ":- macro_decls const(F, V) --->",
                  "    [ (:- function '$compound'(F, [any]) -> int),",
                  "      ('$compound'(F, [_]) -> V) ].",
                  ":- const(one, 1)."
                ]
            )
        m <- userModule cp
        [map (.macroName) e.node.expansion | e <- m.equations] @?= [["const"]],
      testCase "the unused-parameter warning covers declaration macros" $ do
        (_, ws) <-
          compileAllOk
            [("m.chr", ":- module(m).\n:- macro_decls d(X) ---> [].\n:- d(1).\n")]
        [w.annotation.node | RenameWarnings rws <- ws, w <- rws]
          @?= [UnusedMacroParameter (QualifiedName "m" "d") "X"],
      testCase "a qualified use of an imported macro" $ do
        let provider =
              T.unlines
                [ ":- module(p, [macro(flag/1)]).",
                  ":- macro_decls flag(N) ---> [(:- chr_constraint N/0)]."
                ]
            user = T.unlines [":- module(m).", ":- use_module(p).", ":- p:flag(on)."]
        case compileModules stdlib False [("p.chr", provider), ("m.chr", user)] of
          Right (cp, _) -> userModule cp >>= \m -> constraintNames m @?= [("on", 0)]
          Left e -> assertFailure (displayMsg e),
      testCase "a declaration macro may share a name with a constraint" $ do
        cp <-
          compileOk
            ( T.unlines
                [ ":- module(m).",
                  ":- chr_constraint flag/1.",
                  ":- macro_decls flag(N) ---> [(:- chr_constraint N/0)].",
                  ":- flag(on).",
                  "on ==> flag(1)."
                ]
            )
        m <- userModule cp
        constraintNames m @?= [("flag", 1), ("on", 0)],
      testCase "fresh variables are not captured by a goal macro in the output" $ do
        -- The declaration macro's N is freshened as _decl_0_N; the goal
        -- macro's own N must not alias it.
        cp <-
          compileOk
            ( T.unlines
                [ ":- module(m).",
                  ":- chr_constraint p/1, q/2.",
                  ":- macro twice(X) ---> [q(X, N), q(N, X)].",
                  ":- macro_decls gen ---> [(p(N) ==> twice(N))].",
                  ":- gen."
                ]
            )
        let prog = show cp.desugaredProgram
        assertContains "_decl_0_N" prog
        assertContains "_macro_0_N" prog
    ]

diagnosticTests :: TestTree
diagnosticTests =
  testGroup
    "diagnostics"
    [ testCase "a built-in directive of the wrong shape is reported" $ do
        es <- validationErrors [("m.chr", ":- chr_constraint a/0.\n:- module(42).\n")]
        es @?= [MalformedDirective "module"],
      testCase "a declaration macro with a built-in directive's key" $ do
        es <-
          validationErrors
            [("m.chr", src [":- module(m).", ":- macro_decls inline(X) ---> []."])]
        es @?= [DeclMacroBuiltinDirective "inline" 1],
      testCase "a non-callable directive is malformed" $ do
        es <- declErrors [("m.chr", ":- module(m).\n:- 42.\n:- \"s\".\n")]
        errNodes es
          @?= [DeclMacroParseError MalformedTopLevel, DeclMacroParseError MalformedTopLevel],
      testCase "an import list hides a declaration macro" $ do
        let p1 =
              src
                [ ":- module(p).",
                  ":- macro_decls d ---> [].",
                  ":- macro_decls e ---> []."
                ]
            user = src [":- module(m).", ":- use_module(p, [macro(e/0)]).", ":- d.", ":- p:d."]
        es <- declErrors [("p.chr", p1), ("m.chr", user)]
        errNodes es
          @?= [UnknownDirective "d" 0, DeclMacroRenameError (NotExportedByModule "p" "d" 0)],
      testCase "a goal and a declaration macro with one key, then used" $ do
        es <-
          declErrors
            [ ( "m.chr",
                src
                  [ ":- module(m).",
                    ":- macro k(X) ---> [].",
                    ":- macro_decls k(X) ---> [].",
                    ":- k(1)."
                  ]
              )
            ]
        errNodes es @?= [DeclMacroRenameError (DuplicateMacro "k" 1)],
      testCase "a forbidden clause in a nested use carries the chain" $ do
        es <-
          declErrors
            [ ( "m.chr",
                src
                  [ ":- module(m).",
                    ":- macro_decls outer --->",
                    "    [(:- inner('$compound'(use_module, [lists])))].",
                    ":- macro_decls inner(C) ---> [(:- C)].",
                    ":- outer."
                  ]
              )
            ]
        case es of
          [d] -> do
            d.annotation.node @?= MacroDeclsForbiddenClause "use_module"
            let chain = concatMap T.unpack d.context
            assertContains "m:inner/1" chain
            assertContains "m:outer/0" chain
          other -> assertFailure (show (errNodes other)),
      testCase "a kind mismatch in a nested use is reported once" $ do
        es <-
          declErrors
            [ ( "m.chr",
                src
                  [ ":- module(m).",
                    ":- chr_constraint a/1.",
                    ":- macro g(X) ---> [a(X)].",
                    ":- macro_decls t ---> [(:- g(1)), (:- g(2))].",
                    ":- t."
                  ]
              )
            ]
        case errNodes es of
          [DeclMacroRenameError (MacroKindMismatch _ 1 _)] -> pure ()
          other -> assertFailure (show other),
      testCase "an unknown directive is an error" $ do
        es <- declErrors [("m.chr", ":- module(m).\n:- dynamic(foo/1).\n")]
        errNodes es @?= [UnknownDirective "dynamic" 1],
      testCase "a goal macro used as a directive" $ do
        es <-
          declErrors
            [("m.chr", ":- module(m).\n:- chr_constraint a/0.\n:- macro g ---> [a].\n:- g.\n")]
        case errNodes es of
          [DeclMacroRenameError (MacroKindMismatch _ 0 _)] -> pure ()
          other -> assertFailure (show other),
      testCase "two imported declaration macros are ambiguous" $ do
        let lib n =
              (T.unpack n <> ".chr", ":- module(" <> n <> ").\n:- macro_decls d ---> [].\n")
        es <-
          declErrors
            [ lib "p1",
              lib "p2",
              ("m.chr", ":- module(m).\n:- use_module(p1).\n:- use_module(p2).\n:- d.\n")
            ]
        case errNodes es of
          [DeclMacroRenameError (AmbiguousName "d" 0 _)] -> pure ()
          other -> assertFailure (show other),
      testCase "an error in a recursive use is reported once" $ do
        -- Each level splices a bad clause and recurses forever: the
        -- depth limit abandons the use, and nothing it spliced is
        -- reported on its own.
        es <-
          declErrors
            [ ( "m.chr",
                src
                  [ ":- module(m).",
                    ":- macro_decls grow(X) ---> [bad, (:- grow(s(X)))].",
                    ":- grow(z)."
                  ]
              )
            ]
        case errNodes es of
          [DeclMacroRenameError (MacroExpansionTooDeep _ 1)] -> pure ()
          other -> assertFailure (show other),
      testCase "a nested unknown directive in a branching use is reported once" $ do
        es <-
          declErrors
            [ ( "m.chr",
                T.unlines
                  [ ":- module(m).",
                    ":- macro_decls t/1.",
                    "t(z) ---> [(:- oops)].",
                    "t(s(X)) ---> [(:- t(X)), (:- t(X))].",
                    ":- t(s(s(z)))."
                  ]
              )
            ]
        errNodes es @?= [UnknownDirective "oops" 0],
      testCase "a branching recursion is too large" $ do
        es <-
          declErrors
            [ ( "m.chr",
                T.unlines
                  [ ":- module(m).",
                    ":- macro_decls t/1.",
                    "t(z) ---> [].",
                    "t(s(X)) ---> [(:- t(X)), (:- t(X))].",
                    ":- t(" <> T.replicate 30 "s(" <> "z" <> T.replicate 30 ")" <> ")."
                  ]
              )
            ]
        case errNodes es of
          [DeclMacroRenameError (MacroExpansionTooLarge _ 1)] -> pure ()
          other -> assertFailure (show other),
      testCase "a malformed primitive in a declaration macro" $ do
        es <-
          declErrors
            [ ( "m.chr",
                src
                  [ ":- module(m).",
                    ":- macro_decls d ---> [(:- chr_constraint '$atom'([])/0)].",
                    ":- d."
                  ]
              )
            ]
        case errNodes es of
          [DeclMacroRenameError (MalformedMacroPrimitive _ _)] -> pure ()
          other -> assertFailure (show other),
      testCase "qualified uses: not exported, not imported, unknown module, self" $ do
        let p1 = ("p.chr", ":- module(p, []).\n:- macro_decls hidden ---> [].\n")
            q1 = ("q.chr", ":- module(q).\n:- macro_decls d ---> [].\n")
            user =
              T.unlines
                [ ":- module(m).",
                  ":- use_module(p).",
                  ":- p:hidden.",
                  ":- q:d.",
                  ":- nowhere:d.",
                  ":- m:missing."
                ]
        es <- declErrors [p1, q1, ("m.chr", user)]
        errNodes es
          @?= [ DeclMacroRenameError (NotExportedByModule "p" "hidden" 0),
                DeclMacroRenameError (ModuleNotImported "q" "d" 0),
                DeclMacroRenameError (UnknownModule "nowhere"),
                UnknownDirective "missing" 0
              ],
      testCase "a qualified goal macro used as a directive" $ do
        es <-
          declErrors
            [ ("p.chr", ":- module(p).\n:- chr_constraint a/1.\n:- macro g(X) ---> [a(X)].\n"),
              ("m.chr", ":- module(m).\n:- use_module(p).\n:- p:g(1).\n")
            ]
        case errNodes es of
          [DeclMacroRenameError (MacroKindMismatch (QualifiedName "p" "g") 1 _)] -> pure ()
          other -> assertFailure (show other),
      testCase "a qualified declaration macro in a goal position" $ do
        es <-
          renameErrors
            [ ( "p.chr",
                src
                  [ ":- module(p).",
                    ":- macro_decls d(X) ---> [(:- chr_constraint X/0)]."
                  ]
              ),
              ( "m.chr",
                src
                  [ ":- module(m).",
                    ":- use_module(p).",
                    ":- chr_constraint r/0.",
                    "r <=> p:d(x)."
                  ]
              )
            ]
        case es of
          [MacroKindMismatch (QualifiedName "p" "d") 1 _] -> pure ()
          other -> assertFailure (show other),
      testCase "a declaration macro in a query goal" $ do
        cp <- compileOk ":- module(m).\n:- macro_decls d(X) ---> [(:- chr_constraint X/0)].\n"
        r <- try (prepareGoal cp "d(x)")
        case r of
          Left e@(RenameErrors _) -> assertContains "YCHR-20035" (displayMsg e)
          Left e -> assertFailure ("unexpected error:\n" ++ displayMsg e)
          Right _ -> assertFailure "expected a kind mismatch",
      testCase "a goal macro and a declaration macro with one key are duplicates" $ do
        es <-
          map (.annotation.node)
            <$> declErrors
              [ ( "m.chr",
                  src
                    [ ":- module(m).",
                      ":- macro k(X) ---> [].",
                      ":- macro_decls k(X) ---> []."
                    ]
                )
              ]
        es @?= [DeclMacroRenameError (DuplicateMacro "k" 1)],
      testCase "a declaration-macro body must not name unexported self names" $ do
        es <-
          renameErrors
            [ ( "m.chr",
                src
                  [ ":- module(m, [macro(d/0)]).",
                    ":- chr_constraint c/0.",
                    ":- macro_decls d ---> [(m:c ==> m:c)]."
                  ]
              )
            ]
        assertBool (show es) (any isBodyNotExported es),
      testCase "a generated name missing from the export list is not exported" $ do
        es <-
          renameErrors
            [ ( "m.chr",
                src
                  [ ":- module(m, [macro(flag/1)]).",
                    ":- macro_decls flag(N) ---> [(:- chr_constraint N/0)].",
                    ":- flag(on)."
                  ]
              ),
              ( "u.chr",
                src
                  [ ":- module(u).",
                    ":- use_module(m).",
                    ":- chr_constraint r/0.",
                    "r <=> m:on."
                  ]
              )
            ]
        assertBool (show es) (NotExportedByModule "m" "on" 0 `elem` es),
      testCase "a goal macro inside a generated rule: chain order" $ do
        es <-
          compileErr
            [ ( "m.chr",
                T.unlines
                  [ ":- module(m).",
                    ":- chr_constraint a/0.",
                    ":- macro g ---> [nope:x].",
                    ":- macro_decls gen ---> [(a ==> g)].",
                    ":- gen."
                  ]
              )
            ]
        let out = displayMsg es
            gAt = T.breakOn "m:g/0" (T.pack out)
            genAt = T.breakOn "m:gen/0" (T.pack out)
        assertBool out (T.length (fst gAt) < T.length (fst genAt)),
      testCase "two modules with one name are reported before expansion" $
        case compileModules
          stdlib
          False
          [("a.chr", ":- module(dup).\n:- oops.\n"), ("b.chr", ":- module(dup).\n")] of
          Left e@(CollectErrors _) -> assertContains "YCHR-10004" (displayMsg e)
          Left e -> assertFailure ("unexpected error:\n" ++ displayMsg e)
          Right _ -> assertFailure "expected a duplicate-module error",
      testCase "a forbidden clause in a body as written is reported at definition" $ do
        es <-
          declErrors
            [("m.chr", ":- module(m).\n:- macro_decls bad ---> [(:- use_module(lists))].\n")]
        errNodes es @?= [MacroDeclsForbiddenClause "use_module"],
      testCase "a macro clause in the output is forbidden" $ do
        es <-
          declErrors
            [("m.chr", ":- module(m).\n:- macro_decls bad ---> [(foo ---> [])].\n")]
        errNodes es @?= [MacroDeclsForbiddenClause "--->"],
      testCase "a use that matches no clause" $ do
        es <-
          declErrors
            [("m.chr", ":- module(m).\n:- macro_decls d(a) ---> [].\n:- d(b).\n")]
        case errNodes es of
          [DeclMacroRenameError (NoMatchingMacroClause _ _)] -> pure ()
          other -> assertFailure (show other),
      testCase "an expansion that never stops is too deep" $ do
        es <-
          declErrors
            [ ( "m.chr",
                ":- module(m).\n:- macro_decls grow(X) ---> [(:- grow(s(X)))].\n:- grow(z).\n"
              )
            ]
        case errNodes es of
          [DeclMacroRenameError (MacroExpansionTooDeep _ 1)] -> pure ()
          other -> assertFailure (show other),
      testCase "a malformed spliced clause carries the chain" $ do
        es <-
          declErrors
            [("m.chr", ":- module(m).\n:- macro_decls bad ---> [not_a_clause].\n:- bad.\n")]
        case es of
          [d] -> do
            d.annotation.node @?= DeclMacroParseError MalformedTopLevel
            assertContains "in the expansion of m:bad/0" (concatMap T.unpack d.context)
          other -> assertFailure (show (errNodes other)),
      testCase "a renaming error in a generated rule shows the chain" $
        case compileModules
          stdlib
          False
          [ ( "m.chr",
              T.unlines
                [ ":- module(m).",
                  ":- chr_constraint a/0.",
                  ":- macro_decls gen ---> [(a ==> nope:missing)].",
                  ":- gen."
                ]
            )
          ] of
          Left e@(RenameErrors _) ->
            assertContains "in the expansion of m:gen/0" (displayMsg e)
          Left e -> assertFailure ("unexpected error:\n" ++ displayMsg e)
          Right _ -> assertFailure "expected a rename error"
    ]

-- | Whether an error is 'MacroBodyNotExported'.
isBodyNotExported :: RenameError -> Bool
isBodyNotExported MacroBodyNotExported {} = True
isBodyNotExported _ = False

-- | Compile modules, expecting any error.
compileErr :: [(FilePath, Text)] -> IO Error
compileErr inputs = case compileModules stdlib False inputs of
  Left e -> pure e
  Right _ -> assertFailure "expected an error"

-- | @--dump-splices@: the spliced clauses collected and rendered.
spliceTests :: TestTree
spliceTests =
  testGroup
    "splices"
    [ testCase "generated clauses are collected per module" $ do
        cp <-
          compileOk
            ( src
                [ ":- module(m).",
                  ":- macro_decls flag(N) ---> [(:- chr_constraint N/0)].",
                  ":- flag(on)."
                ]
            )
        case cp.splices of
          [ ModuleSplices
              { moduleName = modName,
                file = file,
                items = items
              }
            ] -> do
              modName @?= "m"
              file @?= "m.chr"
              length items @?= 1
          ms -> assertFailure ("expected one module, got " ++ show (length ms)),
      testCase "renderSplices pins the dump format" $ do
        cp <-
          compileOk
            ( src
                [ ":- module(m).",
                  ":- macro_decls flag(N) ---> [(:- chr_constraint N/0)].",
                  ":- flag(on)."
                ]
            )
        renderSplices cp.splices
          @?= unlines
            [ "% splices for m.chr (module m)",
              "% m:flag/1 at m.chr:3:1",
              ":- chr_constraint on / 0."
            ],
      testCase "user clauses and goal macros are not dumped" $ do
        cp <-
          compileOk
            ( src
                [ ":- module(m).",
                  ":- chr_constraint a/0, b/0.",
                  ":- macro g ---> [b].",
                  "a ==> g.",
                  ":- macro_decls flag(N) ---> [(:- chr_constraint N/0)].",
                  ":- flag(on)."
                ]
            )
        renderSplices cp.splices
          @?= unlines
            [ "% splices for m.chr (module m)",
              "% m:flag/1 at m.chr:6:1",
              ":- chr_constraint on / 0."
            ],
      testCase "a nested use is grouped under the outermost use" $ do
        cp <-
          compileOk
            ( src
                [ ":- module(m).",
                  ":- macro_decls inner(C) ---> [(:- chr_constraint C/0)].",
                  ":- macro_decls outer ---> [(:- inner(a)), (:- inner(b))].",
                  ":- outer."
                ]
            )
        renderSplices cp.splices
          @?= unlines
            [ "% splices for m.chr (module m)",
              "% m:outer/0 at m.chr:4:1",
              ":- chr_constraint a / 0.",
              ":- chr_constraint b / 0."
            ],
      testCase "one block per module, separated by a blank line" $ do
        (prog, _) <-
          compileAllOk
            [ ( "p.chr",
                src
                  [ ":- module(p).",
                    ":- macro_decls d ---> [(:- chr_constraint a/0)].",
                    ":- d."
                  ]
              ),
              ( "q.chr",
                src
                  [ ":- module(q).",
                    ":- macro_decls e ---> [(:- chr_constraint b/0)].",
                    ":- e."
                  ]
              )
            ]
        renderSplices prog.splices
          @?= unlines
            [ "% splices for p.chr (module p)",
              "% p:d/0 at p.chr:3:1",
              ":- chr_constraint a / 0.",
              "",
              "% splices for q.chr (module q)",
              "% q:e/0 at q.chr:3:1",
              ":- chr_constraint b / 0."
            ],
      testCase "a generated goal-macro use is dumped as spliced" $ do
        -- The goal macro expands later, in the renamer; the dump shows
        -- the clause as it was spliced, before that.
        cp <-
          compileOk
            ( src
                [ ":- module(m).",
                  ":- chr_constraint a/0, b/0.",
                  ":- macro g ---> [b].",
                  ":- macro_decls gen ---> [(a ==> g)].",
                  ":- gen."
                ]
            )
        renderSplices cp.splices
          @?= unlines
            [ "% splices for m.chr (module m)",
              "% m:gen/0 at m.chr:5:1",
              "a ==> g."
            ],
      testCase "a use that splices nothing has no block" $ do
        cp <-
          compileOk
            ( src
                [ ":- module(m).",
                  ":- macro_decls empty ---> [].",
                  ":- empty."
                ]
            )
        renderSplices cp.splices @?= ""
    ]

stdlibTests :: TestTree
stdlibTests =
  testGroup
    "standard library"
    [ testCase "a library uses another library's declaration macro" $
        case parseStdLib
          [ ("libs/prelude.chr", ":- module(prelude, []).\n"),
            ( "libs/gen.chr",
              T.unlines
                [ ":- module(gen, [macro(flag/1)]).",
                  ":- macro_decls flag(N) ---> [(:- chr_constraint N/0)]."
                ]
            ),
            ("libs/user.chr", ":- module(user).\n:- use_module(library(gen)).\n:- flag(on).\n")
          ] of
          Left e -> assertFailure (show e)
          Right (StdLib libs) -> case Map.lookup "user" libs of
            Just m -> [cd.name | Ann (ConstraintDecl cd) _ <- m.decls] @?= ["on"]
            Nothing -> assertFailure "library user missing"
    ]
