{-# LANGUAGE OverloadedStrings #-}

module YCHR.DesugarTest (tests) where

import Data.List.NonEmpty qualified as NE
import Data.Map.Strict qualified as Map
import Data.Text (Text)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (assertFailure, testCase, (@?=))
import YCHR.DSL
import YCHR.Internal.Collect (rewriteImports)
import YCHR.Internal.Desugar
  ( DesugarError (..),
    desugarProgram,
    extractSymbolTable,
    liftAllLambdas,
  )
import YCHR.Internal.Desugared qualified as D
import YCHR.Internal.Diagnostic (noDiag)
import YCHR.Internal.PExpr (PExpr (Atom))
import YCHR.Internal.Parsed
import YCHR.Internal.Resolve (ResolveError (..), resolveProgram)
import YCHR.Internal.Resolved qualified as R
import YCHR.Internal.Types
  ( ConstraintType (..),
    Identifier (..),
    lookupSymbol,
    mkSymbolTable,
    symbolTableSize,
  )

getNode :: AnnP a -> a
getNode (AnnP n _ _) = n

-- | Desugaring: head flattening, HNF, goal and guard classification, and lambda lifting.
tests :: TestTree
tests =
  testGroup
    "Desugar"
    [ headTests,
      hnfTests,
      guardTests,
      bodyTests,
      errorTests,
      flatteningTests,
      ruleNameTests,
      symbolTableTests,
      lambdaLiftTests,
      aggregateTests
    ]

resolve :: [Module] -> IO R.Program
resolve mods = case resolveProgram (rewriteImports mods) of
  Right p -> return p
  Left errs -> assertFailure $ "unexpected resolve errors: " ++ show errs

desugar :: [Module] -> IO D.Program
desugar mods = do
  rprog <- resolve mods
  case desugarProgram rprog of
    Right p -> return p
    Left errs -> assertFailure $ "unexpected errors: " ++ show errs

singleRule :: [Module] -> IO D.Rule
singleRule mods = do
  prog <- desugar mods
  let rules = prog.rules
  case rules of
    [r] -> return r
    rs -> assertFailure $ "expected 1 rule, got " ++ show (length rs)

-- | Test-local helper: build a fully-qualified 'Constraint' value to
-- populate raw 'Simplification' / 'Propagation' / 'Simpagation' heads.
-- The DSL itself only exposes the 'Term' constructors 'term' / 'qterm';
-- this helper is the AST-level escape hatch the desugar tests need.
qcon :: Text -> Text -> [Term] -> Constraint
qcon m n args = Constraint (Qualified m n) args

leqQual :: Constraint
leqQual = qcon "M" "leq" [var "X", var "Y"]

leqQual2 :: Constraint
leqQual2 = qcon "M" "leq" [var "A", var "B"]

-- | Convert a fully-qualified parsed 'Constraint' to a
-- 'D.HeadConstraint' for comparison against post-desugar values.
-- Only valid on constraints whose name is 'Qualified' and whose
-- arguments are HNF-shape ('VarTerm' or 'Wildcard'); the test
-- fixtures here always pass that.
hc :: Constraint -> D.HeadConstraint
hc (Constraint (Qualified m n) args) =
  D.HeadConstraint (D.QualifiedName m n) (map toHeadArg args)
  where
    toHeadArg (VarTerm v) = D.HeadVar v
    toHeadArg Wildcard = D.HeadWildcard
    toHeadArg t = error ("hc: non-head-arg in test fixture: " ++ show t)
hc c = error ("hc: expected Qualified constraint, got " ++ show c)

mod1rule :: Head -> Rule
mod1rule h = Rule Nothing (noAnnP h) (noAnnP []) (noAnnP [atom "true"]) []

simpleModule :: Head -> Module
simpleModule h = module' "M" `defining` [mod1rule h]

--------------------------------------------------------------------------------
-- Head normalization
--------------------------------------------------------------------------------

headTests :: TestTree
headTests =
  testGroup
    "head-normalization"
    [ testCase "Simplification maps to kept=[], removed=constraints" $ do
        rule <- singleRule [simpleModule (Simplification [leqQual] [])]
        getNode rule.head @?= D.Head {kept = [], removed = [hc leqQual], aggregates = []},
      testCase "Propagation maps to kept=constraints, removed=[]" $ do
        rule <- singleRule [simpleModule (Propagation [leqQual] [])]
        getNode rule.head @?= D.Head {kept = [hc leqQual], removed = [], aggregates = []},
      testCase "Simpagation maps kept and removed correctly" $ do
        rule <- singleRule [simpleModule (Simpagation [leqQual] [leqQual2] [])]
        getNode rule.head
          @?= D.Head {kept = [hc leqQual], removed = [hc leqQual2], aggregates = []}
    ]

--------------------------------------------------------------------------------
-- Head Normal Form
--------------------------------------------------------------------------------

hnfTests :: TestTree
hnfTests =
  testGroup
    "hnf"
    [ testCase "distinct variables: no change" $ do
        let m = simpleModule (Simplification [qcon "M" "leq" [var "X", var "Y"]] [])
        rule <- singleRule [m]
        getNode rule.head
          @?= D.Head
            []
            [ D.HeadConstraint
                (D.QualifiedName "M" "leq")
                [ D.HeadVar "X",
                  D.HeadVar "Y"
                ]
            ]
            []
        getNode rule.guard @?= [],
      testCase "duplicate variable generates equality guard" $ do
        let m = simpleModule (Simplification [qcon "M" "leq" [var "X", var "X"]] [])
        rule <- singleRule [m]
        getNode rule.head
          @?= D.Head
            []
            [ D.HeadConstraint
                (D.QualifiedName "M" "leq")
                [ D.HeadVar "X",
                  D.HeadVar "$hnf_0"
                ]
            ]
            []
        getNode rule.guard @?= [D.GuardEqual (R.VarExpr "X") (R.VarExpr "$hnf_0")],
      testCase "non-variable argument (integer) generates equality guard" $ do
        let m = simpleModule (Simplification [qcon "M" "leq" [var "X", IntTerm 5]] [])
        rule <- singleRule [m]
        getNode rule.head
          @?= D.Head
            []
            [ D.HeadConstraint
                (D.QualifiedName "M" "leq")
                [ D.HeadVar "X",
                  D.HeadVar "$hnf_0"
                ]
            ]
            []
        getNode rule.guard @?= [D.GuardEqual (R.VarExpr "$hnf_0") (R.IntExpr 5)],
      testCase "non-variable argument (atom) generates equality guard" $ do
        let m = simpleModule (Simplification [qcon "M" "leq" [var "X", atom "foo"]] [])
        rule <- singleRule [m]
        getNode rule.head
          @?= D.Head
            []
            [ D.HeadConstraint
                (D.QualifiedName "M" "leq")
                [ D.HeadVar "X",
                  D.HeadVar "$hnf_0"
                ]
            ]
            []
        getNode rule.guard @?= [D.GuardMatch (R.VarExpr "$hnf_0") (Unqualified "foo") 0],
      testCase "cross-constraint duplicate variable" $ do
        let m =
              simpleModule
                ( Simplification
                    [ qcon "M" "leq" [var "X", var "Y"],
                      qcon "M" "leq" [var "Y", var "Z"]
                    ]
                    []
                )
        rule <- singleRule [m]
        getNode rule.head
          @?= D.Head
            []
            [ D.HeadConstraint (D.QualifiedName "M" "leq") [D.HeadVar "X", D.HeadVar "Y"],
              D.HeadConstraint
                (D.QualifiedName "M" "leq")
                [D.HeadVar "$hnf_0", D.HeadVar "Z"]
            ]
            []
        getNode rule.guard @?= [D.GuardEqual (R.VarExpr "Y") (R.VarExpr "$hnf_0")],
      testCase "simpagation: kept processed before removed" $ do
        let m =
              simpleModule
                ( Simpagation
                    [qcon "M" "leq" [var "X", var "Y"]]
                    [qcon "M" "leq" [var "Y", var "Z"]]
                    []
                )
        rule <- singleRule [m]
        getNode rule.head
          @?= D.Head
            [D.HeadConstraint (D.QualifiedName "M" "leq") [D.HeadVar "X", D.HeadVar "Y"]]
            [ D.HeadConstraint
                (D.QualifiedName "M" "leq")
                [D.HeadVar "$hnf_0", D.HeadVar "Z"]
            ]
            []
        getNode rule.guard @?= [D.GuardEqual (R.VarExpr "Y") (R.VarExpr "$hnf_0")],
      testCase "hnf guards prepended before user guards" $ do
        let m =
              module' "M"
                `defining` [ Rule
                               Nothing
                               ( noAnnP
                                   (Simplification [qcon "M" "leq" [var "X", var "X"]] [])
                               )
                               (noAnnP [hostCall "gt" [var "X", IntTerm 0]])
                               (noAnnP [atom "true"])
                               []
                           ]
        rule <- singleRule [m]
        getNode rule.guard
          @?= [ D.GuardEqual (R.VarExpr "X") (R.VarExpr "$hnf_0"),
                D.GuardExpr (R.HostExpr "gt" [R.VarExpr "X", R.IntExpr 0])
              ],
      testCase "two wildcards stay as wildcards without guards" $ do
        let m = simpleModule (Simplification [qcon "M" "foo" [wildcard, wildcard]] [])
        rule <- singleRule [m]
        getNode rule.head
          @?= D.Head
            []
            [ D.HeadConstraint
                (D.QualifiedName "M" "foo")
                [D.HeadWildcard, D.HeadWildcard]
            ]
            []
        getNode rule.guard @?= [],
      testCase "wildcard and non-variable: only non-variable gets guard" $ do
        let m = simpleModule (Simplification [qcon "M" "foo" [wildcard, IntTerm 1]] [])
        rule <- singleRule [m]
        getNode rule.head
          @?= D.Head
            []
            [ D.HeadConstraint
                (D.QualifiedName "M" "foo")
                [ D.HeadWildcard,
                  D.HeadVar "$hnf_0"
                ]
            ]
            []
        getNode rule.guard @?= [D.GuardEqual (R.VarExpr "$hnf_0") (R.IntExpr 1)]
    ]

--------------------------------------------------------------------------------
-- Guard classification
--------------------------------------------------------------------------------

guardTests :: TestTree
guardTests =
  testGroup
    "guard-classification"
    [ testCase "host call becomes GuardExpr" $ do
        let m =
              module' "M"
                `defining` [ Rule
                               Nothing
                               (noAnnP (Simplification [leqQual] []))
                               ( noAnnP
                                   [ hostCall "gt" [var "X", IntTerm 0]
                                   ]
                               )
                               (noAnnP [atom "true"])
                               []
                           ]
        rule <- singleRule [m]
        getNode rule.guard
          @?= [ D.GuardExpr
                  ( R.HostExpr
                      "gt"
                      [ R.VarExpr "X",
                        R.IntExpr 0
                      ]
                  )
              ],
      testCase "atom true becomes GuardExpr" $ do
        let m =
              module' "M"
                `defining` [ Rule
                               Nothing
                               (noAnnP (Simplification [leqQual] []))
                               ( noAnnP
                                   [ atom
                                       "true"
                                   ]
                               )
                               (noAnnP [atom "true"])
                               []
                           ]
        rule <- singleRule [m]
        getNode rule.guard @?= [D.GuardExpr (R.CtorExpr (Unqualified "true") [])]
    ]

--------------------------------------------------------------------------------
-- Body goal classification
--------------------------------------------------------------------------------

bodyTests :: TestTree
bodyTests =
  testGroup
    "body-classification"
    [ testCase "= becomes BodyUnify" $ do
        rule <-
          singleRule [simpleModule' (Simplification [leqQual] []) [var "X" .=. var "Y"]]
        getNode rule.body @?= [D.BodyUnify (R.VarExpr "X") (R.VarExpr "Y")],
      testCase "is becomes BodyIs" $ do
        rule <-
          singleRule
            [ simpleModule'
                (Simplification [leqQual] [])
                [ var "X" `is` term "+" [int 1, int 2]
                ]
            ]
        getNode rule.body
          @?= [ D.BodyIs
                  "X"
                  ( R.CtorExpr
                      (Unqualified "+")
                      [ R.IntExpr 1,
                        R.IntExpr 2
                      ]
                  )
              ],
      testCase "Qualified compound becomes BodyTell" $ do
        let body = [CompoundTerm (Qualified "M" "leq") [var "X"]]
        rule <- singleRule [simpleModule' (Simplification [leqQual] []) body]
        getNode rule.body
          @?= [D.BodyTell (D.QualifiedName "M" "leq") [R.VarExpr "X"]],
      testCase "hostCall becomes BodyHostStmt" $ do
        rule <-
          singleRule
            [ simpleModule'
                (Simplification [leqQual] [])
                [ hostCall
                    "print"
                    [ var
                        "X"
                    ]
                ]
            ]
        getNode rule.body @?= [D.BodyHostStmt "print" [R.VarExpr "X"]],
      testCase "atom true becomes BodyTrue" $ do
        rule <- singleRule [simpleModule' (Simplification [leqQual] []) [atom "true"]]
        getNode rule.body @?= [D.BodyTrue]
    ]
  where
    simpleModule' h body =
      module' "M"
        `defining` [ Rule
                       Nothing
                       (noAnnP h)
                       (noAnnP [])
                       ( noAnnP
                           body
                       )
                       []
                   ]

--------------------------------------------------------------------------------
-- Error handling
--------------------------------------------------------------------------------

errorTests :: TestTree
errorTests =
  testGroup
    "error-handling"
    [ testCase "unqualified compound in body produces UnexpectedBodyExpr" $ do
        let badExpr = R.CtorExpr (Unqualified "foo") [R.VarExpr "X"]
            m =
              module' "M"
                `defining` [ Rule
                               Nothing
                               (noAnnP (Simplification [leqQual] []))
                               (noAnnP [])
                               (noAnnP [term "foo" [var "X"]])
                               []
                           ]
        rprog <- resolve [m]
        case desugarProgram rprog of
          Left errs ->
            errs @?= [noDiag (AnnP (UnexpectedBodyExpr badExpr) dummyLoc (Atom ""))]
          Right _ -> assertFailure "expected Left",
      testCase "two unqualified compounds collect both errors" $ do
        let bad1 = R.CtorExpr (Unqualified "foo") [R.VarExpr "X"]
            bad2 = R.CtorExpr (Unqualified "bar") [R.VarExpr "Y"]
            m =
              module' "M"
                `defining` [ Rule
                               Nothing
                               (noAnnP (Simplification [leqQual] []))
                               (noAnnP [])
                               (noAnnP [term "foo" [var "X"], term "bar" [var "Y"]])
                               []
                           ]
        rprog <- resolve [m]
        case desugarProgram rprog of
          Left errs ->
            errs
              @?= [ noDiag (AnnP (UnexpectedBodyExpr bad1) dummyLoc (Atom "")),
                    noDiag (AnnP (UnexpectedBodyExpr bad2) dummyLoc (Atom ""))
                  ]
          Right _ -> assertFailure "expected Left",
      testCase "non-true atom in body produces UnexpectedBodyExpr" $ do
        let badExpr = R.CtorExpr (Unqualified "foo") []
            m =
              module' "M"
                `defining` [ Rule
                               Nothing
                               (noAnnP (Simplification [leqQual] []))
                               (noAnnP [])
                               (noAnnP [atom "foo"])
                               []
                           ]
        rprog <- resolve [m]
        case desugarProgram rprog of
          Left errs ->
            errs @?= [noDiag (AnnP (UnexpectedBodyExpr badExpr) dummyLoc (Atom ""))]
          Right _ -> assertFailure "expected Left",
      testCase "bare variable in guard becomes GuardExpr" $ do
        let goal = var "X"
            m =
              module' "M"
                `defining` [ Rule
                               Nothing
                               (noAnnP (Simplification [leqQual] []))
                               (noAnnP [goal])
                               (noAnnP [atom "true"])
                               []
                           ]
        rprog <- resolve [m]
        case desugarProgram rprog of
          Left errs -> assertFailure ("unexpected errors: " ++ show errs)
          Right prog -> case prog.rules of
            (rule : _) -> getNode rule.guard @?= [D.GuardExpr (R.VarExpr "X")]
            [] -> assertFailure "expected at least 1 rule",
      testCase "bare integer in guard produces NonBooleanGuard" $ do
        let badExpr = R.IntExpr 42
            m =
              module' "M"
                `defining` [ Rule
                               Nothing
                               (noAnnP (Simplification [leqQual] []))
                               (noAnnP [int 42])
                               (noAnnP [atom "true"])
                               []
                           ]
        rprog <- resolve [m]
        case desugarProgram rprog of
          Left errs ->
            errs @?= [noDiag (AnnP (NonBooleanGuard badExpr) dummyLoc (Atom ""))]
          Right _ -> assertFailure "expected Left",
      testCase "non-true/false atom in guard produces NonBooleanGuard" $ do
        let badExpr = R.CtorExpr (Unqualified "foo") []
            m =
              module' "M"
                `defining` [ Rule
                               Nothing
                               (noAnnP (Simplification [leqQual] []))
                               (noAnnP [atom "foo"])
                               (noAnnP [atom "true"])
                               []
                           ]
        rprog <- resolve [m]
        case desugarProgram rprog of
          Left errs ->
            errs @?= [noDiag (AnnP (NonBooleanGuard badExpr) dummyLoc (Atom ""))]
          Right _ -> assertFailure "expected Left",
      testCase "atom false becomes GuardExpr" $ do
        let m =
              module' "M"
                `defining` [ Rule
                               Nothing
                               (noAnnP (Simplification [leqQual] []))
                               (noAnnP [atom "false"])
                               (noAnnP [atom "true"])
                               []
                           ]
        rule <- singleRule [m]
        getNode rule.guard @?= [D.GuardExpr (R.CtorExpr (Unqualified "false") [])]
    ]

--------------------------------------------------------------------------------
-- Multi-module flattening
--------------------------------------------------------------------------------

flatteningTests :: TestTree
flatteningTests =
  testGroup
    "flattening"
    [ testCase "two modules with one rule each yield two rules" $ do
        let m1 = module' "A" `defining` [[qterm "A" "c" []] <=> [atom "true"]]
            m2 = module' "B" `defining` [[qterm "B" "d" []] <=> [atom "true"]]
        prog <- desugar [m1, m2]
        length prog.rules @?= 2,
      testCase "empty module list yields empty program" $ do
        prog <- desugar []
        length prog.rules @?= 0,
      testCase "module with no rules contributes no rules" $ do
        let empty = module' "Empty"
            m = module' "M" `defining` [[qterm "M" "c" []] <=> [atom "true"]]
        prog <- desugar [empty, m]
        length prog.rules @?= 1
    ]

--------------------------------------------------------------------------------
-- Rule name preservation
--------------------------------------------------------------------------------

ruleNameTests :: TestTree
ruleNameTests =
  testGroup
    "rule-name"
    [ testCase "named rule preserves name" $ do
        let m =
              module' "M"
                `defining` [ "my_rule"
                               @: [qterm "M" "leq" [var "X", var "Y"]]
                               <=> [atom "true"]
                           ]
        rule <- singleRule [m]
        rule.name @?= Just "my_rule",
      testCase "anonymous rule has Nothing name" $ do
        rule <- singleRule [simpleModule (Simplification [leqQual] [])]
        rule.name @?= Nothing
    ]

--------------------------------------------------------------------------------
-- Symbol table
--------------------------------------------------------------------------------

symbolTableTests :: TestTree
symbolTableTests =
  testGroup
    "symbol-table"
    [ testCase "empty program yields empty table" $
        extractSymbolTable (D.Program [] [] Map.empty Map.empty Map.empty Map.empty [])
          @?= mkSymbolTable [],
      testCase "one qualified constraint in head gets id 0" $ do
        let prog =
              D.Program
                [ D.Rule
                    Nothing
                    (noAnnP (D.Head [] [D.HeadConstraint (D.QualifiedName "M" "leq") []] []))
                    (noAnnP [])
                    (noAnnP [])
                ]
                []
                Map.empty
                Map.empty
                Map.empty
                Map.empty
                []
        extractSymbolTable prog
          @?= mkSymbolTable
            [ ( Identifier (Qualified "M" "leq") 0,
                ConstraintType 0
              )
            ],
      testCase "same constraint in head and body appears only once" $ do
        let prog =
              D.Program
                [ D.Rule
                    Nothing
                    ( noAnnP
                        (D.Head [] [D.HeadConstraint (D.QualifiedName "M" "leq") []] [])
                    )
                    (noAnnP [])
                    ( noAnnP
                        [D.BodyTell (D.QualifiedName "M" "leq") []]
                    )
                ]
                []
                Map.empty
                Map.empty
                Map.empty
                Map.empty
                []
        extractSymbolTable prog
          @?= mkSymbolTable
            [ ( Identifier (Qualified "M" "leq") 0,
                ConstraintType 0
              )
            ],
      testCase "unqualified name in body not in table" $ do
        let prog =
              D.Program
                [ D.Rule
                    Nothing
                    (noAnnP (D.Head [] [D.HeadConstraint (D.QualifiedName "M" "leq") []] []))
                    (noAnnP [])
                    (noAnnP [D.BodyHostStmt "print" []])
                ]
                []
                Map.empty
                Map.empty
                Map.empty
                Map.empty
                []
        let table = extractSymbolTable prog
        lookupSymbol (Identifier (Unqualified "print") 0) table @?= Nothing,
      testCase "ids assigned in Set.toList order (module-first then name)" $ do
        -- Qualified "A" "z" < Qualified "B" "a" by derived Ord
        let prog =
              D.Program
                [ D.Rule
                    Nothing
                    ( noAnnP
                        ( D.Head
                            []
                            [ D.HeadConstraint (D.QualifiedName "A" "z") [],
                              D.HeadConstraint (D.QualifiedName "B" "a") []
                            ]
                            []
                        )
                    )
                    (noAnnP [])
                    (noAnnP [])
                ]
                []
                Map.empty
                Map.empty
                Map.empty
                Map.empty
                []
        let table = extractSymbolTable prog
        ( lookupSymbol (Identifier (Qualified "A" "z") 0) table,
          lookupSymbol (Identifier (Qualified "B" "a") 0) table
          )
          @?= (Just (ConstraintType 0), Just (ConstraintType 1)),
      testCase "same name different arities get distinct ids" $ do
        let prog =
              D.Program
                [ D.Rule
                    Nothing
                    ( noAnnP
                        ( D.Head
                            []
                            [ D.HeadConstraint
                                (D.QualifiedName "M" "foo")
                                [D.HeadVar "X"]
                            ]
                            []
                        )
                    )
                    (noAnnP [])
                    ( noAnnP
                        [ D.BodyTell
                            (D.QualifiedName "M" "foo")
                            [R.VarExpr "X", R.VarExpr "Y"]
                        ]
                    )
                ]
                []
                Map.empty
                Map.empty
                Map.empty
                Map.empty
                []
        let table = extractSymbolTable prog
        symbolTableSize table @?= 2
    ]

--------------------------------------------------------------------------------
-- Lambda lifting
--------------------------------------------------------------------------------

lambdaLiftTests :: TestTree
lambdaLiftTests =
  testGroup
    "lambda-lift"
    [ testCase "lambda captures HNF-bound pattern variable" $ do
        -- f([X|Xs]) -> fun(Y) -> Y + X
        --
        -- HNF decomposes the compound pattern so that X is bound by a
        -- GuardGetArg, not by the surface parameter list. The
        -- lambda-lifter must therefore treat HNF-introduced bindings as
        -- in scope; otherwise the fun(Y) lambda would be lifted without
        -- capturing X and the reference inside the body would dangle.
        let lambdaBody = term "+" [var "Y", var "X"]
            -- Resolved-AST shape of the lambda body. The test module has
            -- no prelude import, so '+' stays 'Unqualified' through
            -- resolution and lands as a 'CtorExpr' (not a 'CallExpr').
            lambdaBodyExpr =
              R.CtorExpr
                (Unqualified "+")
                [R.VarExpr "Y", R.VarExpr "X"]
            lambdaTerm =
              CompoundTerm
                (Unqualified "->")
                [CompoundTerm (Unqualified "fun") [var "Y"], lambdaBody]
            listPattern = term "." [var "X", var "Xs"]
            funDecl =
              noAnn
                ( FunctionDecl
                    FunctionDeclBody
                      { name = "f",
                        arity = 1,
                        argTypes = Nothing,
                        returnType = Nothing,
                        isOpen = False,
                        kind = DKFunction,
                        requiring = Nothing,
                        refining = Nothing
                      }
                )
            funEq =
              noAnnP
                FunctionEquation
                  { funName = Qualified "M" "f",
                    args = [listPattern],
                    guard = noAnnP [],
                    rhs = noAnnP (NE.singleton lambdaTerm),
                    expansion = []
                  }
            m = (module' "M") {decls = [funDecl], equations = [funEq]}
        prog <- desugar [m]
        let (lifted, liftErrs) = liftAllLambdas prog
        liftErrs @?= []
        let isLambda f = f.name.baseName == "__lambda_0"
        case filter isLambda lifted.functions of
          [lam] -> do
            lam.arity @?= 2
            case map (.node) lam.equations of
              [eq] -> do
                eq.params @?= [D.HeadVar "X", D.HeadVar "Y"]
                eq.guards @?= []
                eq.prelude @?= []
                eq.rhs @?= lambdaBodyExpr
              eqs -> assertFailure $ "expected 1 equation, got " ++ show (length eqs)
          fs ->
            assertFailure $ "expected exactly one __lambda_0, got " ++ show (length fs),
      testCase "rejects non-variable lambda parameter" $ do
        -- fun("hello") -> "world" end is rejected at the resolve phase:
        -- the resolver's term-to-Expr translator validates lambda
        -- parameter shapes and raises 'LambdaParamError' before the
        -- desugarer (or lambda lifter) ever sees the program.
        let lambdaTerm =
              CompoundTerm
                (Unqualified "->")
                [ CompoundTerm (Unqualified "fun") [TextTerm "hello"],
                  TextTerm "world"
                ]
            funDecl =
              Ann
                ( FunctionDecl
                    ( FunctionDeclBody
                        "f"
                        1
                        Nothing
                        Nothing
                        False
                        DKFunction
                        Nothing
                        Nothing
                    )
                )
                dummyLoc
            funEq =
              AnnP
                FunctionEquation
                  { funName = Qualified "M" "f",
                    args = [var "X"],
                    guard = noAnnP [],
                    rhs = noAnnP (NE.singleton lambdaTerm),
                    expansion = []
                  }
                dummyLoc
                (Atom "")
            m = (module' "M") {decls = [funDecl], equations = [funEq]}
        case resolveProgram (rewriteImports [m]) of
          Left errs ->
            errs
              @?= [ noDiag
                      ( AnnP
                          (LambdaParamError (TextTerm "hello"))
                          dummyLoc
                          (Atom "")
                      )
                  ]
          Right _ -> assertFailure "expected LambdaParamError"
    ]

--------------------------------------------------------------------------------
-- Aggregates
--------------------------------------------------------------------------------

-- | @aggregate(Agg, Element, Goal, Result)@ with one goal conjunct
-- @M:c(Args)@, as the renamer hands it to the resolver.
plainAgg :: Maybe Term -> Term -> [Term] -> Term -> Aggregate
plainAgg aggTerm elementTerm goalArgs resultTerm =
  Aggregate
    { kind = AggPlain,
      agg = aggTerm,
      element = elementTerm,
      goal = [AggConstraint (qcon "M" "c" goalArgs)],
      result = resultTerm
    }

-- | @fun(P1, ..., Pn) -> Body end@ — the term the resolver reads as a
-- lambda.
aggLambda :: [Term] -> Term -> Term
aggLambda params body =
  CompoundTerm
    (Unqualified "->")
    [CompoundTerm (Unqualified "fun") params, body]

-- | The single aggregate of a one-rule program's head.
onlyAggregate :: D.Rule -> D.Aggregate
onlyAggregate rule = case getNode rule.head of
  D.Head {aggregates = [a]} -> a
  h -> error ("onlyAggregate: expected one aggregate, got " ++ show h)

-- | The parameter names of every lifted lambda in a program, in function
-- order. A lifted lambda's equation parameters are its captures followed by
-- its own parameters.
liftedLambdaParams :: D.Program -> [[Text]]
liftedLambdaParams prog =
  [ [v | D.HeadVar v <- eq.node.params]
  | f <- prog.functions,
    Just _ <- [f.lambdaArity],
    eq <- f.equations
  ]

aggregateTests :: TestTree
aggregateTests =
  testGroup
    "aggregates"
    [ testCase "compound goal argument: fresh variable plus that conjunct's guards" $ do
        let hd =
              Propagation
                [leqQual]
                [ plainAgg
                    (Just (int 0))
                    (int 1)
                    [CompoundTerm (Unqualified "pair") [var "X", var "Y"]]
                    Wildcard
                ]
        rule <- singleRule [simpleModule hd]
        case onlyAggregate rule of
          D.Aggregate {goal = [D.AggConstraint hcon guards]} -> do
            hcon.args @?= [D.HeadVar "$hnf_0"]
            guards
              @?= [ D.GuardMatch (R.VarExpr "$hnf_0") (Unqualified "pair") 2,
                    D.GuardGetArg "X" (R.VarExpr "$hnf_0") 0,
                    D.GuardGetArg "Y" (R.VarExpr "$hnf_0") 1
                  ]
            -- The guards belong to the conjunct, so they are evaluated
            -- inside its loop and never join the rule's guard.
            getNode rule.guard @?= []
          a -> assertFailure ("unexpected aggregate: " ++ show a),
      testCase "repeated goal variable: equality guard" $ do
        let hd =
              Propagation
                [leqQual]
                [plainAgg (Just (int 0)) (int 1) [var "X", var "X"] Wildcard]
        rule <- singleRule [simpleModule hd]
        case onlyAggregate rule of
          D.Aggregate {goal = [D.AggConstraint hcon guards]} -> do
            -- The goal starts from an empty seen set: X's first occurrence
            -- binds, the second is matched against it.
            hcon.args @?= [D.HeadVar "X", D.HeadVar "$hnf_0"]
            guards @?= [D.GuardEqual (R.VarExpr "X") (R.VarExpr "$hnf_0")]
          a -> assertFailure ("unexpected aggregate: " ++ show a),
      testCase "a nested goal does not change what the enclosing goal has seen" $ do
        let nested = plainAgg (Just (int 0)) (int 1) [var "Y"] Wildcard
            outer =
              (plainAgg (Just (int 0)) (int 1) [] Wildcard)
                { goal =
                    [ AggConstraint (qcon "M" "c" [var "X"]),
                      AggNested nested,
                      AggConstraint (qcon "M" "c" [var "X"])
                    ]
                }
        rule <- singleRule [simpleModule (Propagation [leqQual2] [outer])]
        case onlyAggregate rule of
          D.Aggregate {goal = [_, D.AggNested _, D.AggConstraint hcon guards]} -> do
            -- X was seen by the enclosing goal before the nested one, so
            -- its second occurrence is still matched against the first.
            hcon.args @?= [D.HeadVar "$hnf_0"]
            guards @?= [D.GuardEqual (R.VarExpr "X") (R.VarExpr "$hnf_0")]
          a -> assertFailure ("unexpected aggregate: " ++ show a),
      testCase "head and goal share one fresh-name counter" $ do
        let hd =
              Propagation
                [qcon "M" "leq" [CompoundTerm (Unqualified "pair") [var "X", var "Y"]]]
                [ plainAgg
                    (Just (int 0))
                    (int 1)
                    [CompoundTerm (Unqualified "pair") [var "Z"]]
                    Wildcard
                ]
        rule <- singleRule [simpleModule hd]
        -- The head's compound argument consumed $hnf_0, so the goal's is
        -- \$hnf_1: the counter is shared, the seen set is not.
        case onlyAggregate rule of
          D.Aggregate {goal = [D.AggConstraint hcon _]} ->
            hcon.args @?= [D.HeadVar "$hnf_1"]
          a -> assertFailure ("unexpected aggregate: " ++ show a)
        length (getNode rule.guard) @?= 3,
      testCase "lambda in element captures a goal variable" $ do
        let hd =
              Propagation
                [leqQual]
                [ plainAgg
                    (Just (int 0))
                    (aggLambda [var "Y"] (var "W"))
                    [var "W"]
                    (var "W")
                ]
        prog <- desugar [simpleModule hd]
        let (prog', errs) = liftAllLambdas prog
        errs @?= []
        -- The element is evaluated inside the goal's loop, so the goal
        -- variable is in scope and becomes a leading capture parameter.
        liftedLambdaParams prog' @?= [["W", "Y"]],
      testCase "lambda in agg does not capture a goal variable" $ do
        let hd =
              Propagation
                [leqQual]
                [ plainAgg
                    (Just (aggLambda [var "Y"] (var "W")))
                    (int 1)
                    [var "W"]
                    (var "W")
                ]
        prog <- desugar [simpleModule hd]
        let (prog', errs) = liftAllLambdas prog
        errs @?= []
        -- agg is evaluated before the fold's loops: the goal variable is
        -- outside its scope, so it is not captured. Compiling the lifted
        -- body reports it as an unbound variable, which is the right
        -- diagnostic for a value the closure cannot have.
        liftedLambdaParams prog' @?= [["Y"]]
    ]
