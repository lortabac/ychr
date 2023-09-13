{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE OverloadedStrings #-}

module YCHR.Compiler.Rename.Tests (tests) where

import Test.Tasty
import Test.Tasty.HUnit
import YCHR.Compiler.Rename
import YCHR.Types.Common
import YCHR.Types.Parsed
import YCHR.Types.Renamed

tests :: TestTree
tests =
  testGroup
    "renamer tests"
    [ testCase "qualify names" $
        qualifyModuleNames psModule1 @?= Right rnModule1
    ]

psModule1 :: PsModule
psModule1 =
  Module
    { moduleName = "module1",
      imports = [Import "module2" ["constr2", "constr3"]],
      constraints = [ConstraintDef "constr1"],
      rules = [psRule1]
    }

rnModule1 :: RnModule
rnModule1 = psModule1 {rules = [rnRule1]}

psRule1 :: PsRule
psRule1 = Simplification Nothing (Head [psConstr1]) (Guard []) (Body [ChrConstr psConstr2])

rnRule1 :: RnRule
rnRule1 = Simplification Nothing (Head [rnConstr1]) (Guard []) (Body [ChrConstr rnConstr2])

psConstr1 :: PsChrConstraint
psConstr1 = ChrConstraint (PsName "constr1") []

psConstr2 :: PsChrConstraint
psConstr2 = ChrConstraint (PsName "constr2") []

rnConstr1 :: RnChrConstraint
rnConstr1 = ChrConstraint (QualifiedName "module1" "constr1") []

rnConstr2 :: RnChrConstraint
rnConstr2 = ChrConstraint (QualifiedName "module2" "constr2") []
