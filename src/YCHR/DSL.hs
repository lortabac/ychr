{-# LANGUAGE OverloadedStrings #-}

module YCHR.DSL where

import Data.Text (Text)
import YCHR.Parsed
import YCHR.Types

--------------------------------------------------------------------------------
-- Module & Declaration Helpers
--------------------------------------------------------------------------------

-- | Create a new module definition
module' :: Text -> Module
module' name = Module name [] [] [] Nothing

-- | Set the export list of a module
exporting :: Module -> [Declaration] -> Module
exporting m decls = m {modExports = Just decls}

-- | Add imports to a module
importing :: Module -> [Text] -> Module
importing m imps = m {modImports = map ModuleImport imps}

-- | Add declarations to a module: @declaring [ "leq" // 2 ]@
declaring :: Module -> [Declaration] -> Module
declaring m decls = m {modDecls = decls}

-- | Add rules to a module
defining :: Module -> [Rule] -> Module
defining m rules = m {modRules = rules}

-- | Helper for arity: @"leq" // 2@
(//) :: Text -> Int -> Declaration
(//) = ConstraintDecl

--------------------------------------------------------------------------------
-- Rule Construction Operators
--------------------------------------------------------------------------------

-- | Name a rule: @"my_rule" @: [con "a" []] <=> [con "b" []]@
(@:) :: Text -> Rule -> Rule
name @: r = r {ruleName = Just name}

-- | Simplification Rule: @[head] <=> [body]@
(<=>) :: [Constraint] -> [Term] -> Rule
lhs <=> rhs = Rule Nothing (Simplification lhs) [] rhs

-- | Propagation Rule: @[head] ==> [body]@
(==>) :: [Constraint] -> [Term] -> Rule
lhs ==> rhs = Rule Nothing (Propagation lhs) [] rhs

-- | Simpagation Rule: @[kept] \ [removed] <=> [body]@
(\\) :: [Constraint] -> [Constraint] -> [Term] -> Rule
(k \\ r) body = Rule Nothing (Simpagation k r) [] body

-- | Add a guard to an existing rule (infix)
(|-) :: Rule -> [Term] -> Rule
r |- g = r {ruleGuard = g}

--------------------------------------------------------------------------------
-- Constraint & Term Helpers
--------------------------------------------------------------------------------

-- | Create a constraint (defaults to Unqualified)
con :: Text -> [Term] -> Constraint
con n args = Constraint (Unqualified n) args

-- | Manual qualification operator: @"Mod" .: con "leq" [X, Y]@
(.:) :: Text -> Constraint -> Constraint
m .: (Constraint (Unqualified n) args) = Constraint (Qualified m n) args
_ .: c = c

-- | Create a variable term
var :: Text -> Term
var = VarTerm

-- | Create a compound term (data functor)
func :: Text -> [Term] -> Term
func n args = CompoundTerm (Unqualified n) args

-- | Create an atom term
atom :: Text -> Term
atom = AtomTerm

-- | Integer literal term
int :: Int -> Term
int = IntTerm

-- | Text (string) literal term
text :: Text -> Term
text = TextTerm

-- | Wildcard term: matches anything without binding
wildcard :: Term
wildcard = Wildcard

--------------------------------------------------------------------------------
-- Syntax Sugar for Body Goals
--------------------------------------------------------------------------------

-- | Unification: @var "X" .=. var "Y"@
(.=.) :: Term -> Term -> Term
l .=. r = CompoundTerm (Unqualified "=") [l, r]

-- | Host assignment: @var "X" .:=. func "get_val" []@
(.:=.) :: Term -> Term -> Term
v .:=. f = CompoundTerm (Unqualified ":=") [v, f]

-- | Arithmetic evaluation: @var "X" \`is\` func "+" [int 2, var "Y"]@
is :: Term -> Term -> Term
is v e = CompoundTerm (Unqualified "is") [v, e]

infixr 3 `is`

-- | Host statement: @hostStmt "print" [var "X"]@
hostStmt :: Text -> [Term] -> Term
hostStmt f args = CompoundTerm (Unqualified "host") [CompoundTerm (Unqualified f) args]

{-

Examples:

orderModule :: Module
orderModule =
  module' "Order"
    `declaring` [ "leq" // 2 ]
    `defining`  [
        "refl" @: [con "leq" [var "X", var "X"]] <=> [atom "true"]
      ]

logicModule :: Module
logicModule =
  module' "Logic"
    `importing` [ "Order" ]
    `defining`  [
        -- "leq" will be qualified to "Order:leq" during Renaming
        "trans" @: [con "leq" [var "X", var "Y"], con "leq" [var "Y", var "Z"]]
               ==> [con "leq" [var "X", var "Z"]]
      ]
-}
