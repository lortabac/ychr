module YCHR.DSL where

import YCHR.Parsed
import YCHR.Types

--------------------------------------------------------------------------------
-- Module & Declaration Helpers
--------------------------------------------------------------------------------

-- | Create a new module definition
module' :: String -> Module
module' name = Module name [] [] []

-- | Add imports to a module
importing :: Module -> [String] -> Module
importing m imps = m {modImports = imps}

-- | Add declarations to a module: @declaring [ "leq" // 2 ]@
declaring :: Module -> [Declaration] -> Module
declaring m decls = m {modDecls = decls}

-- | Add rules to a module
defining :: Module -> [Rule] -> Module
defining m rules = m {modRules = rules}

-- | Helper for arity: @"leq" // 2@
(//) :: String -> Int -> Declaration
(//) = ConstraintDecl

--------------------------------------------------------------------------------
-- Rule Construction Operators
--------------------------------------------------------------------------------

-- | Name a rule: @"my_rule" @: [con "a" []] <=> [con "b" []]@
(@:) :: String -> Rule -> Rule
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
con :: String -> [Term] -> Constraint
con n args = Constraint (Unqualified n) args

-- | Manual qualification operator: @"Mod" .: con "leq" [X, Y]@
(.:) :: String -> Constraint -> Constraint
m .: (Constraint (Unqualified n) args) = Constraint (Qualified m n) args
_ .: c = c

-- | Create a variable term
var :: String -> Term
var = VarTerm

-- | Create a compound term (data functor)
func :: String -> [Term] -> Term
func n args = CompoundTerm (Unqualified n) args

-- | Create an atom term
atom :: String -> Term
atom = AtomTerm

--------------------------------------------------------------------------------
-- Syntax Sugar for Body Goals
--------------------------------------------------------------------------------

-- | Unification: @var "X" .=. var "Y"@
(.=.) :: Term -> Term -> Term
l .=. r = CompoundTerm (Unqualified "=") [l, r]

-- | Host assignment: @var "X" .:=. func "get_val" []@
(.:=.) :: Term -> Term -> Term
v .:=. f = CompoundTerm (Unqualified ":=") [v, f]

-- | Host statement: @hostStmt "print" [var "X"]@
hostStmt :: String -> [Term] -> Term
hostStmt f args = CompoundTerm (Unqualified "$") [CompoundTerm (Unqualified f) args]

--------------------------------------------------------------------------------
-- Built-in Operator Helpers
--------------------------------------------------------------------------------

-- | Addition: @var "X" .+. var "Y"@
(.+.) :: Term -> Term -> Term
l .+. r = CompoundTerm (Unqualified "+") [l, r]

-- | Subtraction: @var "X" .-. var "Y"@
(.-.) :: Term -> Term -> Term
l .-. r = CompoundTerm (Unqualified "-") [l, r]

-- | Multiplication: @var "X" .*. var "Y"@
(.*.) :: Term -> Term -> Term
l .*. r = CompoundTerm (Unqualified "*") [l, r]

-- | Division: @var "X" ./. var "Y"@
(./.) :: Term -> Term -> Term
l ./. r = CompoundTerm (Unqualified "/") [l, r]

-- | Negation: @neg (var "X")@
neg :: Term -> Term
neg x = CompoundTerm (Unqualified "neg") [x]

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
