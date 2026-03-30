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
module' name = Module name [] [] [] [] Nothing

-- | Set the export list of a module
exporting :: Module -> [Declaration] -> Module
exporting m ds = m {exports = Just ds}

-- | Add imports to a module
importing :: Module -> [Text] -> Module
importing m imps = m {imports = map (noAnn . ModuleImport) imps}

-- | Add declarations to a module: @declaring [ "leq" // 2 ]@
declaring :: Module -> [Declaration] -> Module
declaring m ds = m {decls = map noAnn ds}

-- | Add rules to a module
defining :: Module -> [Rule] -> Module
defining m rls = m {rules = rls}

-- | Helper for arity: @"leq" // 2@
(//) :: Text -> Int -> Declaration
(//) = ConstraintDecl

--------------------------------------------------------------------------------
-- Rule Construction Operators
--------------------------------------------------------------------------------

-- | Name a rule: @"my_rule" @: [con "a" []] <=> [con "b" []]@
(@:) :: Text -> Rule -> Rule
n @: (Rule _ h g b) = Rule (Just (noAnn n)) h g b

-- | Simplification Rule: @[head] <=> [body]@
(<=>) :: [Constraint] -> [Term] -> Rule
lhs <=> rhs = Rule Nothing (noAnn (Simplification lhs)) (noAnn []) (noAnn rhs)

-- | Propagation Rule: @[head] ==> [body]@
(==>) :: [Constraint] -> [Term] -> Rule
lhs ==> rhs = Rule Nothing (noAnn (Propagation lhs)) (noAnn []) (noAnn rhs)

-- | Simpagation Rule: @[kept] \ [removed] <=> [body]@
(\\) :: [Constraint] -> [Constraint] -> [Term] -> Rule
(k \\ r) body = Rule Nothing (noAnn (Simpagation k r)) (noAnn []) (noAnn body)

-- | Add a guard to an existing rule (infix)
(|-) :: Rule -> [Term] -> Rule
r |- g = let Rule n h _ b = r in Rule n h (noAnn g) b

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

-- | Arithmetic evaluation: @var "X" \`is\` func "+" [int 2, var "Y"]@
is :: Term -> Term -> Term
is v e = CompoundTerm (Unqualified "is") [v, e]

infixr 3 `is`

-- | Host call: @hostCall "print" [var "X"]@ produces @host:print(X)@.
hostCall :: Text -> [Term] -> Term
hostCall f args = CompoundTerm (Qualified "host" f) args

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
