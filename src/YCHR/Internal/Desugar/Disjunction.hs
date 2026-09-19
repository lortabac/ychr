{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Lowering the disjunction operator @;@ to choice points.
--
-- @;@ is surface syntax for a @search:alt\/1@ constraint over lifted
-- goals. This pass is the lifting: every 'D.BodyOr' becomes a tell of
-- @search:alt@ whose argument is the list of quoted disjunct calls,
-- and every branch becomes a rule of its own.
--
-- > h(X) <=> p(X), (b(X) ; c(Y), d(X, Y)), q(X).
-- > % ==>
-- > h(X) <=> p(X), alt([quote('__disj_1'(X)), quote('__disj_2'(X, Y))]), q(X).
-- > '__disj_1'(X)    <=> b(X).
-- > '__disj_2'(X, Y) <=> c(Y), d(X, Y).
--
-- It has the same shape as lambda lifting
-- ('YCHR.Internal.Desugar.liftAllLambdas'), and shares its rule for
-- parameters: a disjunct takes the variables it shares with the
-- enclosing rule's scope — head, guard and body — in ascending order.
-- A variable that occurs only inside one branch is still in the rule's
-- body scope, so it is a parameter too. That is what makes it the same
-- variable in every branch that mentions it, and after the
-- disjunction: it is allocated once, before the choice.
--
-- Two orderings matter and are easy to get wrong:
--
--   * This runs /after/ lambda lifting, so a lambda inside a disjunct
--     has already become a closure over the enclosing scope and moves
--     into the lifted rule as an ordinary expression.
--   * This runs /after/ type checking, which sees the pre-lowering AST
--     where each branch is still in the enclosing rule and checked
--     against its typing. The lifted constraints are therefore
--     declared arity-only (every argument @any@): deriving argument
--     types here would only restate what has already been checked.
module YCHR.Internal.Desugar.Disjunction (lowerDisjunctions) where

import Data.List (mapAccumL)
import Data.List.NonEmpty qualified as NE
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as T
import YCHR.Internal.Desugar (bodyGoalVars, guardVars)
import YCHR.Internal.Desugared qualified as D
import YCHR.Internal.Parsed (AnnP (..))
import YCHR.Internal.Resolved qualified as R
import YCHR.Internal.Types
  ( ConstraintKey (..),
    HeadArg (..),
    HeadConstraint (..),
    Name (..),
    QualifiedName (..),
    TypeExpr (..),
  )
-- Hidden so '.head' resolves under MicroHs (dev-docs/MICROHS_GAPS.md, gap 1).
import Prelude hiding (head)

-- | The argument type a lifted constraint is declared with. Arity-only
-- declarations spell every position @any@; see 'lowerDisjunctions' on
-- why the branch's real types are not recovered here.
anyType :: TypeExpr
anyType = TypeCon (Unqualified "any") []

-- | Prefix for the constraints this pass lifts branches into. Mirrors
-- 'YCHR.Internal.Desugar.lambdaPrefix'.
disjPrefix :: Text
disjPrefix = "__disj_"

-- | The choice-point constraint @;@ compiles to. Matches
-- 'YCHR.Internal.Runtime.Goal.altName'; the renamer has already
-- refused a @;@ in a module that cannot see it (YCHR-20021).
altConstraint :: QualifiedName
altConstraint = QualifiedName "search" "alt"

-- | Threaded state: a counter supplying fresh @__disj_N@ names, and
-- the rules lifted out so far, newest first. The counter is global to
-- the program rather than per rule, so a name identifies its branch
-- uniquely wherever it shows up.
data LowerState = LowerState
  { counter :: !Int,
    lifted :: [D.Rule]
  }

-- | Rewrite every disjunction in the program into a choice point.
--
-- A program with no @;@ comes back with the same rules and the same
-- constraint table.
lowerDisjunctions :: D.Program -> D.Program
lowerDisjunctions prog =
  let st0 = LowerState {counter = 1, lifted = []}
      (st, rules') = mapAccumL lowerRule st0 prog.rules
      newRules = reverse st.lifted
   in prog
        { D.rules = rules' ++ newRules,
          D.constraintTypes =
            Map.union prog.constraintTypes (Map.fromList (map declOf newRules))
        }
  where
    -- Arity-only, exactly as `:- chr_constraint name/arity` would be.
    declOf r = case r.head.node.removed of
      [c] -> (ConstraintKey c.name (length c.args), map (const anyType) c.args)
      _ -> error "Disjunction.declOf: lifted rule is not a simplification"

lowerRule :: LowerState -> D.Rule -> (LowerState, D.Rule)
lowerRule st rule =
  let (st', goals) = lowerGoals (contextOf rule) st rule.body.node
   in (st', rule {D.body = rule.body {node = goals}})

-- | What a lifted branch needs from the rule it came out of: the
-- module to declare the new constraint in, the variables in scope, and
-- the annotations to carry over so a diagnostic inside a branch still
-- points at the source the branch was written in.
data Context = Context
  { modName :: Text,
    scope :: Set.Set Text,
    headAnn :: AnnP D.Head,
    bodyAnn :: AnnP [D.BodyGoal]
  }

contextOf :: D.Rule -> Context
contextOf rule =
  Context
    { modName = ruleModName rule.head.node,
      scope = ruleScope rule,
      headAnn = rule.head,
      bodyAnn = rule.body
    }

lowerGoals :: Context -> LowerState -> [D.BodyGoal] -> (LowerState, [D.BodyGoal])
lowerGoals ctx = mapAccumL (lowerGoal ctx)

-- | One goal. Only 'D.BodyOr' changes: @;@ can appear nowhere else in
-- a body, so no other shape needs walking.
lowerGoal :: Context -> LowerState -> D.BodyGoal -> (LowerState, D.BodyGoal)
lowerGoal ctx st (D.BodyOr branches) =
  let (st', altGoals) = mapAccumL (liftBranch ctx) st (NE.toList branches)
   in (st', D.BodyTell altConstraint [exprList altGoals])
lowerGoal _ st goal = (st, goal)

-- | Lift one branch into its own rule and return the quoted call that
-- names it. A nested disjunction inside the branch is lowered first,
-- so the rule this produces is already free of them.
liftBranch :: Context -> LowerState -> [D.BodyGoal] -> (LowerState, R.Expr)
liftBranch ctx st branch =
  let (st1, branch') = lowerGoals ctx st branch
      params = Set.toAscList (bodyGoalVars branch' `Set.intersection` ctx.scope)
      idx = st1.counter
      qname = QualifiedName ctx.modName (disjPrefix <> T.pack (show idx))
      rule =
        D.Rule
          { name = Nothing,
            head =
              ctx.headAnn
                { node =
                    D.Head
                      { kept = [],
                        removed = [HeadConstraint qname (map HeadVar params)]
                      }
                },
            guard = ctx.bodyAnn {node = []},
            body = ctx.bodyAnn {node = branch'}
          }
      st2 = st1 {counter = idx + 1, lifted = rule : st1.lifted}
   in (st2, quoted (R.CtorExpr (qualifiedName qname) (map R.VarExpr params)))

-- | Wrap a disjunct call in @quote\/1@. The alternatives of an @alt@
-- are goals, not values: the compound has to reach the store as data
-- rather than be told when the list is built.
quoted :: R.Expr -> R.Expr
quoted e = R.CtorExpr (Unqualified "quote") [e]

qualifiedName :: QualifiedName -> Name
qualifiedName (QualifiedName m n) = Qualified m n

-- | A runtime list as an expression, over the prelude's list
-- constructors — the pair the renamer canonicalizes @[a, b]@ to.
exprList :: [R.Expr] -> R.Expr
exprList = foldr cons nil
  where
    cons h t = R.CtorExpr (Qualified "prelude" ".") [h, t]
    nil = R.CtorExpr (Qualified "prelude" "[]") []

-- | Every variable the rule mentions: head, guard, and body. The same
-- scope the lambda lifter uses, and for the same reason — a lifted
-- body must not capture a name the enclosing rule does not have.
ruleScope :: D.Rule -> Set.Set Text
ruleScope rule =
  Set.unions
    [ Set.fromList
        [ v
        | c <- rule.head.node.kept ++ rule.head.node.removed,
          HeadVar v <- c.args
        ],
      guardVars rule.guard.node,
      bodyGoalVars rule.body.node
    ]

-- | The module a rule belongs to, read off its head. Mirrors
-- 'YCHR.Internal.Desugar.ruleModName'; the qualification invariant is
-- enforced by 'HeadConstraint', and only an empty head could fail,
-- which the parser does not produce.
ruleModName :: D.Head -> Text
ruleModName h = case h.kept ++ h.removed of
  (c : _) -> c.name.moduleName
  [] -> error "Disjunction.ruleModName: empty rule head"
