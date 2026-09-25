-- | Which argument positions a VM program looks up through an index.
--
-- The compiler turns the equality guards of a rule occurrence into
-- 'Foreach' index conditions; this module reads those conditions back
-- off a 'Program', which is what tells the runtime which
-- @(constraint type, argument position)@ pairs a store must keep an
-- index for. It lives next to the IR rather than in the runtime so that
-- the compiled program can carry the answer as a lazily computed field
-- ('YCHR.Internal.Compile.Pipeline.CompiledProgram'), instead of every
-- session walking the whole program — prelude included — before a short
-- goal has done any work.
--
-- See "YCHR.Internal.Runtime.Index" for what the runtime does with the
-- result.
module YCHR.Internal.VM.Index
  ( indexablePositions,
  )
where

import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IntMap
import Data.IntSet (IntSet)
import Data.IntSet qualified as IntSet
import Data.List qualified as List
import YCHR.Internal.Types (ConstraintType (..))
import YCHR.Internal.VM.Types (ArgIndex (..), Procedure (..), Program (..), Stmt (..))

-- | The argument positions the program ever looks up through an index
-- condition, per constraint type index.
--
-- Every 'Foreach' condition is a candidate: the compiler emits one per
-- equality guard it managed to lift onto the iterator. Positions are
-- collected whatever the nesting depth, because a 'Foreach' can sit
-- inside another loop's body, inside a conditional, or inside a
-- reactivation drain.
--
-- A condition this returns is one the store must be able to answer for
-- every constraint it stores, so a missing entry is not a missed
-- optimization but a wrong answer: a position the store was not told to
-- index has no entries, and a lookup there would find nothing. The walk
-- is therefore over /every/ procedure of the program — including the
-- library and prelude procedures the program pulls in, which is what
-- makes the answer big enough to be worth caching.
indexablePositions :: Program -> IntMap IntSet
indexablePositions prog = List.foldl' addProc IntMap.empty prog.procedures
  where
    -- Both bodies are pattern-bound rather than reached through a
    -- record-dot selector: a selector's type here is only constrained
    -- by the 'Foldable' the surrounding 'List.foldl'' is instantiated
    -- at, which GHC cannot resolve.
    addProc acc Procedure {body = stmts} = List.foldl' addStmt acc stmts
    addStmt acc stmt = case stmt of
      Foreach _ cType _ conds body ->
        List.foldl' addStmt (List.foldl' (addCond cType) acc conds) body
      If _ thenStmts elseStmts ->
        List.foldl' addStmt (List.foldl' addStmt acc thenStmts) elseStmts
      DrainReactivationQueue _ body -> List.foldl' addStmt acc body
      _ -> acc
    addCond cType acc (ArgIndex pos, _) =
      let ConstraintType tidx = cType
       in IntMap.insertWith IntSet.union tidx (IntSet.singleton pos) acc
