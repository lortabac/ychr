{-# LANGUAGE LambdaCase #-}

-- | Procedure-name closure over a VM program.
--
-- Every @CallExpr@ a program carries must name one of the program's own
-- procedures, and so must every target of its 'Program.evaluables' and
-- 'Program.callables' dispatch tables. The compiler derives the
-- procedure names, the call sites that name them, and both tables'
-- targets from the same function list, so a dangling target is a
-- compiler bug rather than anything a user program can produce. The
-- interpreter reports one at run time as @callProc: unknown procedure
-- \@name@, on whichever path reaches it first; this module lets the
-- compiler report it before the program runs.
--
-- The check is run as an assertion, not as a user-facing diagnostic:
-- see @YCHR.Internal.Compile.Pipeline.compileModules@ for the compiled
-- program, and @YCHR.Internal.Runtime.Session.withCHRExtra@ for the
-- query-time procedures and callables that are compiled after it. The
-- latter must resolve against the /union/ of the compiled names and the
-- extras' own, because an extra may call a compiled procedure and one
-- extra may call another.
--
-- The walk is total: every 'Stmt', 'ValExpr', 'BoolExpr', 'IdExpr' and
-- 'CallArg' constructor has exactly one arm, with no catch-all, so a
-- constructor added to the VM makes this module non-exhaustive and
-- therefore a build failure under @-Wall -Werror@.
--
-- Two readings are deliberately not checked here. A hand-built
-- 'Program' — the one the interpreter's 'YCHR.Internal.Runtime.Interpreter.interpret'
-- takes — is not compiler output, so it keeps the interpreter's runtime
-- error; and a @CallExpr@ name that names a procedure of a /different/
-- program is indistinguishable from a missing one at this granularity.
module YCHR.Internal.VM.Closure
  ( -- * Checks
    danglingTargets,
    danglingCalls,
    danglingCallables,
    procedureNames,
    closureFailure,
  )
where

import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text qualified as T
import YCHR.Internal.VM.Types
  ( BoolExpr (..),
    CallArg (..),
    CallableKey,
    EvaluableKey,
    IdExpr (..),
    Name (..),
    Procedure (..),
    Program (..),
    Stmt (..),
    ValExpr (..),
    historyIdsList,
  )

-- | The names of a program's procedures: the table a closure check
-- resolves against.
procedureNames :: [Procedure] -> Set Name
procedureNames procs = Set.fromList [p.name | p <- procs]

-- | Every call target a compiled program carries that its own procedure
-- table does not define: the @CallExpr@ sites of every body, then the
-- 'Program.evaluables' and 'Program.callables' targets. In
-- first-appearance order, without duplicates. An empty list means the
-- program is closed; 'closureFailure' turns a non-empty one into the
-- message a caller reports.
danglingTargets :: Program -> [Name]
danglingTargets prog =
  danglingCalls known prog.procedures
    ++ danglingEvaluables known prog.evaluables
    ++ danglingCallables known prog.callables
  where
    known = procedureNames prog.procedures

-- | The targets of the @CallExpr@ sites reachable from these procedures
-- that @known@ does not define, in first-appearance order, without
-- duplicates.
danglingCalls :: Set Name -> [Procedure] -> [Name]
danglingCalls known = dedup . concatMap procedureCalls
  where
    procedureCalls Procedure {body = stmts} = concatMap stmtCalls stmts

    stmtCalls = \case
      LetVal _ e -> valCalls e
      LetId _ e -> idCalls e
      AssignVal _ e -> valCalls e
      AssignId _ e -> idCalls e
      If cond thenStmts elseStmts ->
        boolCalls cond
          ++ concatMap stmtCalls thenStmts
          ++ concatMap stmtCalls elseStmts
      Foreach _ _ _ conds body ->
        concatMap (valCalls . snd) conds ++ concatMap stmtCalls body
      Continue _ -> []
      Break _ -> []
      Return e -> valCalls e
      ExprStmt e -> valCalls e
      BoolExprStmt e -> boolCalls e
      Store e -> idCalls e
      Kill e -> idCalls e
      AddHistory _ ids -> concatMap idCalls (historyIdsList ids)
      DrainReactivationQueue _ body -> concatMap stmtCalls body
      PushFrame _ -> []

    valCalls = \case
      Var _ -> []
      Lit _ -> []
      CallExpr n args
        | Set.member n known -> concatMap argCalls args
        | otherwise -> n : concatMap argCalls args
      HostCall _ es -> concatMap valCalls es
      EvalDeep e -> valCalls e
      ApplyClosure f es -> valCalls f ++ concatMap valCalls es
      EvalIs e -> valCalls e
      NewVar -> []
      MakeTerm _ es -> concatMap valCalls es
      GetArg e _ -> valCalls e
      FieldArg e _ -> idCalls e
      FieldType e -> idCalls e

    argCalls = \case
      AVal e -> valCalls e
      AId e -> idCalls e

    boolCalls = \case
      BLit _ -> []
      BNot e -> boolCalls e
      BAnd l r -> boolCalls l ++ boolCalls r
      BOr l r -> boolCalls l ++ boolCalls r
      BMatchTerm e _ _ -> valCalls e
      BEqual l r -> valCalls l ++ valCalls r
      BIdEqual l r -> idCalls l ++ idCalls r
      BAlive e -> idCalls e
      BIsConstraintType e _ -> idCalls e
      BNotInHistory _ ids -> concatMap idCalls (historyIdsList ids)
      BUnify l r -> valCalls l ++ valCalls r
      BFromVal e -> valCalls e
      BEvalDeep e -> boolCalls e
      BSoftGuard e -> boolCalls e

    idCalls = \case
      IdVar _ -> []
      CreateConstraint _ es -> concatMap valCalls es

-- | The dispatch-table half of 'danglingTargets', split out for the
-- union check @Session.withCHRExtra@ runs over query-time callables.
danglingEvaluables :: Set Name -> [(EvaluableKey, Name)] -> [Name]
danglingEvaluables known entries = missingIn known (map snd entries)

-- | 'danglingEvaluables' over a program's callables table.
danglingCallables :: Set Name -> [(CallableKey, Name)] -> [Name]
danglingCallables known entries = missingIn known (map snd entries)

missingIn :: Set Name -> [Name] -> [Name]
missingIn known = dedup . filter (`Set.notMember` known)

-- | First appearance wins, so a report names the call site the walk
-- reached first rather than an arbitrary duplicate.
dedup :: [Name] -> [Name]
dedup = go Set.empty
  where
    go _ [] = []
    go seen (n : ns)
      | Set.member n seen = go seen ns
      | otherwise = n : go (Set.insert n seen) ns

-- | The compiler-bug message for the first dangling target, or
-- 'Nothing' when the list is empty. @ctx@ names the check that ran, so
-- the message reads @compileModules: call to unknown procedure x@.
closureFailure :: String -> [Name] -> Maybe String
closureFailure _ [] = Nothing
closureFailure ctx (n : _) =
  Just (ctx ++ ": call to unknown procedure " ++ T.unpack n.unName)
