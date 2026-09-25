{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedRecordDot #-}

-- | The Haskell interpreter's slot phase: a VM program with every local
-- variable resolved to a per-procedure integer slot.
--
-- The VM ('YCHR.Internal.VM.Types') identifies a local variable by its
-- 'Name' — a 'Data.Text.Text' — because that is what the compiler
-- generates and what the other backends (Scheme, and a future
-- JavaScript backend) translate into a binder of their target language.
-- A tree-walking interpreter is the one backend that has to maintain a
-- per-call environment itself, and looking locals up by text there means
-- a @Text@ comparison and a @Map@ rebalance per access and per binding.
--
-- This module is that backend's private AST: the same statements and
-- expressions, with the two reference forms ('SVar', 'SIdVar') and the
-- four binding forms ('SLetVal', 'SLetId', 'SAssignVal', 'SAssignId')
-- carrying a 'Slot' instead of a 'Name'. Everything else is a direct
-- counterpart of a VM constructor, so the phase is a total, structure-
-- preserving rewrite of the program and nothing more.
--
-- == Ownership
--
-- The phase is interpreter-specific and lives in the runtime namespace
-- for that reason. The code-generation backends do not want it: they
-- emit a target-language binder per local (@let@ in Scheme, and the same
-- shape in JavaScript), where the target's own lexical addressing
-- already does what a slot does, and where the emitted identifier has to
-- be a name anyway. A future interpreter in another host language would
-- reimplement the idea in that host rather than reuse this AST.
--
-- Two properties are what keep a second consumer cheap if one ever
-- appears. The module is /pure/ — data types and total pure functions,
-- importing only the VM and shared type definitions
-- ('YCHR.Internal.VM.Types', 'YCHR.Internal.Types') and @Data.*@, never
-- the interpreter monad, an @IORef@ or IO — so lifting it into a shared
-- namespace is a rename with no code change; and the mapping is total,
-- so it can be applied to any 'Program' without a failure mode. See
-- @dev-docs/PROJECT.md@ and @dev-docs/INVARIANTS.md@.
--
-- == The mirroring invariant
--
-- Every VM 'Stmt', 'ValExpr', 'BoolExpr', 'IdExpr' and 'CallArg'
-- constructor has exactly one counterpart here. Adding a constructor to
-- the VM makes this module's pattern matches non-exhaustive, which the
-- build treats as an error under @-Wall -Werror@; that is the mechanism
-- that keeps the phase from going silently stale. Extend the lowering in
-- the same change as the VM.
--
-- == Slot assignment
--
-- Slots are numbered from 0 in one counter per procedure, shared by both
-- kinds of binding, because a parameter is heterogeneous at run time:
-- "YCHR.Internal.Runtime.Interpreter" binds a call's arguments by the
-- runtime tag it is handed, so a parameter's slot number must be the
-- same whether the value lands in the value map or the id map.
--
-- Parameters take @0 .. length params - 1@ in order. Every other binder
-- takes the next free slot at the point it is reached in a left-to-right
-- walk of the body: a @let@ binding, a 'Foreach' loop variable, and the
-- variable a 'DrainReactivationQueue' binds (the compiler emits no @let@
-- for it — the interpreter's @insertId@ creates it on first write). A
-- binder always takes a fresh slot, so a re-binding shadows the earlier
-- one rather than overwriting its cell.
--
-- Shadowing is correct for emitted code because of how the compiler
-- emits: every read is preceded on its execution path by the binder this
-- walk selects for it. Names are *not* unique within a procedure —
-- @activate_c@ binds one @dropped@ per occurrence, and an equation chain
-- binds the same pattern variable once per equation — but each read sits
-- in the segment that follows its own binder, so the fresh slot is the
-- one that read should see.
--
-- One reading is an assumption on emitted code rather than a consequence
-- of the walk: an 'If' arm's binders stay in scope for the *other* arm
-- and for the statements after the 'If' (the interpreter's environment is
-- one flat map, so that is where its bindings live). No emitted 'If'
-- binds a name in its else arm — the then arm carries the rule body or
-- equation, and the else arm is either empty or the eq-dispatch
-- fallback, whose only statements are 'AssignVal's of a binder
-- introduced outside the 'If' — so no read can be resolved to one arm's
-- slot while the other arm wrote a different one. A hand-built 'Program'
-- that bound one name in both arms and read it afterwards would observe
-- the difference; this is pinned by a case in
-- @test/YCHR/Runtime/SlotsTest.hs@.
--
-- The walk is deliberately total rather than failing on a name it cannot
-- place. A reference or an assignment to a name with no binder in scope
-- gets a fresh slot that no earlier binder wrote; a reference then
-- reaches the interpreter's existing "unbound variable" runtime error
-- when it runs, exactly as it does today, instead of this pass turning a
-- recoverable error into a Haskell 'error'. (An assignment does bind its
-- slot — the interpreter's @insertVal@ inserts — so what it lacks is a
-- prior value, not a place to put one.)
module YCHR.Internal.Runtime.Slots
  ( -- * The phase
    Slot,
    SlotProgram (..),
    SlotProc (..),
    SlotStmt (..),
    SlotValExpr (..),
    SlotBoolExpr (..),
    SlotIdExpr (..),
    SlotCallArg (..),

    -- * Lowering
    lowerProgram,
    lowerProcedure,
  )
where

import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import YCHR.Internal.Types (ConstraintType, RuleId)
import YCHR.Internal.VM.Types
  ( ArgIndex,
    BoolExpr (..),
    CallArg (..),
    IdExpr (..),
    Label,
    Literal,
    Name,
    ProcKind,
    Procedure (..),
    Program (..),
    StackFrame,
    Stmt (..),
    ValExpr (..),
    historyIdsList,
  )

-- | A local-variable slot, numbered per procedure.
--
-- A bare 'Int' alias on purpose: the interpreter keys 'Data.IntMap.Strict'
-- by it, and the precision of the phase comes from this module's own
-- types, not from making the key a newtype the maps would have to unwrap.
type Slot = Int

-- ---------------------------------------------------------------------------
-- The phase
-- ---------------------------------------------------------------------------

-- | A whole program in slot form.
newtype SlotProgram = SlotProgram
  { -- | The phase's procedures, keyed by name — the lookup table the
    -- interpreter runs against. Same keys as the VM program's procedure
    -- list, so a name that resolves there resolves here.
    slotProcedures :: Map Name SlotProc
  }
  deriving (Show, Eq)

-- | A procedure in slot form.
data SlotProc = SlotProc
  { -- | How many arguments the procedure takes. Parameters occupy slots
    -- @0 .. slotProcArity - 1@, so this is also the first slot a local
    -- can be bound to and all the interpreter needs for its arity check.
    --
    -- There is deliberately no procedure name here: the interpreter
    -- holds these keyed by name and resolves a call by the name it is
    -- calling with, which is the same one for diagnostics.
    slotProcArity :: !Int,
    slotProcBody :: [SlotStmt],
    -- | Structural classification, carried through unchanged so the
    -- tracer keeps labelling events off it.
    slotProcKind :: ProcKind
  }
  deriving (Show, Eq)

-- | Statements, with every local variable reference resolved to a slot.
data SlotStmt
  = SLetVal Slot SlotValExpr
  | SLetId Slot SlotIdExpr
  | SAssignVal Slot SlotValExpr
  | SAssignId Slot SlotIdExpr
  | SIf SlotBoolExpr [SlotStmt] [SlotStmt]
  | SForeach Label ConstraintType Slot [(ArgIndex, SlotValExpr)] [SlotStmt]
  | SContinue Label
  | SBreak Label
  | SReturn SlotValExpr
  | SExprStmt SlotValExpr
  | SBoolExprStmt SlotBoolExpr
  | SStore SlotIdExpr
  | SKill SlotIdExpr
  | SAddHistory RuleId [SlotIdExpr]
  | SDrainReactivationQueue Slot [SlotStmt]
  | SPushFrame StackFrame
  deriving (Show, Eq)

-- | Value-producing expressions, with local references slot-resolved.
--
-- 'SVar' carries the source 'Name' next to the slot for one reason
-- only: the interpreter's "unbound variable" message names it, and that
-- message is part of the runtime's contract. It is read on the failure
-- path and nowhere else.
data SlotValExpr
  = SVar Slot Name
  | SLit Literal
  | SCallExpr Name [SlotCallArg]
  | SHostCall Name [SlotValExpr]
  | SEvalDeep SlotValExpr
  | SApplyClosure SlotValExpr [SlotValExpr]
  | SEvalIs SlotValExpr
  | SNewVar
  | SMakeTerm Name [SlotValExpr]
  | SGetArg SlotValExpr Int
  | SFieldArg SlotIdExpr ArgIndex
  | SFieldType SlotIdExpr
  deriving (Show, Eq)

-- | Boolean-producing expressions, with local references slot-resolved.
data SlotBoolExpr
  = SBLit Bool
  | SBNot SlotBoolExpr
  | SBAnd SlotBoolExpr SlotBoolExpr
  | SBOr SlotBoolExpr SlotBoolExpr
  | SBMatchTerm SlotValExpr Name Int
  | SBEqual SlotValExpr SlotValExpr
  | SBIdEqual SlotIdExpr SlotIdExpr
  | SBAlive SlotIdExpr
  | SBIsConstraintType SlotIdExpr ConstraintType
  | SBNotInHistory RuleId [SlotIdExpr]
  | SBUnify SlotValExpr SlotValExpr
  | SBFromVal SlotValExpr
  | SBEvalDeep SlotBoolExpr
  | SBSoftGuard SlotBoolExpr
  deriving (Show, Eq)

-- | Constraint-identifier-producing expressions.
data SlotIdExpr
  = SIdVar Slot Name
  | SCreateConstraint ConstraintType [SlotValExpr]
  deriving (Show, Eq)

-- | Procedure-call argument in slot form.
data SlotCallArg
  = SCallVal SlotValExpr
  | SCallId SlotIdExpr
  deriving (Show, Eq)

-- ---------------------------------------------------------------------------
-- Lowering
-- ---------------------------------------------------------------------------

-- | Lower a whole program. The map spine is built eagerly — so a session
-- has a lookup table to index — but each procedure's body stays a thunk
-- until that procedure is first called, which is why this can be a lazy
-- field on a compiled program without costing anything on a short goal.
lowerProgram :: Program -> SlotProgram
lowerProgram prog =
  SlotProgram (Map.fromList [(p.name, lowerProcedure p) | p <- prog.procedures])

-- | Lower one procedure: parameters take the first slots, then every
-- binder in the body takes the next one.
lowerProcedure :: Procedure -> SlotProc
lowerProcedure proc =
  let initialScope = Map.fromList (zip proc.params [0 ..])
      body = fst (lowerStmts (Walker (length proc.params) initialScope) proc.body)
   in SlotProc
        { slotProcArity = length proc.params,
          slotProcBody = body,
          slotProcKind = proc.procKind
        }

-- | The walk's state: the next free slot, and the slot each name in
-- scope is bound to.
data Walker = Walker
  { nextSlot :: !Int,
    scope :: Map Name Slot
  }

-- | The slot a name is already bound to, or a fresh one that nothing
-- will bind (see the module header on totality).
slotOf :: Walker -> Name -> (Slot, Walker)
slotOf w name = case Map.lookup name w.scope of
  Just s -> (s, w)
  Nothing -> let s = w.nextSlot in (s, w {nextSlot = s + 1, scope = Map.insert name s w.scope})

-- | Bind a name to a fresh slot, shadowing any earlier binding.
bindName :: Walker -> Name -> (Slot, Walker)
bindName w name =
  let s = w.nextSlot
   in (s, w {nextSlot = s + 1, scope = Map.insert name s w.scope})

-- | Walk a statement list left to right. Bindings made by earlier
-- statements are visible to later ones, matching the interpreter's
-- single mutable environment; nested blocks see them too.
lowerStmts :: Walker -> [Stmt] -> ([SlotStmt], Walker)
lowerStmts w0 = go w0 []
  where
    go w acc [] = (reverse acc, w)
    go w acc (stmt : rest) =
      let (stmt', w') = lowerStmt w stmt
       in go w' (stmt' : acc) rest

lowerStmt :: Walker -> Stmt -> (SlotStmt, Walker)
lowerStmt w = \case
  LetVal name expr ->
    let (expr', w1) = lowerValExpr w expr
        (slot, w2) = bindName w1 name
     in (SLetVal slot expr', w2)
  LetId name expr ->
    let (expr', w1) = lowerIdExpr w expr
        (slot, w2) = bindName w1 name
     in (SLetId slot expr', w2)
  AssignVal name expr ->
    let (expr', w1) = lowerValExpr w expr
        (slot, w2) = slotOf w1 name
     in (SAssignVal slot expr', w2)
  AssignId name expr ->
    let (expr', w1) = lowerIdExpr w expr
        (slot, w2) = slotOf w1 name
     in (SAssignId slot expr', w2)
  If cond thenBranch elseBranch ->
    let (cond', w1) = lowerBoolExpr w cond
        (then', w2) = lowerStmts w1 thenBranch
        (else', w3) = lowerStmts w2 elseBranch
     in (SIf cond' then' else', w3)
  Foreach lbl cType suspVar conditions body ->
    let (conditions', w1) = lowerConditions w conditions
        (slot, w2) = bindName w1 suspVar
        (body', w3) = lowerStmts w2 body
     in (SForeach lbl cType slot conditions' body', w3)
  Continue lbl -> (SContinue lbl, w)
  Break lbl -> (SBreak lbl, w)
  Return expr -> let (expr', w1) = lowerValExpr w expr in (SReturn expr', w1)
  ExprStmt expr -> let (expr', w1) = lowerValExpr w expr in (SExprStmt expr', w1)
  BoolExprStmt expr -> let (expr', w1) = lowerBoolExpr w expr in (SBoolExprStmt expr', w1)
  Store expr -> let (expr', w1) = lowerIdExpr w expr in (SStore expr', w1)
  Kill expr -> let (expr', w1) = lowerIdExpr w expr in (SKill expr', w1)
  AddHistory ruleId ids ->
    let (ids', w1) = lowerIdExprs w (historyIdsList ids)
     in (SAddHistory ruleId ids', w1)
  DrainReactivationQueue suspVar body ->
    -- The compiler emits no binder for this variable; the interpreter
    -- creates it on the first queue entry, so the phase binds it here.
    -- If the name is already in scope the existing slot is the one the
    -- interpreter would write to.
    let (slot, w1) = slotOf w suspVar
        (body', w2) = lowerStmts w1 body
     in (SDrainReactivationQueue slot body', w2)
  PushFrame frame -> (SPushFrame frame, w)

lowerConditions :: Walker -> [(ArgIndex, ValExpr)] -> ([(ArgIndex, SlotValExpr)], Walker)
lowerConditions w0 = go w0 []
  where
    go w acc [] = (reverse acc, w)
    go w acc ((idx, expr) : rest) =
      let (expr', w') = lowerValExpr w expr
       in go w' ((idx, expr') : acc) rest

lowerValExpr :: Walker -> ValExpr -> (SlotValExpr, Walker)
lowerValExpr w = \case
  Var name -> let (slot, w') = slotOf w name in (SVar slot name, w')
  Lit lit -> (SLit lit, w)
  CallExpr name args -> let (args', w') = lowerCallArgs w args in (SCallExpr name args', w')
  HostCall name args -> let (args', w') = lowerValExprs w args in (SHostCall name args', w')
  EvalDeep expr -> let (expr', w') = lowerValExpr w expr in (SEvalDeep expr', w')
  ApplyClosure f args ->
    let (f', w1) = lowerValExpr w f
        (args', w2) = lowerValExprs w1 args
     in (SApplyClosure f' args', w2)
  EvalIs expr -> let (expr', w') = lowerValExpr w expr in (SEvalIs expr', w')
  NewVar -> (SNewVar, w)
  MakeTerm functor args ->
    let (args', w') = lowerValExprs w args in (SMakeTerm functor args', w')
  GetArg expr idx -> let (expr', w') = lowerValExpr w expr in (SGetArg expr' idx, w')
  FieldArg expr idx -> let (expr', w') = lowerIdExpr w expr in (SFieldArg expr' idx, w')
  FieldType expr -> let (expr', w') = lowerIdExpr w expr in (SFieldType expr', w')

lowerValExprs :: Walker -> [ValExpr] -> ([SlotValExpr], Walker)
lowerValExprs w0 = go w0 []
  where
    go w acc [] = (reverse acc, w)
    go w acc (expr : rest) =
      let (expr', w') = lowerValExpr w expr
       in go w' (expr' : acc) rest

lowerBoolExpr :: Walker -> BoolExpr -> (SlotBoolExpr, Walker)
lowerBoolExpr w = \case
  BLit b -> (SBLit b, w)
  BNot expr -> let (expr', w') = lowerBoolExpr w expr in (SBNot expr', w')
  BAnd l r ->
    let (l', w1) = lowerBoolExpr w l
        (r', w2) = lowerBoolExpr w1 r
     in (SBAnd l' r', w2)
  BOr l r ->
    let (l', w1) = lowerBoolExpr w l
        (r', w2) = lowerBoolExpr w1 r
     in (SBOr l' r', w2)
  BMatchTerm expr functor arity ->
    let (expr', w') = lowerValExpr w expr in (SBMatchTerm expr' functor arity, w')
  BEqual l r ->
    let (l', w1) = lowerValExpr w l
        (r', w2) = lowerValExpr w1 r
     in (SBEqual l' r', w2)
  BIdEqual l r ->
    let (l', w1) = lowerIdExpr w l
        (r', w2) = lowerIdExpr w1 r
     in (SBIdEqual l' r', w2)
  BAlive expr -> let (expr', w') = lowerIdExpr w expr in (SBAlive expr', w')
  BIsConstraintType expr cType ->
    let (expr', w') = lowerIdExpr w expr in (SBIsConstraintType expr' cType, w')
  BNotInHistory ruleId ids ->
    let (ids', w') = lowerIdExprs w (historyIdsList ids)
     in (SBNotInHistory ruleId ids', w')
  BUnify l r ->
    let (l', w1) = lowerValExpr w l
        (r', w2) = lowerValExpr w1 r
     in (SBUnify l' r', w2)
  BFromVal expr -> let (expr', w') = lowerValExpr w expr in (SBFromVal expr', w')
  BEvalDeep expr -> let (expr', w') = lowerBoolExpr w expr in (SBEvalDeep expr', w')
  BSoftGuard expr -> let (expr', w') = lowerBoolExpr w expr in (SBSoftGuard expr', w')

lowerIdExpr :: Walker -> IdExpr -> (SlotIdExpr, Walker)
lowerIdExpr w = \case
  IdVar name -> let (slot, w') = slotOf w name in (SIdVar slot name, w')
  CreateConstraint cType args ->
    let (args', w') = lowerValExprs w args
     in (SCreateConstraint cType args', w')

lowerIdExprs :: Walker -> [IdExpr] -> ([SlotIdExpr], Walker)
lowerIdExprs w0 = go w0 []
  where
    go w acc [] = (reverse acc, w)
    go w acc (expr : rest) =
      let (expr', w') = lowerIdExpr w expr
       in go w' (expr' : acc) rest

lowerCallArgs :: Walker -> [CallArg] -> ([SlotCallArg], Walker)
lowerCallArgs w0 = go w0 []
  where
    go w acc [] = (reverse acc, w)
    go w acc (arg : rest) = case arg of
      AVal expr ->
        let (expr', w') = lowerValExpr w expr
         in go w' (SCallVal expr' : acc) rest
      AId expr ->
        let (expr', w') = lowerIdExpr w expr
         in go w' (SCallId expr' : acc) rest
