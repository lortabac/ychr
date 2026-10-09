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
-- carrying a 'Slot' instead of a 'Name', and a 'CallExpr' carrying a
-- 'CallTarget' that 'lowerProgram' resolves to a 'ProcIx' where it can.
-- Everything else is a direct counterpart of a VM constructor, so the
-- phase is a total, structure-preserving rewrite of the program and
-- nothing more.
--
-- == Ownership
--
-- The phase is owned by the Haskell interpreter and lives in the
-- interpreter's namespace ('YCHR.Internal.Interpreter') for that reason:
-- it is neither runtime machinery — it imports no monad, no @IORef@ and
-- no IO, and knows nothing about a session, a store or a trail — nor
-- part of the target-independent VM IR that "YCHR.Internal.VM" holds,
-- because the code-generation backends do not want it. They emit a
-- target-language binder per local (@let@ in Scheme, and the same shape
-- in JavaScript), where the target's own lexical addressing already does
-- what a slot does, and where the emitted identifier has to be a name
-- anyway. A future interpreter in another host language would
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
-- The one place the phase adds rather than mirrors is the callee of a
-- 'CallExpr': the VM names it, and 'lowerProgram' resolves that name to
-- the position of the callee in the program's procedure list
-- ('CallTarget'). The name survives only as the fallback for a target
-- no procedure of the program declares, which compiler output never
-- produces ("YCHR.Internal.VM.Closure" asserts it) but a hand-built
-- 'Program' may.
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
-- @test/YCHR/Interpreter/SlotsTest.hs@.
--
-- The walk is deliberately total rather than failing on a name it cannot
-- place. A reference or an assignment to a name with no binder in scope
-- gets a fresh slot that no earlier binder wrote; a reference then
-- reaches the interpreter's existing "unbound variable" runtime error
-- when it runs, exactly as it does today, instead of this pass turning a
-- recoverable error into a Haskell 'error'. (An assignment does bind its
-- slot — the interpreter's @insertVal@ inserts — so what it lacks is a
-- prior value, not a place to put one.)
module YCHR.Internal.Interpreter.Slots
  ( -- * The phase
    Slot,
    ProcIx (..),
    CallTarget (..),
    SlotProgram (..),
    SlotProc (..),
    SlotStmt (..),
    SlotValExpr (..),
    SlotBoolExpr (..),
    SlotIdExpr (..),
    SlotCallArg (..),

    -- * Lowering
    lowerProgram,
    addProcedures,
    emptySlotProgram,
  )
where

import Data.Array (Array, bounds, elems, listArray)
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

-- | A procedure index: the position of a procedure in its program's
-- procedure list ('Program.procedures'), which is what a resolved
-- 'CallTarget' carries.
--
-- A newtype rather than the bare 'Int' @Slot@ is: a local slot and a
-- procedure index are both integer keys — the slot goes into the
-- interpreter's @Env@ 'Data.IntMap.Strict's, the index into its entry
-- array — and only the type keeps one from being written where the
-- other belongs.
newtype ProcIx = ProcIx {unProcIx :: Int}
  deriving (Show, Eq, Ord)

-- | How a compiled call names its callee.
--
-- 'ProcIndex' is the resolver's answer for an emitted call: the callee
-- is a procedure of the same program, so the interpreter reaches it by
-- index instead of by a 'Map' lookup over 'Name' with its 'Data.Text'
-- comparisons on every call.
--
-- 'ProcName' is the fallback for a target no procedure of the program
-- declares. Compiler output never produces one — `lowerProgram` is
-- where the compiler's calls are resolved, and
-- "YCHR.Internal.VM.Closure" asserts the closure of what it emits
-- before the program is built — but a hand-built 'Program' passed to
-- 'YCHR.Internal.Runtime.Interpreter.interpret' may, and that keeps the
-- interpreter's existing @unknown procedure@ runtime error.
data CallTarget
  = ProcIndex !ProcIx
  | ProcName !Name
  deriving (Show, Eq)

-- | A whole program in slot form.
data SlotProgram = SlotProgram
  { -- | The phase's procedures, keyed by name — the lookup table the
    -- interpreter's name-based entry points run against (a query's
    -- @tell_\<c\>@, reactivation dispatch, @'$call'@ and @is@ dispatch,
    -- and the interpreter's own 'interpret' entry). Same keys as the VM
    -- program's procedure list, so a name that resolves there resolves
    -- here.
    --
    -- This is also the map the walk resolves emitted call targets
    -- through: a callee's index is a field on its 'SlotProc', so there
    -- is no second name-keyed map to build.
    slotProcedures :: Map Name SlotProc,
    -- | The program's procedures in the order of its procedure list and
    -- indexed @0 .. n - 1@: the table a resolved 'CallTarget' reads.
    -- 'slotProcedures' is the name-keyed view of the same list, with
    -- one difference a duplicated name produces: the map keeps the last
    -- procedure of that name, while the array keeps every one at its
    -- own index. An empty program has bounds @(0, -1)@, so the bounds
    -- are a dense range with no gaps, and 'addProcedures' can append at
    -- @snd (bounds arr) + 1@.
    --
    -- A boxed 'Data.Array', and deliberately so: it is the one
    -- container of the four the micro-benchmarks measured that is
    -- fastest on /both/ hosts — a constant ~89 reductions per lookup
    -- under MicroHs whatever @n@ is, against 130 to 285 for a
    -- 'Data.Map.Strict' ('Int'- or 'Data.Text.Text'-keyed) and 716 to
    -- 1186 for an @IntMap@, which MicroHs cannot inline the
    -- @Data.Bits@ work of — and under GHC it allocates nothing per
    -- lookup (micro-benchmarks in @dev-docs/MICROHS_PERFORMANCE.md@
    -- §7C.1 and item 8). The key is the unwrapped 'Int' rather than
    -- 'ProcIx' because a resolved index is read off
    -- 'SlotProc.slotProcIx' by pattern match, which costs nothing,
    -- where the newtype's derived 'Ord' would add a dispatch per
    -- comparison.
    --
    -- Boxed arrays are lazy in their elements, so the 'SlotProc's here
    -- are the same thunks 'slotProcedures' holds and no body is forced
    -- by building the array. The array is built once per program, and
    -- "YCHR.Internal.Runtime.Monad" keeps its field lazy for that
    -- reason.
    slotProcEntries :: Array Int SlotProc
  }
  deriving (Show, Eq)

-- | A procedure in slot form.
data SlotProc = SlotProc
  { -- | The procedure's name, kept for diagnostics only: the arity
    -- mismatch 'YCHR.Internal.Runtime.Interpreter.bindParams' reports,
    -- and the "stale procedure index" internal error. A resolved
    -- 'CallTarget' needs no name to reach the procedure, and the
    -- interpreter reads this field only on a failure path.
    slotProcName :: !Name,
    -- | The procedure's position in its program's procedure list: what
    -- a call to this procedure resolves to. Carried here rather than in
    -- a name-to-index map so that a program needs one name-keyed map
    -- ('slotProcedures') and one index-keyed array ('slotProcEntries'),
    -- not three.
    slotProcIx :: !ProcIx,
    -- | How many arguments the procedure takes. Parameters occupy slots
    -- @0 .. slotProcArity - 1@, so this is also the first slot a local
    -- can be bound to and all the interpreter needs for its arity check.
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

-- | Value-producing expressions, with local references slot-resolved
-- and call targets procedure-resolved.
--
-- 'SVar' carries the source 'Name' next to the slot for one reason
-- only: the interpreter's "unbound variable" message names it, and that
-- message is part of the runtime's contract. It is read on the failure
-- path and nowhere else. 'SCallExpr' carries a 'CallTarget' instead of a
-- name, so the interpreter does not pay a name lookup per call; see
-- 'CallTarget' for the fallback that keeps a hand-built program's
-- unknown-callee error.
data SlotValExpr
  = SVar Slot Name
  | SLit Literal
  | SCallExpr CallTarget [SlotCallArg]
  | SHostCall Name [SlotValExpr]
  | SEvalDeep SlotValExpr
  | SApplyClosure SlotValExpr [SlotValExpr]
  | SEvalIs SlotValExpr
  | SNewVar
  | SMakeTerm Name [SlotValExpr]
  | SGetArg SlotValExpr Word
  | SFieldArg SlotIdExpr ArgIndex
  | SFieldType SlotIdExpr
  deriving (Show, Eq)

-- | Boolean-producing expressions, with local references slot-resolved.
data SlotBoolExpr
  = SBLit Bool
  | SBNot SlotBoolExpr
  | SBAnd SlotBoolExpr SlotBoolExpr
  | SBOr SlotBoolExpr SlotBoolExpr
  | SBMatchTerm SlotValExpr Name Word
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

-- | Lower a whole program, resolving every emitted call target against
-- the program's own procedures.
--
-- The table spines are built eagerly — so a session has both lookup
-- tables to index — but each procedure's body stays a thunk until that
-- procedure is first called, which is why this can be a lazy field on a
-- compiled program without costing anything on a short goal. The
-- resolution lives in that thunk too: a body resolves the calls it
-- contains when it is first forced, not when the program is lowered.
--
-- @resolve@ and @procMap@ are mutually recursive (resolution consults
-- the map that holds the procedures being resolved), which is fine
-- because resolution happens strictly inside a body thunk: 'SlotProc'
-- forces its index and arity, never its body, so building the map never
-- demands the resolver.
lowerProgram :: Program -> SlotProgram
lowerProgram prog =
  let lowered =
        [ (i, p.name, lowerProcedureWith (ProcIx i) (resolveCallIn procMap) p)
        | (i, p) <- zip [0 ..] prog.procedures
        ]
      procMap = Map.fromList [(n, proc) | (_, n, proc) <- lowered]
   in SlotProgram
        { slotProcedures = procMap,
          slotProcEntries =
            listArray
              (0, length prog.procedures - 1)
              [proc | (_, _, proc) <- lowered]
        }

-- | Extend a lowered program with procedures compiled after it —
-- query-time lifted lambdas ('YCHR.Internal.Runtime.Session.withCHRExtra').
-- The entries the program already has keep their indices; the extras
-- take the ones after the highest index in use, so a program built by
-- 'lowerProgram' or by an earlier 'addProcedures' (whose indices are
-- @0 .. n - 1@) is extended rather than re-based. The base index is
-- @snd (bounds arr) + 1@: the entry table is a dense array, so its
-- upper bound is the last index in use, and the @O(n)@ rebuild of
-- 'elems' is paid only on this cold path — a query that lifts lambdas.
--
-- An extra may call a compiled procedure and one extra may call
-- another, so the extras are resolved against the union of both name
-- spaces — the same union 'YCHR.Internal.Runtime.Session.withCHRExtra'
-- merges into the interpreter's table. On a name collision the extras
-- shadow the compiled procedures in the name view, matching the
-- left-biased @Map.union@ that merge is; a compiled body's calls were
-- resolved when it was lowered, so they keep pointing at the compiled
-- procedure (see @dev-docs\/INVARIANTS.md@,
-- "Session construction"). Query-time lambdas are lifted under fresh
-- @__lambda_N@ names, so the collision cannot occur today.
--
-- The empty list returns the program unchanged, so a query that lifts
-- no lambda pays nothing.
addProcedures :: SlotProgram -> [Procedure] -> SlotProgram
addProcedures sp [] = sp
addProcedures sp extras =
  let base = snd (bounds sp.slotProcEntries) + 1
      lowered =
        [ (i, p.name, lowerProcedureWith (ProcIx i) (resolveCallIn merged) p)
        | (i, p) <- zip [base ..] extras
        ]
      merged =
        Map.fromList [(n, proc) | (_, n, proc) <- lowered]
          `Map.union` sp.slotProcedures
   in SlotProgram
        { slotProcedures = merged,
          slotProcEntries =
            listArray
              (0, base + length extras - 1)
              (elems sp.slotProcEntries ++ [proc | (_, _, proc) <- lowered])
        }

-- | A program with no procedures: what a hand-built session (a unit
-- test exercising primitives, which needs no compiled procedure) starts
-- from.
emptySlotProgram :: SlotProgram
emptySlotProgram = SlotProgram Map.empty (listArray (0, -1) [])

-- | The resolver 'lowerProgram' and 'addProcedures' hand the walk: a
-- name the table knows becomes the callee's index, and anything else
-- keeps its name for the interpreter's runtime error.
resolveCallIn :: Map Name SlotProc -> Name -> CallTarget
resolveCallIn procMap n = case Map.lookup n procMap of
  Just proc -> ProcIndex proc.slotProcIx
  Nothing -> ProcName n

-- | Lower one procedure: parameters take the first slots, then every
-- binder in the body takes the next one, and calls are resolved through
-- @resolveCall@.
--
-- Not exported: a 'SlotProc' carries the index its callers will reach it
-- by ('slotProcIx'), so one lowered on its own — with no position in a
-- program — would be a procedure whose index means nothing. Only
-- 'lowerProgram' and 'addProcedures', which know the position, call
-- this.
lowerProcedureWith :: ProcIx -> (Name -> CallTarget) -> Procedure -> SlotProc
lowerProcedureWith ix resolveCall proc =
  let initialScope = Map.fromList (zip proc.params [0 ..])
      body =
        fst
          ( lowerStmts
              (Walker (length proc.params) initialScope resolveCall)
              proc.body
          )
   in SlotProc
        { slotProcName = proc.name,
          slotProcIx = ix,
          slotProcArity = length proc.params,
          slotProcBody = body,
          slotProcKind = proc.procKind
        }

-- | The walk's state: the next free slot, the slot each name in
-- scope is bound to, and how to name the callee of a call.
data Walker = Walker
  { nextSlot :: !Int,
    scope :: Map Name Slot,
    resolveCall :: Name -> CallTarget
  }

-- | The slot a name is already bound to, or a fresh one that nothing
-- will bind (see the module header on totality).
slotOf :: Walker -> Name -> (Slot, Walker)
slotOf w name = case Map.lookup name w.scope of
  Just s -> (s, w)
  Nothing ->
    let s = w.nextSlot
     in (s, w {nextSlot = s + 1, scope = Map.insert name s w.scope})

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
  CallExpr name args ->
    let (args', w') = lowerCallArgs w args
     in (SCallExpr (w.resolveCall name) args', w')
  HostCall name args ->
    let (args', w') = lowerValExprs w args
     in (SHostCall name args', w')
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
