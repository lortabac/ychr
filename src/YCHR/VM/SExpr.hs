{-# LANGUAGE OverloadedStrings #-}

-- | Serialization and deserialization of VM programs as s-expressions.
--
-- The s-expression format uses kebab-case identifiers that mirror the
-- Haskell VM constructors.  This format is designed for consumption by
-- external backends (Erlang, Python, Clojure, etc.) and as a
-- compilation cache artifact.
--
-- Example:
--
-- @
-- (program 1
--   (procedure "tell_leq" ("X" "Y")
--     (let "id" (create-constraint 0 (var "X") (var "Y")))
--     (store (var "id"))
--     (expr-stmt (call-expr "activate_leq" (var "id")))))
-- @
module YCHR.VM.SExpr
  ( -- * VMProgram
    VMProgram (..),

    -- * High-level API
    serialize,
    deserialize,

    -- * Low-level API
    programToSExpr,
    programFromSExpr,
  )
where

import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as T
import YCHR.SExpr (SExpr (..), parseSExpr, printSExpr)
import YCHR.Types qualified as Types
import YCHR.VM.Types

-- ---------------------------------------------------------------------------
-- VMProgram
-- ---------------------------------------------------------------------------

-- | A VM program bundled with metadata needed by external backends.
data VMProgram = VMProgram
  { program :: Program,
    exportedSet :: Set Types.Identifier,
    symbolTable :: Types.SymbolTable
  }
  deriving (Show, Eq)

-- ---------------------------------------------------------------------------
-- High-level API
-- ---------------------------------------------------------------------------

-- | Serialize a VM program to s-expression text.
serialize :: VMProgram -> Text
serialize = printSExpr . vmProgramToSExpr

-- | Deserialize a VM program from s-expression text.
deserialize :: Text -> Either Text VMProgram
deserialize input = case parseSExpr input of
  Left e -> Left (T.pack e)
  Right sexpr -> vmProgramFromSExpr sexpr

-- ---------------------------------------------------------------------------
-- Serialization (VM → SExpr)
-- ---------------------------------------------------------------------------

vmProgramToSExpr :: VMProgram -> SExpr
vmProgramToSExpr vmp =
  SList
    [ SAtom "vm-program",
      programToSExpr vmp.program,
      SList (SAtom "exports" : map identToSExpr (Set.toAscList vmp.exportedSet)),
      symbolTableToSExpr vmp.symbolTable
    ]

symbolTableToSExpr :: Types.SymbolTable -> SExpr
symbolTableToSExpr st =
  SList (SAtom "symbol-table" : map entryToSExpr (Types.symbolTableToList st))
  where
    entryToSExpr (Types.Identifier n arity, Types.ConstraintType ct) = SList [chrNameToSExpr n, SInt arity, SInt ct]

identToSExpr :: Types.Identifier -> SExpr
identToSExpr (Types.Identifier n arity) = SList [chrNameToSExpr n, SInt arity]

chrNameToSExpr :: Types.Name -> SExpr
chrNameToSExpr (Types.Unqualified t) = SString t
chrNameToSExpr (Types.Qualified m t) = SList [SAtom "qualified", SString m, SString t]

programToSExpr :: Program -> SExpr
programToSExpr prog =
  SList (SAtom "program" : SInt prog.numTypes : map procedureToSExpr prog.procedures)

procedureToSExpr :: Procedure -> SExpr
procedureToSExpr proc =
  SList
    ( SAtom "procedure"
        : SString proc.name.unName
        : SList (map nameToSExpr proc.params)
        : map stmtToSExpr proc.body
    )

stmtToSExpr :: Stmt -> SExpr
stmtToSExpr (Let n e) = SList [SAtom "let", nameToSExpr n, exprToSExpr e]
stmtToSExpr (Assign n e) = SList [SAtom "assign", nameToSExpr n, exprToSExpr e]
stmtToSExpr (If c ts es) =
  SList [SAtom "if", exprToSExpr c, SList (map stmtToSExpr ts), SList (map stmtToSExpr es)]
stmtToSExpr (Foreach lbl ct sv conds body) =
  SList
    [ SAtom "foreach",
      labelToSExpr lbl,
      constraintTypeToSExpr ct,
      nameToSExpr sv,
      SList [SList [SInt i, exprToSExpr e] | (ArgIndex i, e) <- conds],
      SList (map stmtToSExpr body)
    ]
stmtToSExpr (Continue lbl) = SList [SAtom "continue", labelToSExpr lbl]
stmtToSExpr (Break lbl) = SList [SAtom "break", labelToSExpr lbl]
stmtToSExpr (Return e) = SList [SAtom "return", exprToSExpr e]
stmtToSExpr (ExprStmt e) = SList [SAtom "expr-stmt", exprToSExpr e]
stmtToSExpr (Store e) = SList [SAtom "store", exprToSExpr e]
stmtToSExpr (Kill e) = SList [SAtom "kill", exprToSExpr e]
stmtToSExpr (AddHistory rn es) =
  SList (SAtom "add-history" : ruleNameToSExpr rn : map exprToSExpr es)
stmtToSExpr (DrainReactivationQueue sv body) =
  SList (SAtom "drain-reactivation-queue" : nameToSExpr sv : map stmtToSExpr body)

exprToSExpr :: Expr -> SExpr
exprToSExpr (Var n) = SList [SAtom "var", nameToSExpr n]
exprToSExpr (Lit l) = literalToSExpr l
exprToSExpr (CallExpr n es) = SList (SAtom "call-expr" : nameToSExpr n : map exprToSExpr es)
exprToSExpr (HostCall n es) = SList (SAtom "host-call" : nameToSExpr n : map exprToSExpr es)
exprToSExpr (HostEval e) = SList [SAtom "host-eval", exprToSExpr e]
exprToSExpr (Not e) = SList [SAtom "not", exprToSExpr e]
exprToSExpr (And a b) = SList [SAtom "and", exprToSExpr a, exprToSExpr b]
exprToSExpr (Or a b) = SList [SAtom "or", exprToSExpr a, exprToSExpr b]
exprToSExpr NewVar = SAtom "new-var"
exprToSExpr (MakeTerm n es) = SList (SAtom "make-term" : nameToSExpr n : map exprToSExpr es)
exprToSExpr (MatchTerm e n a) = SList [SAtom "match-term", exprToSExpr e, nameToSExpr n, SInt a]
exprToSExpr (GetArg e i) = SList [SAtom "get-arg", exprToSExpr e, SInt i]
exprToSExpr (CreateConstraint ct es) =
  SList (SAtom "create-constraint" : constraintTypeToSExpr ct : map exprToSExpr es)
exprToSExpr (Alive e) = SList [SAtom "alive", exprToSExpr e]
exprToSExpr (IdEqual a b) = SList [SAtom "id-equal", exprToSExpr a, exprToSExpr b]
exprToSExpr (IsConstraintType e ct) =
  SList [SAtom "is-constraint-type", exprToSExpr e, constraintTypeToSExpr ct]
exprToSExpr (NotInHistory rn es) =
  SList (SAtom "not-in-history" : ruleNameToSExpr rn : map exprToSExpr es)
exprToSExpr (Unify a b) = SList [SAtom "unify", exprToSExpr a, exprToSExpr b]
exprToSExpr (Equal a b) = SList [SAtom "equal", exprToSExpr a, exprToSExpr b]
exprToSExpr (FieldGet e f) = SList [SAtom "field-get", exprToSExpr e, fieldToSExpr f]

literalToSExpr :: Literal -> SExpr
literalToSExpr (IntLit n) = SList [SAtom "int", SInt n]
literalToSExpr (AtomLit s) = SList [SAtom "atom", SString s]
literalToSExpr (TextLit s) = SList [SAtom "text", SString s]
literalToSExpr (BoolLit True) = SAtom "true"
literalToSExpr (BoolLit False) = SAtom "false"
literalToSExpr WildcardLit = SAtom "wildcard"

fieldToSExpr :: Field -> SExpr
fieldToSExpr FieldId = SAtom "field-id"
fieldToSExpr (FieldArg (ArgIndex i)) = SList [SAtom "field-arg", SInt i]
fieldToSExpr FieldType = SAtom "field-type"

nameToSExpr :: Name -> SExpr
nameToSExpr (Name t) = SString t

labelToSExpr :: Label -> SExpr
labelToSExpr (Label t) = SString t

ruleNameToSExpr :: RuleName -> SExpr
ruleNameToSExpr (RuleName t) = SString t

constraintTypeToSExpr :: ConstraintType -> SExpr
constraintTypeToSExpr (ConstraintType n) = SInt n

-- ---------------------------------------------------------------------------
-- Deserialization (SExpr → VM)
-- ---------------------------------------------------------------------------

type Err a = Either Text a

err :: Text -> Err a
err = Left

vmProgramFromSExpr :: SExpr -> Err VMProgram
vmProgramFromSExpr (SList [SAtom "vm-program", progS, SList (SAtom "exports" : exportSexprs), stS]) = do
  prog <- programFromSExpr progS
  exports <- traverse identFromSExpr exportSexprs
  st <- symbolTableFromSExpr stS
  pure VMProgram {program = prog, exportedSet = Set.fromList exports, symbolTable = st}
vmProgramFromSExpr s = err ("expected (vm-program ...), got: " <> printSExpr s)

symbolTableFromSExpr :: SExpr -> Err Types.SymbolTable
symbolTableFromSExpr (SList (SAtom "symbol-table" : entries)) = do
  pairs <- traverse entryFromSExpr entries
  pure (Types.mkSymbolTable pairs)
  where
    entryFromSExpr (SList [n, SInt arity, SInt ct]) = do
      name <- chrNameFromSExpr n
      pure (Types.Identifier name arity, Types.ConstraintType ct)
    entryFromSExpr s = err ("expected (name arity int), got: " <> printSExpr s)
symbolTableFromSExpr s = err ("expected (symbol-table ...), got: " <> printSExpr s)

identFromSExpr :: SExpr -> Err Types.Identifier
identFromSExpr (SList [n, SInt arity]) = do
  name <- chrNameFromSExpr n
  pure (Types.Identifier name arity)
identFromSExpr s = err ("expected (name arity), got: " <> printSExpr s)

chrNameFromSExpr :: SExpr -> Err Types.Name
chrNameFromSExpr (SString t) = pure (Types.Unqualified t)
chrNameFromSExpr (SList [SAtom "qualified", SString m, SString t]) = pure (Types.Qualified m t)
chrNameFromSExpr s = err ("expected name, got: " <> printSExpr s)

programFromSExpr :: SExpr -> Err Program
programFromSExpr (SList (SAtom "program" : SInt n : procs)) = do
  ps <- traverse procedureFromSExpr procs
  pure Program {numTypes = n, procedures = ps}
programFromSExpr s = err ("expected (program ...), got: " <> printSExpr s)

procedureFromSExpr :: SExpr -> Err Procedure
procedureFromSExpr (SList (SAtom "procedure" : SString nm : SList paramSexprs : bodyExprs)) = do
  params' <- traverse nameFromSExpr paramSexprs
  body' <- traverse stmtFromSExpr bodyExprs
  pure Procedure {name = Name nm, params = params', body = body'}
procedureFromSExpr s = err ("expected (procedure ...), got: " <> printSExpr s)

stmtFromSExpr :: SExpr -> Err Stmt
stmtFromSExpr (SList [SAtom "let", n, e]) = Let <$> nameFromSExpr n <*> exprFromSExpr e
stmtFromSExpr (SList [SAtom "assign", n, e]) = Assign <$> nameFromSExpr n <*> exprFromSExpr e
stmtFromSExpr (SList [SAtom "if", c, SList ts, SList es]) =
  If <$> exprFromSExpr c <*> traverse stmtFromSExpr ts <*> traverse stmtFromSExpr es
stmtFromSExpr (SList [SAtom "foreach", lbl, ct, sv, SList conds, SList body]) =
  Foreach
    <$> labelFromSExpr lbl
    <*> constraintTypeFromSExpr ct
    <*> nameFromSExpr sv
    <*> traverse condFromSExpr conds
    <*> traverse stmtFromSExpr body
stmtFromSExpr (SList [SAtom "continue", lbl]) = Continue <$> labelFromSExpr lbl
stmtFromSExpr (SList [SAtom "break", lbl]) = Break <$> labelFromSExpr lbl
stmtFromSExpr (SList [SAtom "return", e]) = Return <$> exprFromSExpr e
stmtFromSExpr (SList [SAtom "expr-stmt", e]) = ExprStmt <$> exprFromSExpr e
stmtFromSExpr (SList [SAtom "store", e]) = Store <$> exprFromSExpr e
stmtFromSExpr (SList [SAtom "kill", e]) = Kill <$> exprFromSExpr e
stmtFromSExpr (SList (SAtom "add-history" : rn : es)) =
  AddHistory <$> ruleNameFromSExpr rn <*> traverse exprFromSExpr es
stmtFromSExpr (SList (SAtom "drain-reactivation-queue" : sv : body)) =
  DrainReactivationQueue <$> nameFromSExpr sv <*> traverse stmtFromSExpr body
stmtFromSExpr s = err ("expected statement, got: " <> printSExpr s)

exprFromSExpr :: SExpr -> Err Expr
exprFromSExpr (SList [SAtom "var", n]) = Var <$> nameFromSExpr n
exprFromSExpr (SList [SAtom "int", SInt n]) = pure (Lit (IntLit n))
exprFromSExpr (SList [SAtom "atom", SString s]) = pure (Lit (AtomLit s))
exprFromSExpr (SList [SAtom "text", SString s]) = pure (Lit (TextLit s))
exprFromSExpr (SAtom "true") = pure (Lit (BoolLit True))
exprFromSExpr (SAtom "false") = pure (Lit (BoolLit False))
exprFromSExpr (SAtom "wildcard") = pure (Lit WildcardLit)
exprFromSExpr (SList (SAtom "call-expr" : n : es)) =
  CallExpr <$> nameFromSExpr n <*> traverse exprFromSExpr es
exprFromSExpr (SList (SAtom "host-call" : n : es)) =
  HostCall <$> nameFromSExpr n <*> traverse exprFromSExpr es
exprFromSExpr (SList [SAtom "host-eval", e]) = HostEval <$> exprFromSExpr e
exprFromSExpr (SList [SAtom "not", e]) = Not <$> exprFromSExpr e
exprFromSExpr (SList [SAtom "and", a, b]) = And <$> exprFromSExpr a <*> exprFromSExpr b
exprFromSExpr (SList [SAtom "or", a, b]) = Or <$> exprFromSExpr a <*> exprFromSExpr b
exprFromSExpr (SAtom "new-var") = pure NewVar
exprFromSExpr (SList (SAtom "make-term" : n : es)) =
  MakeTerm <$> nameFromSExpr n <*> traverse exprFromSExpr es
exprFromSExpr (SList [SAtom "match-term", e, n, SInt a]) =
  MatchTerm <$> exprFromSExpr e <*> nameFromSExpr n <*> pure a
exprFromSExpr (SList [SAtom "get-arg", e, SInt i]) =
  GetArg <$> exprFromSExpr e <*> pure i
exprFromSExpr (SList (SAtom "create-constraint" : ct : es)) =
  CreateConstraint <$> constraintTypeFromSExpr ct <*> traverse exprFromSExpr es
exprFromSExpr (SList [SAtom "alive", e]) = Alive <$> exprFromSExpr e
exprFromSExpr (SList [SAtom "id-equal", a, b]) =
  IdEqual <$> exprFromSExpr a <*> exprFromSExpr b
exprFromSExpr (SList [SAtom "is-constraint-type", e, ct]) =
  IsConstraintType <$> exprFromSExpr e <*> constraintTypeFromSExpr ct
exprFromSExpr (SList (SAtom "not-in-history" : rn : es)) =
  NotInHistory <$> ruleNameFromSExpr rn <*> traverse exprFromSExpr es
exprFromSExpr (SList [SAtom "unify", a, b]) = Unify <$> exprFromSExpr a <*> exprFromSExpr b
exprFromSExpr (SList [SAtom "equal", a, b]) = Equal <$> exprFromSExpr a <*> exprFromSExpr b
exprFromSExpr (SList [SAtom "field-get", e, f]) = FieldGet <$> exprFromSExpr e <*> fieldFromSExpr f
exprFromSExpr s = err ("expected expression, got: " <> printSExpr s)

fieldFromSExpr :: SExpr -> Err Field
fieldFromSExpr (SAtom "field-id") = pure FieldId
fieldFromSExpr (SList [SAtom "field-arg", SInt i]) = pure (FieldArg (ArgIndex i))
fieldFromSExpr (SAtom "field-type") = pure FieldType
fieldFromSExpr s = err ("expected field, got: " <> printSExpr s)

condFromSExpr :: SExpr -> Err (ArgIndex, Expr)
condFromSExpr (SList [SInt i, e]) = (ArgIndex i,) <$> exprFromSExpr e
condFromSExpr s = err ("expected (index expr), got: " <> printSExpr s)

nameFromSExpr :: SExpr -> Err Name
nameFromSExpr (SString t) = pure (Name t)
nameFromSExpr s = err ("expected string (name), got: " <> printSExpr s)

labelFromSExpr :: SExpr -> Err Label
labelFromSExpr (SString t) = pure (Label t)
labelFromSExpr s = err ("expected string (label), got: " <> printSExpr s)

ruleNameFromSExpr :: SExpr -> Err RuleName
ruleNameFromSExpr (SString t) = pure (RuleName t)
ruleNameFromSExpr s = err ("expected string (rule name), got: " <> printSExpr s)

constraintTypeFromSExpr :: SExpr -> Err ConstraintType
constraintTypeFromSExpr (SInt n) = pure (ConstraintType n)
constraintTypeFromSExpr s = err ("expected int (constraint type), got: " <> printSExpr s)
