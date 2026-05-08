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
--     (let-id "id" (create-constraint 0 (var "X") (var "Y")))
--     (store (id-var "id"))
--     (expr-stmt (call-expr "activate_leq" (arg-id (id-var "id"))))))
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
import Text.Read (readMaybe)
import YCHR.Loc (SourceLoc (..))
import YCHR.SExpr (SExpr (..), parseSExpr, printSExpr)
import YCHR.Types qualified as Types
import YCHR.VM.Types

-- ---------------------------------------------------------------------------
-- VMProgram
-- ---------------------------------------------------------------------------

-- | A VM program bundled with metadata needed by external backends.
data VMProgram = VMProgram
  { program :: Program,
    exportedSet :: Set Types.QualifiedIdentifier,
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
    entryToSExpr (Types.Identifier n arity, Types.ConstraintType ct) =
      SList
        [ chrNameToSExpr n,
          SInt arity,
          SInt ct
        ]

identToSExpr :: Types.QualifiedIdentifier -> SExpr
identToSExpr (Types.QualifiedIdentifier m n arity) =
  SList
    [ chrNameToSExpr
        ( Types.Qualified
            m
            n
        ),
      SInt arity
    ]

chrNameToSExpr :: Types.Name -> SExpr
chrNameToSExpr (Types.Unqualified t) = SString t
chrNameToSExpr (Types.Qualified m t) = SList [SAtom "qualified", SString m, SString t]

programToSExpr :: Program -> SExpr
programToSExpr prog =
  SList
    ( SAtom "program"
        : SInt prog.numTypes
        : SList (SAtom "type-names" : map chrNameToSExpr prog.typeNames)
        : SInt prog.numRules
        : SList (SAtom "rule-names" : map SString prog.ruleNames)
        : map procedureToSExpr prog.procedures
    )

procedureToSExpr :: Procedure -> SExpr
procedureToSExpr proc =
  SList
    ( SAtom "procedure"
        : SString proc.name.unName
        : SList (map nameToSExpr proc.params)
        : map stmtToSExpr proc.body
    )

stmtToSExpr :: Stmt -> SExpr
stmtToSExpr (LetVal n e) = SList [SAtom "let-val", nameToSExpr n, valExprToSExpr e]
stmtToSExpr (LetId n e) = SList [SAtom "let-id", nameToSExpr n, idExprToSExpr e]
stmtToSExpr (AssignVal n e) = SList [SAtom "assign-val", nameToSExpr n, valExprToSExpr e]
stmtToSExpr (AssignId n e) = SList [SAtom "assign-id", nameToSExpr n, idExprToSExpr e]
stmtToSExpr (If c ts es) =
  SList [SAtom "if", valExprToSExpr c, SList (map stmtToSExpr ts), SList (map stmtToSExpr es)]
stmtToSExpr (Foreach lbl ct sv conds body) =
  SList
    [ SAtom "foreach",
      labelToSExpr lbl,
      constraintTypeToSExpr ct,
      nameToSExpr sv,
      SList [SList [SInt i, valExprToSExpr e] | (ArgIndex i, e) <- conds],
      SList (map stmtToSExpr body)
    ]
stmtToSExpr (Continue lbl) = SList [SAtom "continue", labelToSExpr lbl]
stmtToSExpr (Break lbl) = SList [SAtom "break", labelToSExpr lbl]
stmtToSExpr (Return e) = SList [SAtom "return", valExprToSExpr e]
stmtToSExpr (ExprStmt e) = SList [SAtom "expr-stmt", valExprToSExpr e]
stmtToSExpr (Store e) = SList [SAtom "store", idExprToSExpr e]
stmtToSExpr (Kill e) = SList [SAtom "kill", idExprToSExpr e]
stmtToSExpr (AddHistory rid es) =
  SList (SAtom "add-history" : ruleIdToSExpr rid : map idExprToSExpr es)
stmtToSExpr (DrainReactivationQueue sv body) =
  SList (SAtom "drain-reactivation-queue" : nameToSExpr sv : map stmtToSExpr body)
stmtToSExpr (PushFrame frame) =
  SList
    [ SAtom "push-frame",
      SAtom frame.frameLabel,
      SAtom (T.pack (show frame.frameSourceLoc.line)),
      SAtom (T.pack (show frame.frameSourceLoc.col)),
      SAtom (T.pack frame.frameSourceLoc.file),
      SAtom frame.frameSourceCode
    ]

valExprToSExpr :: ValExpr -> SExpr
valExprToSExpr (Var n) = SList [SAtom "var", nameToSExpr n]
valExprToSExpr (Lit l) = literalToSExpr l
valExprToSExpr (CallExpr n es) =
  SList (SAtom "call-expr" : nameToSExpr n : map callArgToSExpr es)
valExprToSExpr (HostCall n es) =
  SList (SAtom "host-call" : nameToSExpr n : map valExprToSExpr es)
valExprToSExpr (EvalDeep e) = SList [SAtom "eval-deep", valExprToSExpr e]
valExprToSExpr (Not e) = SList [SAtom "not", valExprToSExpr e]
valExprToSExpr (And a b) = SList [SAtom "and", valExprToSExpr a, valExprToSExpr b]
valExprToSExpr (Or a b) = SList [SAtom "or", valExprToSExpr a, valExprToSExpr b]
valExprToSExpr NewVar = SAtom "new-var"
valExprToSExpr (MakeTerm n es) =
  SList (SAtom "make-term" : nameToSExpr n : map valExprToSExpr es)
valExprToSExpr (MatchTerm e n a) =
  SList
    [ SAtom "match-term",
      valExprToSExpr e,
      nameToSExpr n,
      SInt a
    ]
valExprToSExpr (GetArg e i) = SList [SAtom "get-arg", valExprToSExpr e, SInt i]
valExprToSExpr (Alive e) = SList [SAtom "alive", idExprToSExpr e]
valExprToSExpr (IdEqual a b) = SList [SAtom "id-equal", idExprToSExpr a, idExprToSExpr b]
valExprToSExpr (IsConstraintType e ct) =
  SList [SAtom "is-constraint-type", idExprToSExpr e, constraintTypeToSExpr ct]
valExprToSExpr (NotInHistory rid es) =
  SList (SAtom "not-in-history" : ruleIdToSExpr rid : map idExprToSExpr es)
valExprToSExpr (Unify a b) = SList [SAtom "unify", valExprToSExpr a, valExprToSExpr b]
valExprToSExpr (Equal a b) = SList [SAtom "equal", valExprToSExpr a, valExprToSExpr b]
valExprToSExpr (FieldArg e (ArgIndex i)) =
  SList [SAtom "field-arg", idExprToSExpr e, SInt i]
valExprToSExpr (FieldType e) = SList [SAtom "field-type", idExprToSExpr e]

idExprToSExpr :: IdExpr -> SExpr
idExprToSExpr (IdVar n) = SList [SAtom "id-var", nameToSExpr n]
idExprToSExpr (CreateConstraint ct es) =
  SList (SAtom "create-constraint" : constraintTypeToSExpr ct : map valExprToSExpr es)

callArgToSExpr :: CallArg -> SExpr
callArgToSExpr (AVal e) = SList [SAtom "arg-val", valExprToSExpr e]
callArgToSExpr (AId e) = SList [SAtom "arg-id", idExprToSExpr e]

literalToSExpr :: Literal -> SExpr
literalToSExpr (IntLit n) = SList [SAtom "int", SInt n]
literalToSExpr (FloatLit n) = SList [SAtom "float", SFloat n]
literalToSExpr (AtomLit s) = SList [SAtom "atom", SString s]
literalToSExpr (TextLit s) = SList [SAtom "text", SString s]
literalToSExpr (BoolLit True) = SAtom "true"
literalToSExpr (BoolLit False) = SAtom "false"
literalToSExpr WildcardLit = SAtom "wildcard"

nameToSExpr :: Name -> SExpr
nameToSExpr (Name t) = SString t

labelToSExpr :: Label -> SExpr
labelToSExpr (Label t) = SString t

ruleIdToSExpr :: RuleId -> SExpr
ruleIdToSExpr (RuleId n) = SInt n

constraintTypeToSExpr :: ConstraintType -> SExpr
constraintTypeToSExpr (ConstraintType n) = SInt n

-- ---------------------------------------------------------------------------
-- Deserialization (SExpr → VM)
-- ---------------------------------------------------------------------------

type Err a = Either Text a

err :: Text -> Err a
err = Left

vmProgramFromSExpr :: SExpr -> Err VMProgram
vmProgramFromSExpr
  ( SList
      [ SAtom "vm-program",
        progS,
        SList (SAtom "exports" : exportSexprs),
        stS
        ]
    ) = do
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

identFromSExpr :: SExpr -> Err Types.QualifiedIdentifier
identFromSExpr (SList [n, SInt arity]) = do
  name <- chrNameFromSExpr n
  case name of
    Types.Qualified m t -> pure (Types.QualifiedIdentifier m t arity)
    Types.Unqualified t -> err ("expected qualified name in export, got: " <> t)
identFromSExpr s = err ("expected (name arity), got: " <> printSExpr s)

chrNameFromSExpr :: SExpr -> Err Types.Name
chrNameFromSExpr (SString t) = pure (Types.Unqualified t)
chrNameFromSExpr (SList [SAtom "qualified", SString m, SString t]) = pure (Types.Qualified m t)
chrNameFromSExpr s = err ("expected name, got: " <> printSExpr s)

programFromSExpr :: SExpr -> Err Program
programFromSExpr
  ( SList
      ( SAtom "program"
          : SInt n
          : SList (SAtom "type-names" : tnSexprs)
          : SInt nr
          : SList (SAtom "rule-names" : rnSexprs)
          : procs
        )
    ) = do
    tns <- traverse chrNameFromSExpr tnSexprs
    rns <- traverse textFromSExpr rnSexprs
    ps <- traverse procedureFromSExpr procs
    pure
      Program
        { numTypes = n,
          typeNames = tns,
          numRules = nr,
          ruleNames = rns,
          procedures = ps
        }
programFromSExpr s = err ("expected (program ...), got: " <> printSExpr s)

textFromSExpr :: SExpr -> Err Text
textFromSExpr (SString t) = pure t
textFromSExpr s = err ("expected name string, got: " <> printSExpr s)

procedureFromSExpr :: SExpr -> Err Procedure
procedureFromSExpr (SList (SAtom "procedure" : SString nm : SList paramSexprs : bodyExprs)) =
  do
    params' <- traverse nameFromSExpr paramSexprs
    body' <- traverse stmtFromSExpr bodyExprs
    pure Procedure {name = Name nm, params = params', body = body'}
procedureFromSExpr s = err ("expected (procedure ...), got: " <> printSExpr s)

stmtFromSExpr :: SExpr -> Err Stmt
stmtFromSExpr (SList [SAtom "let-val", n, e]) =
  LetVal <$> nameFromSExpr n <*> valExprFromSExpr e
stmtFromSExpr (SList [SAtom "let-id", n, e]) =
  LetId <$> nameFromSExpr n <*> idExprFromSExpr e
stmtFromSExpr (SList [SAtom "assign-val", n, e]) =
  AssignVal <$> nameFromSExpr n <*> valExprFromSExpr e
stmtFromSExpr (SList [SAtom "assign-id", n, e]) =
  AssignId <$> nameFromSExpr n <*> idExprFromSExpr e
stmtFromSExpr (SList [SAtom "if", c, SList ts, SList es]) =
  If <$> valExprFromSExpr c <*> traverse stmtFromSExpr ts <*> traverse stmtFromSExpr es
stmtFromSExpr (SList [SAtom "foreach", lbl, ct, sv, SList conds, SList body]) =
  Foreach
    <$> labelFromSExpr lbl
    <*> constraintTypeFromSExpr ct
    <*> nameFromSExpr sv
    <*> traverse condFromSExpr conds
    <*> traverse stmtFromSExpr body
stmtFromSExpr (SList [SAtom "continue", lbl]) = Continue <$> labelFromSExpr lbl
stmtFromSExpr (SList [SAtom "break", lbl]) = Break <$> labelFromSExpr lbl
stmtFromSExpr (SList [SAtom "return", e]) = Return <$> valExprFromSExpr e
stmtFromSExpr (SList [SAtom "expr-stmt", e]) = ExprStmt <$> valExprFromSExpr e
stmtFromSExpr (SList [SAtom "store", e]) = Store <$> idExprFromSExpr e
stmtFromSExpr (SList [SAtom "kill", e]) = Kill <$> idExprFromSExpr e
stmtFromSExpr (SList (SAtom "add-history" : rid : es)) =
  AddHistory <$> ruleIdFromSExpr rid <*> traverse idExprFromSExpr es
stmtFromSExpr (SList (SAtom "drain-reactivation-queue" : sv : body)) =
  DrainReactivationQueue <$> nameFromSExpr sv <*> traverse stmtFromSExpr body
stmtFromSExpr
  ( SList
      [ SAtom "push-frame",
        SAtom label,
        SAtom lineStr,
        SAtom colStr,
        SAtom file,
        SAtom src
        ]
    ) =
    case (readMaybe (T.unpack lineStr), readMaybe (T.unpack colStr)) of
      (Just l, Just c) ->
        pure $ PushFrame $ StackFrame label (SourceLoc (T.unpack file) l c) src
      _ -> err "push-frame: invalid line/col"
stmtFromSExpr s = err ("expected statement, got: " <> printSExpr s)

valExprFromSExpr :: SExpr -> Err ValExpr
valExprFromSExpr (SList [SAtom "var", n]) = Var <$> nameFromSExpr n
valExprFromSExpr (SList [SAtom "int", SInt n]) = pure (Lit (IntLit n))
valExprFromSExpr (SList [SAtom "float", SFloat n]) = pure (Lit (FloatLit n))
valExprFromSExpr (SList [SAtom "atom", SString s]) = pure (Lit (AtomLit s))
valExprFromSExpr (SList [SAtom "text", SString s]) = pure (Lit (TextLit s))
valExprFromSExpr (SAtom "true") = pure (Lit (BoolLit True))
valExprFromSExpr (SAtom "false") = pure (Lit (BoolLit False))
valExprFromSExpr (SAtom "wildcard") = pure (Lit WildcardLit)
valExprFromSExpr (SList (SAtom "call-expr" : n : es)) =
  CallExpr <$> nameFromSExpr n <*> traverse callArgFromSExpr es
valExprFromSExpr (SList (SAtom "host-call" : n : es)) =
  HostCall <$> nameFromSExpr n <*> traverse valExprFromSExpr es
valExprFromSExpr (SList [SAtom "eval-deep", e]) = EvalDeep <$> valExprFromSExpr e
valExprFromSExpr (SList [SAtom "not", e]) = Not <$> valExprFromSExpr e
valExprFromSExpr (SList [SAtom "and", a, b]) =
  And <$> valExprFromSExpr a <*> valExprFromSExpr b
valExprFromSExpr (SList [SAtom "or", a, b]) =
  Or <$> valExprFromSExpr a <*> valExprFromSExpr b
valExprFromSExpr (SAtom "new-var") = pure NewVar
valExprFromSExpr (SList (SAtom "make-term" : n : es)) =
  MakeTerm <$> nameFromSExpr n <*> traverse valExprFromSExpr es
valExprFromSExpr (SList [SAtom "match-term", e, n, SInt a]) =
  MatchTerm <$> valExprFromSExpr e <*> nameFromSExpr n <*> pure a
valExprFromSExpr (SList [SAtom "get-arg", e, SInt i]) =
  GetArg <$> valExprFromSExpr e <*> pure i
valExprFromSExpr (SList [SAtom "alive", e]) = Alive <$> idExprFromSExpr e
valExprFromSExpr (SList [SAtom "id-equal", a, b]) =
  IdEqual <$> idExprFromSExpr a <*> idExprFromSExpr b
valExprFromSExpr (SList [SAtom "is-constraint-type", e, ct]) =
  IsConstraintType <$> idExprFromSExpr e <*> constraintTypeFromSExpr ct
valExprFromSExpr (SList (SAtom "not-in-history" : rid : es)) =
  NotInHistory <$> ruleIdFromSExpr rid <*> traverse idExprFromSExpr es
valExprFromSExpr (SList [SAtom "unify", a, b]) =
  Unify <$> valExprFromSExpr a <*> valExprFromSExpr b
valExprFromSExpr (SList [SAtom "equal", a, b]) =
  Equal <$> valExprFromSExpr a <*> valExprFromSExpr b
valExprFromSExpr (SList [SAtom "field-arg", e, SInt i]) =
  FieldArg <$> idExprFromSExpr e <*> pure (ArgIndex i)
valExprFromSExpr (SList [SAtom "field-type", e]) =
  FieldType <$> idExprFromSExpr e
valExprFromSExpr s = err ("expected value expression, got: " <> printSExpr s)

idExprFromSExpr :: SExpr -> Err IdExpr
idExprFromSExpr (SList [SAtom "id-var", n]) = IdVar <$> nameFromSExpr n
idExprFromSExpr (SList (SAtom "create-constraint" : ct : es)) =
  CreateConstraint <$> constraintTypeFromSExpr ct <*> traverse valExprFromSExpr es
idExprFromSExpr s = err ("expected id expression, got: " <> printSExpr s)

callArgFromSExpr :: SExpr -> Err CallArg
callArgFromSExpr (SList [SAtom "arg-val", e]) = AVal <$> valExprFromSExpr e
callArgFromSExpr (SList [SAtom "arg-id", e]) = AId <$> idExprFromSExpr e
callArgFromSExpr s = err ("expected call argument, got: " <> printSExpr s)

condFromSExpr :: SExpr -> Err (ArgIndex, ValExpr)
condFromSExpr (SList [SInt i, e]) = (ArgIndex i,) <$> valExprFromSExpr e
condFromSExpr s = err ("expected (index expr), got: " <> printSExpr s)

nameFromSExpr :: SExpr -> Err Name
nameFromSExpr (SString t) = pure (Name t)
nameFromSExpr s = err ("expected string (name), got: " <> printSExpr s)

labelFromSExpr :: SExpr -> Err Label
labelFromSExpr (SString t) = pure (Label t)
labelFromSExpr s = err ("expected string (label), got: " <> printSExpr s)

ruleIdFromSExpr :: SExpr -> Err RuleId
ruleIdFromSExpr (SInt n) = pure (RuleId n)
ruleIdFromSExpr s = err ("expected int (rule id), got: " <> printSExpr s)

constraintTypeFromSExpr :: SExpr -> Err ConstraintType
constraintTypeFromSExpr (SInt n) = pure (ConstraintType n)
constraintTypeFromSExpr s = err ("expected int (constraint type), got: " <> printSExpr s)
