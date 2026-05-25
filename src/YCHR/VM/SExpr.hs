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
          SInt (fromIntegral arity),
          SInt (fromIntegral ct)
        ]

identToSExpr :: Types.QualifiedIdentifier -> SExpr
identToSExpr (Types.QualifiedIdentifier m n arity) =
  SList
    [ chrNameToSExpr
        ( Types.Qualified
            m
            n
        ),
      SInt (fromIntegral arity)
    ]

chrNameToSExpr :: Types.Name -> SExpr
chrNameToSExpr (Types.Unqualified t) = SString t
chrNameToSExpr (Types.Qualified m t) = SList [SAtom "qualified", SString m, SString t]

programToSExpr :: Program -> SExpr
programToSExpr prog =
  SList
    ( SAtom "program"
        : SInt (fromIntegral prog.numTypes)
        : SList (SAtom "type-names" : map chrNameToSExpr prog.typeNames)
        : SInt (fromIntegral prog.numRules)
        : SList (SAtom "rule-names" : map SString prog.ruleNames)
        : SList (SAtom "evaluables" : map evaluableEntryToSExpr prog.evaluables)
        : map procedureToSExpr prog.procedures
    )

evaluableEntryToSExpr :: (EvaluableKey, Name) -> SExpr
evaluableEntryToSExpr (key, procName) =
  SList [nameToSExpr key.functor, SInt (fromIntegral key.arity), nameToSExpr procName]

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
  SList [SAtom "if", boolExprToSExpr c, SList (map stmtToSExpr ts), SList (map stmtToSExpr es)]
stmtToSExpr (Foreach lbl ct sv conds body) =
  SList
    [ SAtom "foreach",
      labelToSExpr lbl,
      constraintTypeToSExpr ct,
      nameToSExpr sv,
      SList [SList [SInt (fromIntegral i), valExprToSExpr e] | (ArgIndex i, e) <- conds],
      SList (map stmtToSExpr body)
    ]
stmtToSExpr (Continue lbl) = SList [SAtom "continue", labelToSExpr lbl]
stmtToSExpr (Break lbl) = SList [SAtom "break", labelToSExpr lbl]
stmtToSExpr (Return e) = SList [SAtom "return", valExprToSExpr e]
stmtToSExpr (ExprStmt e) = SList [SAtom "expr-stmt", valExprToSExpr e]
stmtToSExpr (BoolExprStmt e) = SList [SAtom "bool-expr-stmt", boolExprToSExpr e]
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
valExprToSExpr (EvalIs e) = SList [SAtom "eval-is", valExprToSExpr e]
valExprToSExpr NewVar = SAtom "new-var"
valExprToSExpr (MakeTerm n es) =
  SList (SAtom "make-term" : nameToSExpr n : map valExprToSExpr es)
valExprToSExpr (GetArg e i) = SList [SAtom "get-arg", valExprToSExpr e, SInt (fromIntegral i)]
valExprToSExpr (FieldArg e (ArgIndex i)) =
  SList [SAtom "field-arg", idExprToSExpr e, SInt (fromIntegral i)]
valExprToSExpr (FieldType e) = SList [SAtom "field-type", idExprToSExpr e]

boolExprToSExpr :: BoolExpr -> SExpr
boolExprToSExpr (BLit True) = SAtom "btrue"
boolExprToSExpr (BLit False) = SAtom "bfalse"
boolExprToSExpr (BNot e) = SList [SAtom "bnot", boolExprToSExpr e]
boolExprToSExpr (BAnd a b) = SList [SAtom "band", boolExprToSExpr a, boolExprToSExpr b]
boolExprToSExpr (BOr a b) = SList [SAtom "bor", boolExprToSExpr a, boolExprToSExpr b]
boolExprToSExpr (BMatchTerm e n a) =
  SList
    [ SAtom "bmatch-term",
      valExprToSExpr e,
      nameToSExpr n,
      SInt (fromIntegral a)
    ]
boolExprToSExpr (BEqual a b) = SList [SAtom "bequal", valExprToSExpr a, valExprToSExpr b]
boolExprToSExpr (BIdEqual a b) = SList [SAtom "bid-equal", idExprToSExpr a, idExprToSExpr b]
boolExprToSExpr (BAlive e) = SList [SAtom "balive", idExprToSExpr e]
boolExprToSExpr (BIsConstraintType e ct) =
  SList [SAtom "bis-constraint-type", idExprToSExpr e, constraintTypeToSExpr ct]
boolExprToSExpr (BNotInHistory rid es) =
  SList (SAtom "bnot-in-history" : ruleIdToSExpr rid : map idExprToSExpr es)
boolExprToSExpr (BUnify a b) = SList [SAtom "bunify", valExprToSExpr a, valExprToSExpr b]
boolExprToSExpr (BFromVal e) = SList [SAtom "bfrom-val", valExprToSExpr e]
boolExprToSExpr (BEvalDeep e) = SList [SAtom "beval-deep", boolExprToSExpr e]

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
ruleIdToSExpr (RuleId n) = SInt (fromIntegral n)

constraintTypeToSExpr :: ConstraintType -> SExpr
constraintTypeToSExpr (ConstraintType n) = SInt (fromIntegral n)

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
      pure (Types.Identifier name (fromInteger arity), Types.ConstraintType (fromInteger ct))
    entryFromSExpr s = err ("expected (name arity int), got: " <> printSExpr s)
symbolTableFromSExpr s = err ("expected (symbol-table ...), got: " <> printSExpr s)

identFromSExpr :: SExpr -> Err Types.QualifiedIdentifier
identFromSExpr (SList [n, SInt arity]) = do
  name <- chrNameFromSExpr n
  case name of
    Types.Qualified m t -> pure (Types.QualifiedIdentifier m t (fromInteger arity))
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
          : SList (SAtom "evaluables" : evSexprs)
          : procs
        )
    ) = do
    tns <- traverse chrNameFromSExpr tnSexprs
    rns <- traverse textFromSExpr rnSexprs
    evs <- traverse evaluableEntryFromSExpr evSexprs
    ps <- traverse procedureFromSExpr procs
    pure
      Program
        { numTypes = fromInteger n,
          typeNames = tns,
          numRules = fromInteger nr,
          ruleNames = rns,
          evaluables = evs,
          procedures = ps
        }
programFromSExpr s = err ("expected (program ...), got: " <> printSExpr s)

evaluableEntryFromSExpr :: SExpr -> Err (EvaluableKey, Name)
evaluableEntryFromSExpr (SList [fSexpr, SInt arity, pSexpr]) = do
  functor <- nameFromSExpr fSexpr
  procName <- nameFromSExpr pSexpr
  pure (EvaluableKey {functor = functor, arity = fromInteger arity}, procName)
evaluableEntryFromSExpr s = err ("expected evaluable entry, got: " <> printSExpr s)

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
  If <$> boolExprFromSExpr c <*> traverse stmtFromSExpr ts <*> traverse stmtFromSExpr es
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
stmtFromSExpr (SList [SAtom "bool-expr-stmt", e]) = BoolExprStmt <$> boolExprFromSExpr e
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
valExprFromSExpr (SList [SAtom "eval-is", e]) = EvalIs <$> valExprFromSExpr e
valExprFromSExpr (SAtom "new-var") = pure NewVar
valExprFromSExpr (SList (SAtom "make-term" : n : es)) =
  MakeTerm <$> nameFromSExpr n <*> traverse valExprFromSExpr es
valExprFromSExpr (SList [SAtom "get-arg", e, SInt i]) =
  GetArg <$> valExprFromSExpr e <*> pure (fromInteger i)
valExprFromSExpr (SList [SAtom "field-arg", e, SInt i]) =
  FieldArg <$> idExprFromSExpr e <*> pure (ArgIndex (fromInteger i))
valExprFromSExpr (SList [SAtom "field-type", e]) =
  FieldType <$> idExprFromSExpr e
valExprFromSExpr s = err ("expected value expression, got: " <> printSExpr s)

boolExprFromSExpr :: SExpr -> Err BoolExpr
boolExprFromSExpr (SAtom "btrue") = pure (BLit True)
boolExprFromSExpr (SAtom "bfalse") = pure (BLit False)
boolExprFromSExpr (SList [SAtom "bnot", e]) = BNot <$> boolExprFromSExpr e
boolExprFromSExpr (SList [SAtom "band", a, b]) =
  BAnd <$> boolExprFromSExpr a <*> boolExprFromSExpr b
boolExprFromSExpr (SList [SAtom "bor", a, b]) =
  BOr <$> boolExprFromSExpr a <*> boolExprFromSExpr b
boolExprFromSExpr (SList [SAtom "bmatch-term", e, n, SInt a]) =
  BMatchTerm <$> valExprFromSExpr e <*> nameFromSExpr n <*> pure (fromInteger a)
boolExprFromSExpr (SList [SAtom "bequal", a, b]) =
  BEqual <$> valExprFromSExpr a <*> valExprFromSExpr b
boolExprFromSExpr (SList [SAtom "bid-equal", a, b]) =
  BIdEqual <$> idExprFromSExpr a <*> idExprFromSExpr b
boolExprFromSExpr (SList [SAtom "balive", e]) = BAlive <$> idExprFromSExpr e
boolExprFromSExpr (SList [SAtom "bis-constraint-type", e, ct]) =
  BIsConstraintType <$> idExprFromSExpr e <*> constraintTypeFromSExpr ct
boolExprFromSExpr (SList (SAtom "bnot-in-history" : rid : es)) =
  BNotInHistory <$> ruleIdFromSExpr rid <*> traverse idExprFromSExpr es
boolExprFromSExpr (SList [SAtom "bunify", a, b]) =
  BUnify <$> valExprFromSExpr a <*> valExprFromSExpr b
boolExprFromSExpr (SList [SAtom "bfrom-val", e]) = BFromVal <$> valExprFromSExpr e
boolExprFromSExpr (SList [SAtom "beval-deep", e]) = BEvalDeep <$> boolExprFromSExpr e
boolExprFromSExpr s = err ("expected boolean expression, got: " <> printSExpr s)

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
condFromSExpr (SList [SInt i, e]) = (ArgIndex (fromInteger i),) <$> valExprFromSExpr e
condFromSExpr s = err ("expected (index expr), got: " <> printSExpr s)

nameFromSExpr :: SExpr -> Err Name
nameFromSExpr (SString t) = pure (Name t)
nameFromSExpr s = err ("expected string (name), got: " <> printSExpr s)

labelFromSExpr :: SExpr -> Err Label
labelFromSExpr (SString t) = pure (Label t)
labelFromSExpr s = err ("expected string (label), got: " <> printSExpr s)

ruleIdFromSExpr :: SExpr -> Err RuleId
ruleIdFromSExpr (SInt n) = pure (RuleId (fromInteger n))
ruleIdFromSExpr s = err ("expected int (rule id), got: " <> printSExpr s)

constraintTypeFromSExpr :: SExpr -> Err ConstraintType
constraintTypeFromSExpr (SInt n) = pure (ConstraintType (fromInteger n))
constraintTypeFromSExpr s = err ("expected int (constraint type), got: " <> printSExpr s)
