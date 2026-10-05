{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE StandaloneDeriving #-}
-- Every instance here is an orphan by construction: the class lives in
-- "YCHR.Embedded.Generate.ToCode" and the types in the library, and
-- neither module should learn about code generation.
{-# OPTIONS_GHC -Wno-orphans #-}

-- | 'ToCode' for every type the generated resources contain.
--
-- The derivation is one @deriving instance Generic@ plus one
-- @instance ToCode T where toCode = genericToCode@ per type. Keeping
-- the two in one file makes the coverage easy to read off: the list
-- below is exactly the closure of 'YCHR.Internal.StdLib.StdLib' and of
-- the fields of 'YCHR.Internal.Runtime.Session.SessionInput' that are
-- not recomputable at load time ('YCHR.Internal.Runtime.Session.mkSessionInput'
-- rebuilds the slot phase and the indexable positions from the program,
-- so no @Slots@ type appears here).
--
-- A new constructor in one of these types needs no edit — the generic
-- default covers it. A new /field type/ does: it fails to compile until
-- its 'ToCode' instance is added, which is the point.
module YCHR.Embedded.Generate.Instances () where

import GHC.Generics (Generic)
import YCHR.Embedded.Generate.Code (Code (..))
import YCHR.Embedded.Generate.ToCode (ToCode (..), genericToCode)
import YCHR.Internal.Compile.Pipeline (ExportResolution (..))
import YCHR.Internal.Loc (Ann (..), SourceLoc (..))
import YCHR.Internal.PExpr (OpType (..), PExpr (..))
import YCHR.Internal.Parsed
  ( AnnP (..),
    ConstraintDeclBody (..),
    Declaration (..),
    ExtendClassTypeDeclBody (..),
    FunctionDeclBody (..),
    FunctionDeclKind (..),
    FunctionEquation (..),
    Head (..),
    Import (..),
    Module (..),
    OpDecl (..),
    Rule (..),
    TypeExportDeclBody (..),
  )
import YCHR.Internal.Types
  ( BoundSig (..),
    Constraint (..),
    ConstraintType (..),
    DataConstructor (..),
    Name (..),
    QualifiedIdentifier (..),
    QualifiedName (..),
    RuleId (..),
    Term (..),
    TypeDefinition (..),
    TypeExpr (..),
    TypeKind (..),
    UnqualifiedIdentifier (..),
  )
import YCHR.Internal.VM.Types
  ( ArgIndex (..),
    BoolExpr (..),
    CallArg (..),
    CallableKey (..),
    EvaluableKey (..),
    HistoryIds,
    IdExpr (..),
    Label (..),
    Literal (..),
    ProcKind (..),
    Procedure (..),
    Program (..),
    StackFrame (..),
    Stmt (..),
    ValExpr (..),
    historyIdsList,
  )
import YCHR.Internal.VM.Types qualified as VM

-- ---------------------------------------------------------------------------
-- YCHR.Internal.Loc
-- ---------------------------------------------------------------------------

deriving instance Generic SourceLoc

deriving instance Generic (Ann a)

instance ToCode SourceLoc where
  toCode = genericToCode

instance (ToCode a) => ToCode (Ann a) where
  toCode = genericToCode

-- ---------------------------------------------------------------------------
-- YCHR.Internal.PExpr
-- ---------------------------------------------------------------------------

deriving instance Generic PExpr

deriving instance Generic OpType

instance ToCode PExpr where
  toCode = genericToCode

instance ToCode OpType where
  toCode = genericToCode

-- ---------------------------------------------------------------------------
-- YCHR.Internal.Types
-- ---------------------------------------------------------------------------

deriving instance Generic Name

deriving instance Generic Constraint

deriving instance Generic Term

deriving instance Generic TypeDefinition

deriving instance Generic TypeKind

deriving instance Generic DataConstructor

deriving instance Generic TypeExpr

deriving instance Generic BoundSig

deriving instance Generic QualifiedName

deriving instance Generic ConstraintType

deriving instance Generic RuleId

deriving instance Generic UnqualifiedIdentifier

deriving instance Generic QualifiedIdentifier

instance ToCode Name where
  toCode = genericToCode

instance ToCode Constraint where
  toCode = genericToCode

instance ToCode Term where
  toCode = genericToCode

instance ToCode TypeDefinition where
  toCode = genericToCode

instance ToCode TypeKind where
  toCode = genericToCode

instance ToCode DataConstructor where
  toCode = genericToCode

instance ToCode TypeExpr where
  toCode = genericToCode

instance ToCode BoundSig where
  toCode = genericToCode

instance ToCode QualifiedName where
  toCode = genericToCode

instance ToCode ConstraintType where
  toCode = genericToCode

instance ToCode RuleId where
  toCode = genericToCode

instance ToCode UnqualifiedIdentifier where
  toCode = genericToCode

instance ToCode QualifiedIdentifier where
  toCode = genericToCode

-- ---------------------------------------------------------------------------
-- YCHR.Internal.Parsed
-- ---------------------------------------------------------------------------

deriving instance Generic (AnnP a)

deriving instance Generic Import

deriving instance Generic ConstraintDeclBody

deriving instance Generic FunctionDeclBody

deriving instance Generic ExtendClassTypeDeclBody

deriving instance Generic TypeExportDeclBody

deriving instance Generic FunctionDeclKind

deriving instance Generic OpDecl

deriving instance Generic Declaration

deriving instance Generic FunctionEquation

deriving instance Generic Rule

deriving instance Generic Head

deriving instance Generic Module

instance (ToCode a) => ToCode (AnnP a) where
  toCode = genericToCode

instance ToCode Import where
  toCode = genericToCode

instance ToCode ConstraintDeclBody where
  toCode = genericToCode

instance ToCode FunctionDeclBody where
  toCode = genericToCode

instance ToCode ExtendClassTypeDeclBody where
  toCode = genericToCode

instance ToCode TypeExportDeclBody where
  toCode = genericToCode

instance ToCode FunctionDeclKind where
  toCode = genericToCode

instance ToCode OpDecl where
  toCode = genericToCode

instance ToCode Declaration where
  toCode = genericToCode

instance ToCode FunctionEquation where
  toCode = genericToCode

instance ToCode Rule where
  toCode = genericToCode

instance ToCode Head where
  toCode = genericToCode

instance ToCode Module where
  toCode = genericToCode

-- ---------------------------------------------------------------------------
-- YCHR.Internal.Compile.Pipeline
-- ---------------------------------------------------------------------------

deriving instance Generic ExportResolution

instance ToCode ExportResolution where
  toCode = genericToCode

-- ---------------------------------------------------------------------------
-- YCHR.Internal.VM.Types
-- ---------------------------------------------------------------------------

deriving instance Generic VM.Name

deriving instance Generic Label

deriving instance Generic ArgIndex

deriving instance Generic Literal

deriving instance Generic StackFrame

deriving instance Generic ValExpr

deriving instance Generic IdExpr

deriving instance Generic BoolExpr

deriving instance Generic CallArg

deriving instance Generic Stmt

deriving instance Generic ProcKind

deriving instance Generic EvaluableKey

deriving instance Generic CallableKey

deriving instance Generic Procedure

deriving instance Generic Program

instance ToCode VM.Name where
  toCode = genericToCode

instance ToCode Label where
  toCode = genericToCode

instance ToCode ArgIndex where
  toCode = genericToCode

instance ToCode Literal where
  toCode = genericToCode

instance ToCode StackFrame where
  toCode = genericToCode

instance ToCode ValExpr where
  toCode = genericToCode

instance ToCode IdExpr where
  toCode = genericToCode

instance ToCode BoolExpr where
  toCode = genericToCode

instance ToCode CallArg where
  toCode = genericToCode

instance ToCode Stmt where
  toCode = genericToCode

instance ToCode ProcKind where
  toCode = genericToCode

instance ToCode EvaluableKey where
  toCode = genericToCode

instance ToCode CallableKey where
  toCode = genericToCode

instance ToCode Procedure where
  toCode = genericToCode

instance ToCode Program where
  toCode = genericToCode

-- | 'HistoryIds' is the one type in the closure whose constructor is
-- deliberately abstract ("YCHR.Internal.VM.Types"): the canonical order
-- of its tuple is an invariant, and
-- 'YCHR.Internal.VM.Types.historyIdsFromSerialized' is the documented
-- trust boundary for rebuilding one from a list that already has it.
-- The generated module is exactly such a producer, so the instance goes
-- through that function rather than the constructor.
instance ToCode HistoryIds where
  toCode h = CApp (CName "VM.historyIdsFromSerialized") [toCode (historyIdsList h)]
