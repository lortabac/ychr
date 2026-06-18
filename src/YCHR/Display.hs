{-# LANGUAGE OverloadedStrings #-}

-- | Human-readable error display.
module YCHR.Display
  ( Display (..),
    Severity (..),
    ErrorCode (..),
    displaySrcLoc,
    displayMsgWithSrcLoc,
    displayErrorCode,
    collectErrorCode,
    parseValidationErrorCode,
    resolveErrorCode,
    renameErrorCode,
    renameWarningCode,
    exhaustivenessWarningCode,
    desugarErrorCode,
    compileErrorCode,
    typeCheckErrorCode,
    parseErrorCode,
    operatorConflictCode,
    lambdasInLiveQueryCode,
    runtimeErrorCode,
    goalNotAConstraintCode,
  )
where

import Data.List (intercalate)
import Data.Text qualified as T
import System.Console.ANSI
  ( Color (..),
    ColorIntensity (..),
    ConsoleIntensity (..),
    ConsoleLayer (..),
    SGR (..),
    setSGRCode,
  )
import Text.Parsec.Error qualified as PE
import Text.Parsec.Pos (SourcePos, sourceColumn, sourceLine, sourceName)
import YCHR.Collect (CollectError (..))
import YCHR.Compile (CompileError (..))
import YCHR.Compile.Pipeline (Error (..), GoalRejection (..), Warning (..))
import YCHR.Desugar (DesugarError (..))
import YCHR.Diagnostic (Diagnostic (..))
import YCHR.Exhaustiveness (ExhaustivenessWarning (..))
import YCHR.Parsed (AnnP (..))
import YCHR.Parsed qualified as P
import YCHR.Parser (ParseValidationError (..))
import YCHR.Pretty (prettyPExprSrc, prettyTermSrc)
import YCHR.Rename (RenameError (..), RenameWarning (..))
import YCHR.Resolve (ResolveError (..))
import YCHR.Resolved qualified as R
import YCHR.TypeCheck (TypeCheckError (..))
import YCHR.Types qualified as Types
import YCHR.VM (StackFrame (..))

class Display a where
  displayMsg :: a -> String

-- | Diagnostic severity. Drives both the header label (e.g. @=== error
-- ===@) and the foreground color of 'displayMsgWithSrcLoc'.
--
-- 'SevRuntimeError' is the top frame of a runtime-error stack (magenta),
-- and 'SevStackTrace' is each subsequent frame (cyan). Keeping them
-- distinct lets readers locate the actual error site at a glance even
-- when the stack is deep.
data Severity
  = SevError
  | SevWarning
  | SevRuntimeError
  | SevStackTrace

newtype ErrorCode = ErrorCode Int
  deriving (Show, Eq, Ord)

-- | Format an error code as @YCHR-NNNNN@.
displayErrorCode :: ErrorCode -> String
displayErrorCode (ErrorCode n) = "YCHR-" ++ show n

-- | Display a source location as @file:line:col@.
displaySrcLoc :: P.SourceLoc -> String
displaySrcLoc loc = loc.file ++ ":" ++ show loc.line ++ ":" ++ show loc.col

severityLabel :: Severity -> String
severityLabel SevError = "error"
severityLabel SevWarning = "warning"
severityLabel SevRuntimeError = "runtime error"
severityLabel SevStackTrace = "stack trace"

severityColor :: Severity -> Color
severityColor SevError = Red
severityColor SevWarning = Yellow
severityColor SevRuntimeError = Magenta
severityColor SevStackTrace = Cyan

-- | Format a diagnostic message with source location, severity, error code,
-- optional location label, and optional AST context.
--
-- @
-- file:line:col: severity: YCHR-NNNNN
-- location_label
-- message
-- ast_node
-- @
displayMsgWithSrcLoc ::
  ErrorCode ->
  Severity ->
  String ->
  P.SourceLoc ->
  Maybe String ->
  Maybe String ->
  String
displayMsgWithSrcLoc code sev msg loc maybeLabel maybeNode =
  let col = severityColor sev
      lbl = severityLabel sev
      c = setSGRCode [SetColor Foreground Vivid col]
      r = setSGRCode [Reset]
   in c
        ++ "=== "
        ++ lbl
        ++ " ==="
        ++ r
        ++ "\n"
        ++ setSGRCode [SetConsoleIntensity BoldIntensity]
        ++ displaySrcLoc loc
        ++ ": "
        ++ displayErrorCode code
        ++ "\n"
        ++ maybe
          ""
          ( \l ->
              setSGRCode [SetConsoleIntensity BoldIntensity]
                ++ "<<"
                ++ l
                ++ ">>"
                ++ r
                ++ "\n"
          )
          maybeLabel
        ++ msg
        ++ maybe
          ""
          ( \n ->
              -- Skip the message/node separator when msg is empty so a
              -- stack-trace frame (which carries no message of its own)
              -- doesn't render a phantom blank line between '<<label>>'
              -- and the italicized source snippet.
              (if null msg then "" else "\n")
                ++ setSGRCode [SetItalicized True]
                ++ n
                ++ setSGRCode [SetItalicized False]
          )
          maybeNode
        ++ "\n"
        ++ r

-- | Join multiple error messages. Each message is expected to end with
-- a newline, so a single @\"\\n\"@ separator produces a blank line between
-- messages.
displayErrors :: [String] -> String
displayErrors = intercalate "\n"

-- | Append a hint line to a diagnostic message. Hints are rendered as
-- a second sentence, indented two spaces, so they stand apart from the
-- headline inside the 'displayMsgWithSrcLoc' block.
withHint :: String -> String -> String
withHint msg hint = msg ++ "\n  Hint: " ++ hint

-- | Convert a parsec 'Text.Parsec.Pos.SourcePos' to a 'P.SourceLoc'.
sourceLocFromPos :: SourcePos -> P.SourceLoc
sourceLocFromPos sp =
  P.SourceLoc
    { P.file = sourceName sp,
      P.line = sourceLine sp,
      P.col = sourceColumn sp
    }

-- ---------------------------------------------------------------------------
-- Error codes by phase
-- ---------------------------------------------------------------------------

-- | 1xxxx — collect phase
collectErrorCode :: CollectError -> ErrorCode
collectErrorCode (UnknownLibrary _) = ErrorCode 10001
collectErrorCode (CircularLibraryImport _) = ErrorCode 10002

-- | 15xxx — parse validation phase
parseValidationErrorCode :: ParseValidationError -> ErrorCode
parseValidationErrorCode (DiscontiguousEquations _) = ErrorCode 15001
parseValidationErrorCode MalformedImport = ErrorCode 15002
parseValidationErrorCode MalformedConstraint = ErrorCode 15003
parseValidationErrorCode (DiscontiguousFunctionDecls _) = ErrorCode 15004
parseValidationErrorCode (RequiringOnClass _) = ErrorCode 15005
parseValidationErrorCode (RequiringOnExtendClassType _) = ErrorCode 15006
parseValidationErrorCode MalformedDeclaration = ErrorCode 15007
parseValidationErrorCode MalformedExportItem = ErrorCode 15008
parseValidationErrorCode MalformedTypeExpr = ErrorCode 15009
parseValidationErrorCode MalformedDataConstructor = ErrorCode 15010
parseValidationErrorCode MalformedTypeDefinition = ErrorCode 15011
parseValidationErrorCode OpaqueTypeHasConstructors = ErrorCode 15016
parseValidationErrorCode MalformedOpaqueTypeDefinition = ErrorCode 15017
parseValidationErrorCode MalformedBoundSig = ErrorCode 15012
parseValidationErrorCode MalformedFunctionEquation = ErrorCode 15013
parseValidationErrorCode MalformedTopLevel = ErrorCode 15014
parseValidationErrorCode (DuplicateModuleHeader _) = ErrorCode 15015

-- | 16xxx — resolve phase (post-rename, pre-desugar)
resolveErrorCode :: ResolveError -> ErrorCode
resolveErrorCode (ConstraintHasEquations _) = ErrorCode 16001
resolveErrorCode (FunctionInRuleHead _) = ErrorCode 16002
resolveErrorCode (ReservedName _) = ErrorCode 16003
resolveErrorCode (ReservedModuleName _) = ErrorCode 16019
resolveErrorCode (UnqualifiedConstraintName _) = ErrorCode 16004
resolveErrorCode (ExtendsClosedFunction _) = ErrorCode 16005
resolveErrorCode (OrphanFunctionEquation _ _) = ErrorCode 16006
-- Bounded polymorphism (per docs/reference/type-system.md §Bounded
-- Polymorphism §Errors): the unbound-variable, unknown-bound, cycle,
-- and extend-on-bounded checks all live in the resolve phase.
resolveErrorCode (ExtendTypeOnBoundedFunction _) = ErrorCode 16007
resolveErrorCode (UnboundBoundVariable _ _) = ErrorCode 16008
resolveErrorCode (UnknownBoundFunction _ _ _) = ErrorCode 16009
resolveErrorCode (BoundCycle _) = ErrorCode 16010
resolveErrorCode (MultiSigOnFunction _) = ErrorCode 16011
resolveErrorCode (MixedDeclKinds _) = ErrorCode 16012
resolveErrorCode (ExtendClassTypeOnFunction _) = ErrorCode 16013
resolveErrorCode (ExtendClassOnFunction _) = ErrorCode 16014
resolveErrorCode (ExtendFunctionOnClass _) = ErrorCode 16015
resolveErrorCode (ConstraintFunctionCollision _) = ErrorCode 16016
resolveErrorCode (LambdaParamError _) = ErrorCode 16017
resolveErrorCode EmptyLambdaParams = ErrorCode 16018

-- | 2xxxx — rename phase (errors).
-- Code 20004 was previously used for OperatorInImportList; now reserved
-- because operators are permitted in import lists (see UnknownOperatorImport).
renameErrorCode :: RenameError -> ErrorCode
renameErrorCode (AmbiguousName _ _ _) = ErrorCode 20001
renameErrorCode (UnknownName _ _) = ErrorCode 20002
renameErrorCode (UnknownExport _ _ _) = ErrorCode 20003
renameErrorCode (UnknownImport _ _ _) = ErrorCode 20005
renameErrorCode (UnknownOperatorImport _ _) = ErrorCode 20006
renameErrorCode (UseModuleOutOfOrder _) = ErrorCode 20007
renameErrorCode (UnknownExportedConstructor _ _ _ _) = ErrorCode 20008
renameErrorCode (NotExportedByModule _ _ _) = ErrorCode 20009
renameErrorCode (NonExportedConstructor _ _ _) = ErrorCode 20010
renameErrorCode (ConstructorNotExported _ _ _ _) = ErrorCode 20011
renameErrorCode (AmbiguousDataConstructor _ _) = ErrorCode 20012

-- | 2x1xx — rename phase (warnings)
renameWarningCode :: RenameWarning -> ErrorCode
renameWarningCode (UndeclaredDataConstructor _) = ErrorCode 20101
renameWarningCode (DataConstructorArityMismatch _ _) = ErrorCode 20102

-- | 2x1xx — exhaustiveness warnings (a pattern-matching warning, in the
-- same warning band as the rename warnings).
exhaustivenessWarningCode :: ExhaustivenessWarning -> ErrorCode
exhaustivenessWarningCode (NonExhaustiveMatch _ _) = ErrorCode 20103

-- | 3xxxx — desugar phase
desugarErrorCode :: DesugarError -> ErrorCode
desugarErrorCode (UnexpectedBodyExpr _) = ErrorCode 30001
desugarErrorCode (NonBooleanGuard _) = ErrorCode 30002
desugarErrorCode (NonPreludeFunctionBodyItem _) = ErrorCode 30003
desugarErrorCode (NonVariableIsInFunctionBody _) = ErrorCode 30004

-- | 4xxxx — compile phase
compileErrorCode :: CompileError -> ErrorCode
compileErrorCode (UnknownConstraintType _) = ErrorCode 40001
compileErrorCode (UnboundVariable _) = ErrorCode 40002

-- | 6xxxx — type-check phase
typeCheckErrorCode :: TypeCheckError -> ErrorCode
typeCheckErrorCode (InconsistentTypes _ _) = ErrorCode 60001
typeCheckErrorCode (UnboundTypeVar _ _ _) = ErrorCode 60004
typeCheckErrorCode (UndefinedType _ _ _) = ErrorCode 60005
typeCheckErrorCode (NoMatchingOverload _) = ErrorCode 60006
typeCheckErrorCode (DuplicateConstructor _ _) = ErrorCode 60007
typeCheckErrorCode (ConstructorArityMismatch _ _ _) = ErrorCode 60008
typeCheckErrorCode (BoundUnsatisfied _) = ErrorCode 60012

-- | 5xxxx — top-level errors
parseErrorCode :: ErrorCode
parseErrorCode = ErrorCode 50001

operatorConflictCode :: ErrorCode
operatorConflictCode = ErrorCode 50002

lambdasInLiveQueryCode :: ErrorCode
lambdasInLiveQueryCode = ErrorCode 50003

-- | 20013 — @ychr run -g GOAL@ received a goal that is not a single
-- declared constraint (bare expression, conjunction, function call,
-- or an unknown name). Lives in the rename/resolution range because
-- the rejection is about goal-name resolution, not runtime behavior.
goalNotAConstraintCode :: ErrorCode
goalNotAConstraintCode = ErrorCode 20013

-- | 6xxxx — shared with type-check; 60001 is also used for runtime errors
-- raised by 'YCHR.Runtime.Error.runtimeError''/'runtimeErrorS'.
runtimeErrorCode :: ErrorCode
runtimeErrorCode = ErrorCode 60001

-- ---------------------------------------------------------------------------
-- Display instances
-- ---------------------------------------------------------------------------

instance Display (P.AnnP ParseValidationError) where
  displayMsg (AnnP err loc origin) =
    displayMsgWithSrcLoc
      (parseValidationErrorCode err)
      SevError
      (parseValidationErrorMsg err)
      loc
      Nothing
      (Just (prettyPExprSrc origin))

parseValidationErrorMsg :: ParseValidationError -> String
parseValidationErrorMsg (DiscontiguousEquations name) =
  withHint
    ("Equations for function '" ++ T.unpack name ++ "' must be contiguous")
    "declare the function with :- open_function to allow equations from other modules"
parseValidationErrorMsg (DiscontiguousFunctionDecls name) =
  withHint
    ("Declarations for '" ++ T.unpack name ++ "' must be contiguous")
    ( "use :- extend_function (open_function), :- extend_class"
        ++ " or :- extend_class_type (open_class) from another module"
        ++ " to extend an open declaration"
    )
parseValidationErrorMsg MalformedImport =
  withHint
    "Invalid import"
    "expected a module name or library(name)"
parseValidationErrorMsg MalformedConstraint =
  withHint
    "Invalid constraint"
    "expected an atom or compound term"
parseValidationErrorMsg (RequiringOnClass name) =
  withHint
    ( "'requiring' is not allowed on ':- class' / ':- open_class' (declaration '"
        ++ T.unpack name
        ++ "')"
    )
    "bounded polymorphism is reserved for :- function / :- open_function"
parseValidationErrorMsg (RequiringOnExtendClassType name) =
  withHint
    ( "'requiring' is not allowed on ':- extend_class_type' (target '"
        ++ T.unpack name
        ++ "')"
    )
    "bounds belong to the original declaration; an extension cannot introduce them"
parseValidationErrorMsg MalformedDeclaration =
  withHint
    "Invalid declaration"
    "expected name/arity, name(types) -> ret, or sig requiring bounds"
parseValidationErrorMsg MalformedExportItem =
  withHint
    "Invalid export/import list item"
    "expected name/arity, fun name/arity, type(name/arity), or op(prio, type, name)"
parseValidationErrorMsg MalformedTypeExpr =
  withHint
    "Invalid type expression"
    "expected a type variable, atom, or compound type"
parseValidationErrorMsg MalformedDataConstructor =
  withHint
    "Invalid data constructor"
    "expected an atom or compound term in a chr_type alternative"
parseValidationErrorMsg MalformedTypeDefinition =
  withHint
    "Invalid type definition"
    "expected 'name(Vars) ---> con1 ; con2 ; ...'"
parseValidationErrorMsg OpaqueTypeHasConstructors =
  withHint
    "Opaque type cannot have data constructors"
    ( "an opaque type is declared as ':- opaque_type name(Vars).' with no"
        ++ " '---> ...' body; use ':- chr_type' for a type with constructors"
    )
parseValidationErrorMsg MalformedOpaqueTypeDefinition =
  withHint
    "Invalid opaque type definition"
    "expected ':- opaque_type name.' or ':- opaque_type name(Vars).'"
parseValidationErrorMsg MalformedBoundSig =
  withHint
    "Invalid bound signature"
    "expected 'name(t1, ..., tn) -> tret' (or 'name -> tret' for arity zero)"
parseValidationErrorMsg MalformedFunctionEquation =
  withHint
    "Invalid function equation"
    "expected 'lhs [| guard] -> rhs'"
parseValidationErrorMsg MalformedTopLevel =
  withHint
    "Invalid top-level term"
    "expected a directive, rule (<=> or ==>), or function equation (->)"
parseValidationErrorMsg (DuplicateModuleHeader name) =
  withHint
    ("Duplicate ':- module(...)' header for '" ++ T.unpack name ++ "'")
    "a source file may declare at most one module header; remove the redundant directive"

instance Display (Diagnostic ResolveError) where
  displayMsg (Diagnostic lbl (AnnP err loc origin)) =
    displayMsgWithSrcLoc
      (resolveErrorCode err)
      SevError
      (resolveErrorMsg err)
      loc
      (fmap T.unpack lbl)
      (Just (prettyPExprSrc origin))

resolveErrorMsg :: ResolveError -> String
resolveErrorMsg (ConstraintHasEquations name) =
  withHint
    ( "'"
        ++ displayName name
        ++ "' is declared as a constraint but has function equations (->)"
    )
    "either declare it with :- function or remove the equations"
resolveErrorMsg (FunctionInRuleHead name) =
  withHint
    ( "'"
        ++ displayName name
        ++ "' is declared as a function but appears in a rule head"
    )
    "rule heads must be constraints; call the function from the body or a guard instead"
resolveErrorMsg (ReservedName name) =
  "'"
    ++ displayName name
    ++ "' is a reserved name and cannot be used as a constraint or function"
resolveErrorMsg (ReservedModuleName name) =
  withHint
    ("'" ++ T.unpack name ++ "' is a reserved name and cannot be used as a module name")
    "'host' is the wired-in host-call qualifier; rename the module"
resolveErrorMsg (UnqualifiedConstraintName name) =
  withHint
    ( "Internal error: unqualified constraint name reached the resolve phase ('"
        ++ displayName name
        ++ "')"
    )
    "this is a YCHR bug; please report it with the .chr file that triggered it"
resolveErrorMsg (ExtendsClosedFunction name) =
  withHint
    ( "Cannot extend '"
        ++ displayName name
        ++ "' because it is declared as closed"
    )
    "declare it with :- open_function or :- open_class to allow cross-module extensions"
resolveErrorMsg (OrphanFunctionEquation name modName) =
  withHint
    ( "Function '"
        ++ displayName name
        ++ "' is declared elsewhere but has an equation in module '"
        ++ T.unpack modName
        ++ "'"
    )
    ( "use :- extend_function (or :- extend_class) to add equations"
        ++ " to an open declaration from another module"
    )
resolveErrorMsg (ExtendTypeOnBoundedFunction name) =
  withHint
    ( "Cannot extend the type of bounded open function '"
        ++ displayName name
        ++ "'"
    )
    ( "the instance set of a bounded open function is determined by its"
        ++ " requiring clause; declare a new signature of the bound function"
        ++ " instead"
    )
resolveErrorMsg (UnboundBoundVariable declName var) =
  withHint
    ( "Type variable '"
        ++ T.unpack var
        ++ "' in the requiring clause of '"
        ++ T.unpack declName
        ++ "' is not bound by the declaration's primary signature"
    )
    ( "every variable in 'requiring' must also appear in the"
        ++ " declaration's argument or return types"
    )
resolveErrorMsg (UnknownBoundFunction declName boundName arity) =
  withHint
    ( "'"
        ++ T.unpack declName
        ++ "' requires '"
        ++ T.unpack boundName
        ++ "/"
        ++ show arity
        ++ "' but no such function is declared"
    )
    "declare ':- function "
    ++ T.unpack boundName
    ++ "/"
    ++ show arity
    ++ ".' (or import a module that does)"
resolveErrorMsg (BoundCycle names) =
  withHint
    ( "Cyclic 'requiring' clause: "
        ++ intercalate " -> " (map T.unpack names)
    )
    "the bound graph must be acyclic; remove or restructure one of the requiring edges"
resolveErrorMsg (MultiSigOnFunction name) =
  withHint
    ( "'"
        ++ displayName name
        ++ "' is declared with multiple signatures but is not a class"
    )
    ( "use :- class / :- open_class to enable signature overloading,"
        ++ " or keep a single :- function signature"
    )
resolveErrorMsg (MixedDeclKinds name) =
  withHint
    ( "'"
        ++ displayName name
        ++ "' is declared with both :- function and :- class forms"
    )
    ( "pick one form: :- function / :- open_function for single signatures,"
        ++ " :- class / :- open_class for overloads"
    )
resolveErrorMsg (ExtendClassTypeOnFunction name) =
  withHint
    ( "':- extend_class_type' targets '"
        ++ displayName name
        ++ "', which is declared as :- open_function"
    )
    ( "type extensions are only meaningful on :- open_class;"
        ++ " declare the target as :- open_class to overload it"
    )
resolveErrorMsg (ExtendClassOnFunction name) =
  withHint
    ( "':- extend_class' targets '"
        ++ displayName name
        ++ "', which is declared as :- open_function"
    )
    "use :- extend_function to add equations to an :- open_function"
resolveErrorMsg (ExtendFunctionOnClass name) =
  withHint
    ( "':- extend_function' targets '"
        ++ displayName name
        ++ "', which is declared as :- open_class"
    )
    "use :- extend_class to add equations to an :- open_class"
resolveErrorMsg (LambdaParamError term) =
  withHint
    ("Invalid lambda parameter: " ++ prettyTermSrc term)
    "lambda parameters must be variables or the anonymous variable (_)"
resolveErrorMsg EmptyLambdaParams =
  withHint
    "Lambda has no parameters"
    "lambdas must declare at least one parameter; use ':- function' for a no-arg helper"
resolveErrorMsg (ConstraintFunctionCollision name) =
  withHint
    ( "'"
        ++ displayName name
        ++ "' is declared as both :- chr_constraint and a function-like"
        ++ " form in the same module"
    )
    "constraints and functions share the symbol namespace; pick one form for this name"

instance Display (Diagnostic CollectError) where
  displayMsg (Diagnostic lbl (AnnP err loc origin)) =
    displayMsgWithSrcLoc
      (collectErrorCode err)
      SevError
      (collectErrorMsg err)
      loc
      (fmap T.unpack lbl)
      (Just (prettyPExprSrc origin))

collectErrorMsg :: CollectError -> String
collectErrorMsg (UnknownLibrary name) =
  withHint
    ("Unknown library '" ++ T.unpack name ++ "'")
    "check the library name; the built-in libraries are bundled with the compiler"
collectErrorMsg (CircularLibraryImport names) =
  "Circular library import: "
    ++ intercalate " -> " (map T.unpack names)

instance Display (Diagnostic RenameError) where
  displayMsg (Diagnostic lbl (AnnP err loc origin)) =
    displayMsgWithSrcLoc
      (renameErrorCode err)
      SevError
      (renameErrorMsg err)
      loc
      (fmap T.unpack lbl)
      (Just (prettyPExprSrc origin))

renameErrorMsg :: RenameError -> String
renameErrorMsg (AmbiguousName name arity candidates) =
  withHint
    ( "Ambiguous name '"
        ++ T.unpack name
        ++ "/"
        ++ show arity
        ++ "'"
    )
    ( "could be: "
        ++ intercalate ", " (map T.unpack candidates)
        ++ "; qualify the name explicitly to disambiguate"
    )
renameErrorMsg (UnknownName name arity) =
  withHint
    ("Unknown name '" ++ T.unpack name ++ "/" ++ show arity ++ "'")
    "declare it with :- chr_constraint or :- function, or import it from another module"
renameErrorMsg (UnknownExport modName name arity) =
  "Module '"
    ++ T.unpack modName
    ++ "' exports '"
    ++ T.unpack name
    ++ "/"
    ++ show arity
    ++ "' but does not declare it"
renameErrorMsg (UnknownImport modName name arity) =
  "Module '"
    ++ T.unpack modName
    ++ "' does not export '"
    ++ T.unpack name
    ++ "/"
    ++ show arity
    ++ "'"
renameErrorMsg (NotExportedByModule modName name arity) =
  withHint
    ( "Module '"
        ++ T.unpack modName
        ++ "' does not export '"
        ++ T.unpack name
        ++ "/"
        ++ show arity
        ++ "'"
    )
    ( "ensure '"
        ++ T.unpack modName
        ++ "' is imported and exports '"
        ++ T.unpack name
        ++ "/"
        ++ show arity
        ++ "'"
    )
renameErrorMsg (UnknownOperatorImport modName opName) =
  "Module '"
    ++ T.unpack modName
    ++ "' does not export operator '"
    ++ T.unpack opName
    ++ "'"
renameErrorMsg (UseModuleOutOfOrder modName) =
  withHint
    ( "use_module("
        ++ T.unpack modName
        ++ ") appears out of order"
    )
    ( "use_module directives must come immediately after the :- module"
        ++ " directive, before any other directive or rule"
    )
renameErrorMsg (UnknownExportedConstructor modName tyName tyArity conName) =
  "Module '"
    ++ T.unpack modName
    ++ "' exports type '"
    ++ T.unpack tyName
    ++ "/"
    ++ show tyArity
    ++ "' listing constructor '"
    ++ T.unpack conName
    ++ "', but that constructor is not declared on the type"
renameErrorMsg (NonExportedConstructor modName conName arity) =
  withHint
    ( "Module '"
        ++ T.unpack modName
        ++ "' does not export data constructor '"
        ++ T.unpack conName
        ++ "/"
        ++ show arity
        ++ "'"
    )
    ( "add '"
        ++ T.unpack conName
        ++ "' to the type's constructor export list in '"
        ++ T.unpack modName
        ++ "' (e.g. type(t/n, ["
        ++ T.unpack conName
        ++ ", ...]))"
    )
renameErrorMsg (ConstructorNotExported modName tyName tyArity conName) =
  withHint
    ( "Module '"
        ++ T.unpack modName
        ++ "' declares constructor '"
        ++ T.unpack conName
        ++ "' on type '"
        ++ T.unpack tyName
        ++ "/"
        ++ show tyArity
        ++ "' but does not export it"
    )
    ( "add '"
        ++ T.unpack conName
        ++ "' to the constructor export list of type '"
        ++ T.unpack tyName
        ++ "/"
        ++ show tyArity
        ++ "' in module '"
        ++ T.unpack modName
        ++ "'"
    )
renameErrorMsg (AmbiguousDataConstructor name candidates) =
  withHint
    ("Ambiguous data constructor '" ++ T.unpack name ++ "'")
    ( "exported by: "
        ++ intercalate ", " (map T.unpack candidates)
        ++ "; qualify the constructor explicitly to disambiguate"
    )

instance Display (Diagnostic RenameWarning) where
  displayMsg (Diagnostic lbl (AnnP err loc origin)) =
    displayMsgWithSrcLoc
      (renameWarningCode err)
      SevWarning
      (renameWarningMsg err)
      loc
      (fmap T.unpack lbl)
      (Just (prettyPExprSrc origin))

renameWarningMsg :: RenameWarning -> String
renameWarningMsg (UndeclaredDataConstructor name) =
  withHint
    ("Undeclared data constructor '" ++ T.unpack name ++ "'")
    "declare it with :- chr_type, or check the spelling"
renameWarningMsg (DataConstructorArityMismatch name arity) =
  "Data constructor '"
    ++ T.unpack name
    ++ "' used with "
    ++ show arity
    ++ " argument(s) but declared with a different arity"

instance Display (Diagnostic ExhaustivenessWarning) where
  displayMsg (Diagnostic lbl (AnnP err loc origin)) =
    displayMsgWithSrcLoc
      (exhaustivenessWarningCode err)
      SevWarning
      (exhaustivenessWarningMsg err)
      loc
      (fmap T.unpack lbl)
      (Just (prettyPExprSrc origin))

exhaustivenessWarningMsg :: ExhaustivenessWarning -> String
exhaustivenessWarningMsg (NonExhaustiveMatch name witness) =
  withHint
    ( "Non-exhaustive patterns in function '"
        ++ T.unpack name
        ++ "': no equation matches "
        ++ prettyTermSrc witness
    )
    "add an equation for the missing case, or a catch-all variable/wildcard pattern"

instance Display (Diagnostic DesugarError) where
  displayMsg (Diagnostic lbl (AnnP err loc origin)) =
    displayMsgWithSrcLoc
      (desugarErrorCode err)
      SevError
      (desugarErrorMsg err)
      loc
      (fmap T.unpack lbl)
      (Just (prettyPExprSrc origin))

desugarErrorMsg :: DesugarError -> String
desugarErrorMsg (UnexpectedBodyExpr e) =
  withHint
    ("This expression is not valid in a rule body: " ++ prettyTermSrc (R.exprToTerm e))
    ( "rule bodies may contain constraints, function calls,"
        ++ " unifications (=), 'is' expressions, and 'true'"
    )
desugarErrorMsg (NonBooleanGuard e) =
  withHint
    ( "This expression cannot evaluate to a boolean and is not valid as a guard: "
        ++ prettyTermSrc (R.exprToTerm e)
    )
    ( "guards must be function calls, boolean-typed variables,"
        ++ " true/false, or a host call returning a boolean"
    )
desugarErrorMsg (NonPreludeFunctionBodyItem e) =
  withHint
    ( "This expression is not valid before the final return value in a"
        ++ " function body: "
        ++ prettyTermSrc (R.exprToTerm e)
    )
    ( "non-final items must be an 'is' binding (X is E), a host call"
        ++ " (host:f(args)), or a function call"
    )
desugarErrorMsg (NonVariableIsInFunctionBody e) =
  withHint
    ( "The left-hand side of 'is' in a function body must be a variable: "
        ++ prettyTermSrc (R.exprToTerm e)
    )
    "use 'X is E' to bind, then pattern-match on X in subsequent positions"

instance Display (Diagnostic CompileError) where
  displayMsg (Diagnostic lbl (AnnP err loc origin)) =
    displayMsgWithSrcLoc
      (compileErrorCode err)
      SevError
      (compileErrorMsg err)
      loc
      (fmap T.unpack lbl)
      (Just (prettyPExprSrc origin))

compileErrorMsg :: CompileError -> String
compileErrorMsg (UnknownConstraintType name) =
  withHint
    ("Unknown constraint type '" ++ displayName name ++ "'")
    "declare it with :- chr_constraint name/arity"
compileErrorMsg (UnboundVariable var) =
  withHint
    ("Unbound variable '" ++ T.unpack var ++ "'")
    "variables used in a guard or body must also appear in the rule head"

instance Display (Diagnostic TypeCheckError) where
  displayMsg (Diagnostic lbl (AnnP err loc origin)) =
    displayMsgWithSrcLoc
      (typeCheckErrorCode err)
      SevError
      (typeCheckErrorMsg err)
      loc
      (fmap T.unpack lbl)
      (Just (prettyPExprSrc origin))

typeCheckErrorMsg :: TypeCheckError -> String
typeCheckErrorMsg (InconsistentTypes t1 t2) =
  "Type mismatch: '" ++ T.unpack t1 ++ "' does not match '" ++ T.unpack t2 ++ "'"
typeCheckErrorMsg (UnboundTypeVar typeName conName varName) =
  withHint
    ( "Type variable '"
        ++ T.unpack varName
        ++ "' used in constructor '"
        ++ T.unpack conName
        ++ "' is not in scope"
    )
    ( "add '"
        ++ T.unpack varName
        ++ "' to the parameter list of type '"
        ++ T.unpack typeName
        ++ "'"
    )
typeCheckErrorMsg (NoMatchingOverload name) =
  withHint
    ("No matching type declaration for '" ++ T.unpack name ++ "'")
    "check that the argument types match one of the declared signatures"
typeCheckErrorMsg (UndefinedType typeName conName refName) =
  withHint
    ( "Undefined type '"
        ++ T.unpack refName
        ++ "' referenced in constructor '"
        ++ T.unpack conName
        ++ "' of type '"
        ++ T.unpack typeName
        ++ "'"
    )
    "declare it with :- chr_type, or check the spelling"
typeCheckErrorMsg (DuplicateConstructor conName decls) =
  "Data constructor '"
    ++ T.unpack conName
    ++ "' is declared in multiple types: "
    ++ intercalate ", " [T.unpack t ++ "/" ++ show a | (t, a) <- decls]
typeCheckErrorMsg (ConstructorArityMismatch conName usedArity declaredArity) =
  "Data constructor '"
    ++ T.unpack conName
    ++ "' is used with "
    ++ show usedArity
    ++ " argument(s) but declared with "
    ++ show declaredArity
typeCheckErrorMsg (BoundUnsatisfied boundName) =
  withHint
    ( "No declared signature of '"
        ++ T.unpack boundName
        ++ "' is consistent with the substituted bound at this use site"
    )
    ( "either widen the bound function's overload set or call the bounded"
        ++ " operation at a type for which a signature exists"
    )

displayName :: Types.Name -> String
displayName (Types.Unqualified n) = T.unpack n
displayName (Types.Qualified m n) = T.unpack m ++ ":" ++ T.unpack n

-- | Display a single parse error using our 'displayMsgWithSrcLoc' format.
displayParseError :: PE.ParseError -> String
displayParseError err =
  let loc = sourceLocFromPos (PE.errorPos err)
      -- parsec's @show@ on 'ParseError' prepends a line such as
      -- @\"file\" (line N, column M):@ before the actual messages.
      -- Our 'displayMsgWithSrcLoc' renders the location itself, so
      -- strip parsec's prefix to avoid duplication.
      raw = show err
      msg = case dropWhile (/= '\n') raw of
        ('\n' : rest) -> dropWhile (== '\n') rest
        other -> other
   in displayMsgWithSrcLoc parseErrorCode SevError msg loc Nothing Nothing

instance Display Warning where
  displayMsg (RenameWarnings ws) = displayErrors (map displayMsg ws)
  displayMsg (ExhaustivenessWarnings ws) = displayErrors (map displayMsg ws)

instance Display Error where
  displayMsg (ParseError _ err) = displayParseError err
  displayMsg (ParseValidationErrors errs) = displayErrors (map displayMsg errs)
  displayMsg (CollectErrors errs) = displayErrors (map displayMsg errs)
  displayMsg (RenameErrors errs) = displayErrors (map displayMsg errs)
  displayMsg (ResolveErrors errs) = displayErrors (map displayMsg errs)
  displayMsg (DesugarErrors errs) = displayErrors (map displayMsg errs)
  displayMsg (CompileErrors errs) = displayErrors (map displayMsg errs)
  displayMsg (TypeErrors errs) = displayErrors (map displayMsg errs)
  displayMsg (OperatorConflict (AnnP name loc origin)) =
    displayMsgWithSrcLoc
      operatorConflictCode
      SevError
      ( withHint
          ( "Operator conflict: '"
              ++ T.unpack name
              ++ "' is declared with a different fixity or associativity"
              ++ " than an existing operator"
          )
          ( "re-export the existing declaration instead of redeclaring it,"
              ++ " or rename this one"
          )
      )
      loc
      Nothing
      (Just (prettyPExprSrc origin))
  displayMsg (LambdasInLiveQuery loc origin) =
    displayMsgWithSrcLoc
      lambdasInLiveQueryCode
      SevError
      ( withHint
          ( "Anonymous lambdas (fun(...) -> ... end) are not supported"
              ++ " in live REPL sessions"
          )
          ( "lift the lambda into a named :- function declaration in a file"
              ++ " and reload the session"
          )
      )
      loc
      (Just "live session")
      (Just (prettyPExprSrc origin))
  displayMsg (GoalNotAConstraint c reason) =
    displayMsgWithSrcLoc
      goalNotAConstraintCode
      SevError
      ( withHint
          ( case reason of
              NoSuchConstraint ->
                "Goal '" ++ nameArity ++ "' is not a declared constraint"
              AmbiguousConstraint ms ->
                "Goal '"
                  ++ nameArity
                  ++ "' is ambiguous: exported by "
                  ++ intercalate ", " (map T.unpack ms)
              ConstraintNotExported qn ->
                "Goal '"
                  ++ T.unpack (Types.flattenName (Types.qualifiedToName qn))
                  ++ "/"
                  ++ show (length c.args)
                  ++ "' is not exported by its module"
              NotAConstraintItem qn ->
                "Goal '"
                  ++ T.unpack (Types.flattenName (Types.qualifiedToName qn))
                  ++ "/"
                  ++ show (length c.args)
                  ++ "' names a function, not a constraint"
          )
          ( "`ychr run -g GOAL` accepts only a single declared constraint."
              ++ " For expression goals like `1 + 1` or `X is E`,"
              ++ " conjunctions like `a, b`, or function calls,"
              ++ " use `ychr repl` instead — or wrap them in a helper constraint."
          )
      )
      P.dummyLoc
      (Just "<query>")
      Nothing
    where
      nameArity = T.unpack (Types.flattenName c.name) ++ "/" ++ show (length c.args)
  displayMsg (RuntimeError msg stack) = displayErrors (renderFrames msg stack)
    where
      -- An empty stack means the error fired before any 'PushFrame'; we
      -- still produce a runtime-error block, just anchored at 'dummyLoc'.
      renderFrames m [] =
        [displayMsgWithSrcLoc runtimeErrorCode SevRuntimeError m P.dummyLoc Nothing Nothing]
      renderFrames m (top : rest) = renderTop top m : map renderRest rest
      renderTop frame m =
        displayMsgWithSrcLoc
          runtimeErrorCode
          SevRuntimeError
          m
          frame.frameSourceLoc
          (Just (T.unpack frame.frameLabel))
          (Just (T.unpack frame.frameSourceCode))
      renderRest frame =
        displayMsgWithSrcLoc
          runtimeErrorCode
          SevStackTrace
          ""
          frame.frameSourceLoc
          (Just (T.unpack frame.frameLabel))
          (Just (T.unpack frame.frameSourceCode))
