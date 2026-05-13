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
    desugarErrorCode,
    compileErrorCode,
    typeCheckErrorCode,
    parseErrorCode,
    operatorConflictCode,
    lambdasInLiveQueryCode,
    runtimeErrorCode,
  )
where

import Data.Foldable (toList)
import Data.List (dropWhileEnd, intercalate)
import Data.Text (Text)
import Data.Text qualified as T
import Data.Void (Void)
import System.Console.ANSI
  ( Color (..),
    ColorIntensity (..),
    ConsoleIntensity (..),
    ConsoleLayer (..),
    SGR (..),
    setSGRCode,
  )
import Text.Megaparsec
import YCHR.Collect (CollectError (..))
import YCHR.Compile (CompileError (..))
import YCHR.Compile.Pipeline (Error (..), Warning (..))
import YCHR.Desugar (DesugarError (..))
import YCHR.Diagnostic (Diagnostic (..))
import YCHR.Parsed (AnnP (..))
import YCHR.Parsed qualified as P
import YCHR.Parser (ParseValidationError (..))
import YCHR.Pretty (prettyPExprSrc, prettyTermSrc)
import YCHR.Rename (RenameError (..), RenameWarning (..))
import YCHR.Resolve (ResolveError (..))
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

-- | Convert a megaparsec 'SourcePos' to a 'P.SourceLoc'.
sourceLocFromPos :: SourcePos -> P.SourceLoc
sourceLocFromPos sp =
  P.SourceLoc
    { P.file = sourceName sp,
      P.line = unPos (sourceLine sp),
      P.col = unPos (sourceColumn sp)
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

-- | 16xxx — resolve phase (post-rename, pre-desugar)
resolveErrorCode :: ResolveError -> ErrorCode
resolveErrorCode (ConstraintHasEquations _) = ErrorCode 16001
resolveErrorCode (FunctionInRuleHead _) = ErrorCode 16002
resolveErrorCode (ReservedName _) = ErrorCode 16003
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

-- | 2x1xx — rename phase (warnings)
renameWarningCode :: RenameWarning -> ErrorCode
renameWarningCode (UndeclaredDataConstructor _) = ErrorCode 20101
renameWarningCode (DataConstructorArityMismatch _ _) = ErrorCode 20102

-- | 3xxxx — desugar phase
desugarErrorCode :: DesugarError -> ErrorCode
desugarErrorCode (UnexpectedBodyTerm _) = ErrorCode 30001
desugarErrorCode (InvalidLambdaParam _) = ErrorCode 30003

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
desugarErrorMsg (UnexpectedBodyTerm term) =
  withHint
    ("This term is not valid in a rule body: " ++ prettyTermSrc term)
    ( "rule bodies may contain constraints, function calls,"
        ++ " unifications (=), 'is' expressions, and 'true'"
    )
desugarErrorMsg (InvalidLambdaParam term) =
  withHint
    ("Invalid lambda parameter: " ++ prettyTermSrc term)
    "lambda parameters must be variables or the anonymous variable (_)"

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
displayParseError :: PosState Text -> ParseError Text Void -> String
displayParseError posState err =
  let (_, posState') = reachOffset (errorOffset err) posState
      loc = sourceLocFromPos (pstateSourcePos posState')
      msg = dropWhileEnd (== '\n') (parseErrorTextPretty err)
   in displayMsgWithSrcLoc parseErrorCode SevError msg loc Nothing Nothing

instance Display Warning where
  displayMsg (RenameWarnings ws) = displayErrors (map displayMsg ws)

instance Display Error where
  displayMsg (ParseError _ bundle) =
    let posState = bundlePosState bundle
        errs = bundleErrors bundle
     in displayErrors (map (displayParseError posState) (toList errs))
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
