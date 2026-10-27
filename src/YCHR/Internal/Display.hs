{-# LANGUAGE OverloadedStrings #-}

-- | Human-readable error display.
module YCHR.Internal.Display
  ( -- * Types
    Display (..),
    Severity (..),
    ErrorCode (..),

    -- * Displaying
    displaySrcLoc,
    displayMsgWithSrcLoc,
    MsgBlock (..),
    renderSplices,

    -- * Error codes
    displayErrorCode,
    collectErrorCode,
    parseValidationErrorCode,
    resolveErrorCode,
    renameErrorCode,
    declMacroErrorCode,
    renameWarningCode,
    exhaustivenessWarningCode,
    desugarErrorCode,
    compileErrorCode,
    constraintUseErrorCode,
    typeCheckErrorCode,
    typeCheckWarningCode,
    parseErrorCode,
    operatorConflictCode,
    lambdasInLiveQueryCode,
    lambdasInSchemeDriverCode,
    runtimeErrorCode,
    goalNotAConstraintCode,
  )
where

import Data.List (intercalate)
import Data.List.NonEmpty (NonEmpty (..))
import Data.List.NonEmpty qualified as NE
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
import YCHR.Internal.Collect (BareImportHint (..), CollectError (..))
import YCHR.Internal.Compile (CompileError (..))
import YCHR.Internal.Compile.Pipeline
  ( Error (..),
    GoalRejection (..),
    ModuleSplices (..),
    Warning (..),
  )
import YCHR.Internal.ConstraintUse (ConstraintUseError (..), OccurrenceRole (..))
import YCHR.Internal.DeclMacro (DeclMacroError (..))
import YCHR.Internal.Desugar (DesugarError (..))
import YCHR.Internal.Diagnostic (Diagnostic (..))
import YCHR.Internal.Exhaustiveness (ExhaustivenessWarning (..))
import YCHR.Internal.Parsed (AnnP (..), ExpansionStep (..))
import YCHR.Internal.Parsed qualified as P
import YCHR.Internal.Parser (ParseValidationError (..), SourceItem (..))
import YCHR.Internal.Pretty (prettyPExprSrc, prettyTermSrc)
import YCHR.Internal.Rename
  ( BadConjunct (..),
    HeadPart (..),
    NonGoalKind (..),
    RenameError (..),
    RenameWarning (..),
  )
import YCHR.Internal.Rename.Macro
  ( PrimitiveOperand (..),
    macroDepthLimit,
    macroExpansionBudget,
    primitiveOfOperand,
  )
import YCHR.Internal.Resolve
  ( BoundTargetKind (..),
    RefiningViolation (..),
    ResolveError (..),
  )
import YCHR.Internal.Resolved qualified as R
import YCHR.Internal.TypeCheck
  ( ConstructorDecl (..),
    TypeCheckError (..),
    TypeCheckWarning (..),
  )
import YCHR.Internal.Types qualified as Types
import YCHR.Internal.VM (StackFrame (..))

-- | Types that render themselves as user-facing diagnostic text.
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

-- | A stable numeric identifier for a diagnostic class.
newtype ErrorCode = ErrorCode Int
  deriving (Show, Eq, Ord)

-- | Format an error code as @YCHR-NNNNN@.
displayErrorCode :: ErrorCode -> String
displayErrorCode (ErrorCode n) = "YCHR-" ++ show n

-- | Display a source location as @file:line:col@.
displaySrcLoc :: P.SourceLoc -> String
displaySrcLoc loc = loc.file ++ ":" ++ show loc.line ++ ":" ++ show loc.col

-- | Render the @--dump-splices@ report: for each module, a header comment
-- and the clauses its declaration-macro uses spliced, grouped by the
-- outermost use that generated them. Goal macros never appear here (they
-- expand later, in the renamer). See
-- [the macro reference](../../docs/reference/macros.md).
renderSplices :: [ModuleSplices] -> String
renderSplices = intercalate "\n" . map renderModule
  where
    renderModule :: ModuleSplices -> String
    renderModule ms =
      unlines
        ( ( "% splices for "
              ++ ms.file
              ++ " (module "
              ++ T.unpack ms.moduleName
              ++ ")"
          )
            : renderItems Nothing ms.items
        )
    -- A nested use's clauses stay under the outermost use's comment, so
    -- the key is the chain's last step (chains are innermost first).
    -- An item with no chain is user-written and is not dumped.
    renderItems :: Maybe ExpansionStep -> [SourceItem] -> [String]
    renderItems _ [] = []
    renderItems prev (si : rest) = case si.expansion of
      [] -> renderItems prev rest
      chain ->
        let step = last chain
            originLine = ["% " ++ renderStep step | prev /= Just step]
         in originLine
              ++ (prettyPExprSrc si.term.node ++ ".")
              : renderItems (Just step) rest
    renderStep :: ExpansionStep -> String
    renderStep step =
      T.unpack step.macroModule
        ++ ":"
        ++ T.unpack step.macroName
        ++ "/"
        ++ show step.macroArity
        ++ " at "
        ++ displaySrcLoc step.site

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
--   in the expansion of ...
-- ast_node
-- @
--
-- The macro-expansion chain ('MsgBlock.context', from
-- @Diagnostic.context@) is empty for every diagnostic except one raised
-- inside a macro expansion. See docs/reference/macros.md §Diagnostics.
displayMsgWithSrcLoc :: MsgBlock -> String
displayMsgWithSrcLoc block =
  let msg = block.message
      col = severityColor block.severity
      lbl = severityLabel block.severity
      c = setSGRCode [SetColor Foreground Vivid col]
      r = setSGRCode [Reset]
   in c
        ++ "=== "
        ++ lbl
        ++ " ==="
        ++ r
        ++ "\n"
        ++ setSGRCode [SetConsoleIntensity BoldIntensity]
        ++ displaySrcLoc block.loc
        ++ ": "
        ++ displayErrorCode block.code
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
          block.label
        ++ msg
        ++ concatMap (\cl -> "\n  " ++ cl) block.context
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
          block.node
        ++ "\n"
        ++ r

-- | One diagnostic block, as 'displayMsgWithSrcLoc' renders it.
data MsgBlock = MsgBlock
  { code :: ErrorCode,
    severity :: Severity,
    message :: String,
    loc :: P.SourceLoc,
    -- | Shown as @<<label>>@ under the location line.
    label :: Maybe String,
    -- | Source snippet, shown in italics after the message.
    node :: Maybe String,
    -- | Macro-expansion chain, one line each.
    context :: [String]
  }

-- | Render a located diagnostic. Every 'Diagnostic' instance below is
-- this with its own severity, code and message function.
displayDiagnostic ::
  Severity ->
  (e -> ErrorCode) ->
  (e -> String) ->
  Diagnostic e ->
  String
displayDiagnostic sev codeOf msgOf (Diagnostic lbl (AnnP err loc origin) ctx) =
  displayMsgWithSrcLoc
    MsgBlock
      { code = codeOf err,
        severity = sev,
        message = msgOf err,
        loc = loc,
        label = fmap T.unpack lbl,
        node = Just (prettyPExprSrc origin),
        context = map T.unpack ctx
      }

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

-- | Render a qualified name as @mod:name@.
displayQualifiedName :: Types.QualifiedName -> String
displayQualifiedName qn = T.unpack (Types.flattenName (Types.qualifiedToName qn))

-- | Render arities as "2", "1 or 3", "1, 2 or 3".
displayArityList :: NonEmpty Int -> String
displayArityList (n :| []) = show n
displayArityList ns =
  intercalate ", " (map show (NE.init ns)) ++ " or " ++ show (NE.last ns)

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
collectErrorCode (SelfNamedLibraryImport _) = ErrorCode 10003
collectErrorCode (DuplicateModuleName _ _) = ErrorCode 10004
collectErrorCode (UnknownModuleImport _ _) = ErrorCode 10005

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
parseValidationErrorCode InvalidTypeParameter = ErrorCode 15018
parseValidationErrorCode (DuplicateTypeParameter _) = ErrorCode 15019
parseValidationErrorCode RefiningOnConstraint = ErrorCode 15020
parseValidationErrorCode MalformedMacroHead = ErrorCode 15021
parseValidationErrorCode MalformedMacroBody = ErrorCode 15022
parseValidationErrorCode (UndeclaredMacroClause _ _) = ErrorCode 15025
parseValidationErrorCode (DiscontiguousMacroClauses _ _) = ErrorCode 15026
parseValidationErrorCode (DeclMacroBuiltinDirective _ _) = ErrorCode 15027
parseValidationErrorCode (MalformedDirective _) = ErrorCode 15028

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
resolveErrorCode (UnknownBoundFunction _ _ _ _) = ErrorCode 16009
resolveErrorCode (BoundCycle _) = ErrorCode 16010
resolveErrorCode (MultiSigOnFunction _) = ErrorCode 16011
resolveErrorCode (MixedDeclKinds _) = ErrorCode 16012
resolveErrorCode (ExtendClassTypeOnFunction _) = ErrorCode 16013
resolveErrorCode (ExtendClassOnFunction _) = ErrorCode 16014
resolveErrorCode (ExtendFunctionOnClass _) = ErrorCode 16015
resolveErrorCode (ConstraintFunctionCollision _) = ErrorCode 16016
resolveErrorCode (ConstructorFunctionCollision _) = ErrorCode 16020
resolveErrorCode (InvalidRefining _ _) = ErrorCode 16021
resolveErrorCode (LambdaParamError _) = ErrorCode 16017
resolveErrorCode EmptyLambdaParams = ErrorCode 16018
resolveErrorCode (UnsupportedCallArity _) = ErrorCode 16022
resolveErrorCode (InlineUnknownFunction _ _) = ErrorCode 16023
resolveErrorCode (InlineOpenFunction _ _) = ErrorCode 16024
resolveErrorCode (ConstraintUseUnknownConstraint _ _) = ErrorCode 16025
resolveErrorCode (ConstraintUseConflictingDeclaration _ _) = ErrorCode 16026

-- | 2xxxx — rename phase (errors).
-- Code 20004 is reserved: operators are permitted in import lists
-- (see UnknownOperatorImport).
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
renameErrorCode (ConstructorFunctionAmbiguity _ _ _) = ErrorCode 20020
renameErrorCode (ModuleNotImported _ _ _) = ErrorCode 20014
renameErrorCode (UnknownModule _) = ErrorCode 20015
renameErrorCode (ReservedTypeName _ _) = ErrorCode 20016
renameErrorCode (DuplicateTypeDeclaration _ _) = ErrorCode 20017
renameErrorCode (TypeShadowsImport _ _ _) = ErrorCode 20018
renameErrorCode PreludeImportList = ErrorCode 20019
renameErrorCode DisjunctionWithoutSearch = ErrorCode 20021
renameErrorCode DisjunctionNotInRuleBody = ErrorCode 20022
renameErrorCode (DuplicateMacro _ _) = ErrorCode 20023
renameErrorCode (MacroNameCollision _ _) = ErrorCode 20024
renameErrorCode (MacroOutsideGoalPosition _ _) = ErrorCode 20025
renameErrorCode (MacroCycle _ _) = ErrorCode 20026
renameErrorCode (MacroBodyNotExported _ _ _ _) = ErrorCode 20027
renameErrorCode (MacroInvalidInHead _ _) = ErrorCode 20028
renameErrorCode (TellOutsideGoalPosition _) = ErrorCode 20029
renameErrorCode (UnsupportedTellArity _) = ErrorCode 20030
renameErrorCode (TellControlGoal _ _) = ErrorCode 20031
renameErrorCode (NoMatchingMacroClause _ _) = ErrorCode 20032
renameErrorCode (MacroExpansionTooDeep _ _) = ErrorCode 20033
renameErrorCode (MacroEmptyHead _) = ErrorCode 20034
renameErrorCode (MacroKindMismatch _ _ _) = ErrorCode 20035
renameErrorCode (MalformedMacroPrimitive _ _) = ErrorCode 20036
renameErrorCode (MacroPrimitiveOutsideMacro _ _) = ErrorCode 20037
renameErrorCode (MacroExpansionTooLarge _ _) = ErrorCode 20038
renameErrorCode AggregateOnlyHead = ErrorCode 20039
renameErrorCode (AggregateOutsideHead _ _) = ErrorCode 20040
renameErrorCode (MalformedAggregateGoal _) = ErrorCode 20041
renameErrorCode GuardOutsideAggregateGoal = ErrorCode 20042
renameErrorCode (ReservedAggregateName _ _) = ErrorCode 20043

-- | Declaration-macro expansion. Its own errors are 15xxx, raised
-- before conversion to the AST; the renamer's errors it raises keep
-- their 20xxx codes, and conversion errors in spliced clauses their
-- 15xxx parse-validation codes.
declMacroErrorCode :: DeclMacroError -> ErrorCode
declMacroErrorCode (MacroDeclsForbiddenClause _) = ErrorCode 15023
declMacroErrorCode (UnknownDirective _ _) = ErrorCode 15024
declMacroErrorCode (DeclMacroRenameError e) = renameErrorCode e
declMacroErrorCode (DeclMacroParseError e) = parseValidationErrorCode e

-- | 2x1xx — rename phase (warnings)
renameWarningCode :: RenameWarning -> ErrorCode
renameWarningCode (UndeclaredDataConstructor _) = ErrorCode 20101
renameWarningCode (DataConstructorArityMismatch _ _ _) = ErrorCode 20102
renameWarningCode (UnusedMacroParameter _ _) = ErrorCode 20105

-- | 2x1xx — exhaustiveness warnings (a pattern-matching warning, in the
-- same warning band as the rename warnings).
exhaustivenessWarningCode :: ExhaustivenessWarning -> ErrorCode
exhaustivenessWarningCode (NonExhaustiveMatch _ _) = ErrorCode 20103

-- | 2x1xx — type-check warnings. The type checker's /errors/ live in
-- the 6xxxx band, but its warnings join the shared warning band so
-- every @--Werror@-eligible diagnostic carries a @2x1xx@ code.
typeCheckWarningCode :: TypeCheckWarning -> ErrorCode
typeCheckWarningCode (InaccessibleBranch _ _) = ErrorCode 20104
typeCheckWarningCode (AggregateGoalInaccessible _ _) = ErrorCode 20106

-- | 3xxxx — desugar phase
desugarErrorCode :: DesugarError -> ErrorCode
desugarErrorCode (UnexpectedBodyExpr _) = ErrorCode 30001
desugarErrorCode (NonBooleanGuard _) = ErrorCode 30002
desugarErrorCode (NonPreludeFunctionBodyItem _) = ErrorCode 30003
desugarErrorCode (NonVariableIsInFunctionBody _) = ErrorCode 30004
desugarErrorCode DisjunctionInQuery = ErrorCode 30006
desugarErrorCode (InlineNotSingleEquation _ _) = ErrorCode 30007
desugarErrorCode (InlineGuardedEquation _) = ErrorCode 30008
desugarErrorCode (InlineStatefulEquation _) = ErrorCode 30009
desugarErrorCode (InlineCycle _) = ErrorCode 30010

-- | 4xxxx — compile phase
compileErrorCode :: CompileError -> ErrorCode
compileErrorCode (UnknownConstraintType _) = ErrorCode 40001
compileErrorCode (UnboundVariable _) = ErrorCode 40002
compileErrorCode (AggregateLocalEscapes _) = ErrorCode 40003
compileErrorCode (AggregateNestedTake _) = ErrorCode 40004
compileErrorCode AggregateResultNotMaybe = ErrorCode 40005

-- | 45xxx — constraint-use check. Its own bucket rather than the type
-- checker's 6xxxx band: the pass is independent of the CHR checker,
-- even though @--no-check@ gates the two together.
constraintUseErrorCode :: ConstraintUseError -> ErrorCode
constraintUseErrorCode (ConstraintUseViolation _ _ _ _) = ErrorCode 45001

-- | 6xxxx — type-check phase
typeCheckErrorCode :: TypeCheckError -> ErrorCode
typeCheckErrorCode (InconsistentTypes _ _) = ErrorCode 60001
typeCheckErrorCode (UnboundTypeVar _ _ _) = ErrorCode 60004
typeCheckErrorCode (UndefinedType _ _ _) = ErrorCode 60005
typeCheckErrorCode (NoMatchingOverload _) = ErrorCode 60006
typeCheckErrorCode (DuplicateConstructor _ _) = ErrorCode 60007
typeCheckErrorCode (ConstructorArityMismatch _ _ _) = ErrorCode 60008
typeCheckErrorCode (BoundUnsatisfied _) = ErrorCode 60012
typeCheckErrorCode (TypeRefArityMismatch _ _ _ _ _) = ErrorCode 60013
typeCheckErrorCode (AggregateTypeEscapes _) = ErrorCode 60014
typeCheckErrorCode (AggregateLinkConflict _ _) = ErrorCode 60015
typeCheckErrorCode (UndeterminedInstance _ _) = ErrorCode 60016

-- | 5xxxx — top-level errors.
--
-- These standalone code constants are not attached to an enumerable error
-- constructor, so the uniqueness guard in @test/YCHR/ErrorCodeTest.hs@
-- cannot discover them by reflection: any new constant added below must
-- also be listed in that test's @standaloneCodes@.
parseErrorCode :: ErrorCode
parseErrorCode = ErrorCode 50001

-- | 5xxxx — an operator redeclared with a different fixity or associativity.
operatorConflictCode :: ErrorCode
operatorConflictCode = ErrorCode 50002

-- | 5xxxx — a live session received an anonymous lambda.
lambdasInLiveQueryCode :: ErrorCode
lambdasInLiveQueryCode = ErrorCode 50003

-- | 5xxxx — `ychr gen-driver` received an anonymous lambda in a goal argument.
lambdasInSchemeDriverCode :: ErrorCode
lambdasInSchemeDriverCode = ErrorCode 50004

-- | 20013 — @ychr run -g GOAL@ received a goal that is not a single
-- declared constraint (bare expression, conjunction, function call,
-- or an unknown name). Lives in the rename/resolution range because
-- the rejection is about goal-name resolution, not runtime behavior.
goalNotAConstraintCode :: ErrorCode
goalNotAConstraintCode = ErrorCode 20013

-- | 6xxxx — shared with type-check; 60001 is also used for runtime errors
-- raised by 'YCHR.Internal.Runtime.Error.runtimeError''/'runtimeErrorS'.
runtimeErrorCode :: ErrorCode
runtimeErrorCode = ErrorCode 60001

-- ---------------------------------------------------------------------------
-- Display instances
-- ---------------------------------------------------------------------------

instance Display (P.AnnP ParseValidationError) where
  displayMsg (AnnP err loc origin) =
    displayMsgWithSrcLoc
      MsgBlock
        { code = parseValidationErrorCode err,
          severity = SevError,
          message = parseValidationErrorMsg err,
          loc = loc,
          label = Nothing,
          node = Just (prettyPExprSrc origin),
          context = []
        }

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
parseValidationErrorMsg RefiningOnConstraint =
  withHint
    "'refining' is not allowed on ':- chr_constraint'"
    ( "only a function can be a refinement predicate; declare it with"
        ++ " ':- function name(any) -> bool refining type'"
    )
parseValidationErrorMsg MalformedMacroHead =
  withHint
    "Invalid macro head"
    ( "expected ':- macro Name/N', ':- macro Head ---> [Goals]' (or the same"
        ++ " with ':- macro_decls'), or a"
        ++ " clause 'Head ---> [Goals]', where Head is an atom or a compound"
        ++ " whose arguments are patterns; the name may not be qualified or"
        ++ " a reserved symbol (',', ';', '\\\\', '|', '->', '=', 'is',"
        ++ " 'true', 'quote', 'fun', '$call', 'tell', '$compound', '$atom')"
    )
parseValidationErrorMsg MalformedMacroBody =
  withHint
    "Invalid macro body: expected a list literal"
    ( "write the body as a list of goals, e.g. ':- macro both(X) ---> [a(X), b(X)].';"
        ++ " '[]' expands to nothing, and a tail variable ('[G | Gs]') is not allowed"
    )
parseValidationErrorMsg (UndeclaredMacroClause name arity) =
  withHint
    ( "Macro clause for '"
        ++ T.unpack name
        ++ "/"
        ++ show arity
        ++ "', which is not declared as a macro in this module"
    )
    ( "declare it with ':- macro "
        ++ T.unpack name
        ++ "/"
        ++ show arity
        ++ ".' (goal macro) or ':- macro_decls "
        ++ T.unpack name
        ++ "/"
        ++ show arity
        ++ ".' (declaration macro)"
    )
parseValidationErrorMsg (DiscontiguousMacroClauses name arity) =
  withHint
    ( "Clauses for macro '"
        ++ T.unpack name
        ++ "/"
        ++ show arity
        ++ "' must be contiguous"
    )
    "move all of the macro's clauses together"
parseValidationErrorMsg (DeclMacroBuiltinDirective name arity) =
  withHint
    ( "Declaration macro '"
        ++ T.unpack name
        ++ "/"
        ++ show arity
        ++ "' has the name and arity of a built-in directive"
    )
    ( "a declaration macro is used as a directive, so ':- "
        ++ T.unpack name
        ++ "(...)' would always mean the built-in one; rename the macro"
        ++ " or give it another arity"
    )
parseValidationErrorMsg (MalformedDirective name) =
  withHint
    ("Invalid ':- " ++ T.unpack name ++ "' directive")
    "check its arguments; see the language reference for its form"
parseValidationErrorMsg MalformedDeclaration =
  withHint
    "Invalid declaration"
    ( "expected name/arity, name(types) -> ret, sig requiring bounds,"
        ++ " or sig refining type"
    )
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
    ( "expected 'name(t1, ..., tn) -> tret' or 'module:name(t1, ..., tn)"
        ++ " -> tret' (arity zero: 'name -> tret' / 'module:name -> tret')"
    )
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
parseValidationErrorMsg InvalidTypeParameter =
  withHint
    "Invalid type parameter"
    ( "type parameters must be distinct named variables"
        ++ " (a wildcard '_' is not a usable parameter)"
    )
parseValidationErrorMsg (DuplicateTypeParameter v) =
  withHint
    ("Duplicate type parameter '" ++ T.unpack v ++ "'")
    "type parameters must be distinct variables"

instance Display (Diagnostic ResolveError) where
  displayMsg = displayDiagnostic SevError resolveErrorCode resolveErrorMsg

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
    -- One hint per name in 'reservedModuleNames', plus a fallback.
    ( case name of
        "host" -> "'host' is the wired-in host-call qualifier; rename the module"
        "prelude" ->
          "'prelude' is the bundled prelude, imported implicitly by every "
            ++ "module; rename the module"
        _ -> "rename the module"
    )
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
resolveErrorMsg (InvalidRefining declName violation) =
  withHint
    ( "Invalid 'refining' clause on '"
        ++ T.unpack declName
        ++ "': "
        ++ refiningViolationMsg violation
    )
    ( "'refining' is allowed only on a closed ':- function' with a single"
        ++ " typed signature 'name(any) -> bool', and the refined type must"
        ++ " be a base type or a type constructor applied to distinct type"
        ++ " variables"
    )
resolveErrorMsg (UnknownBoundFunction declName boundName arity kind) =
  withHint
    (unknownBoundFunctionSentence declName boundName arity kind)
    (unknownBoundFunctionHint boundName arity kind)
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
resolveErrorMsg (UnsupportedCallArity arity) =
  withHint
    ( "'$call' takes between 1 and "
        ++ show R.maxCallArity
        ++ " arguments, but was given "
        ++ show arity
    )
    ( "apply the callable to between 1 and "
        ++ show R.maxCallArity
        ++ " arguments"
    )
resolveErrorMsg (InlineUnknownFunction name arity) =
  withHint
    ( "':- inline' names '"
        ++ T.unpack name
        ++ "/"
        ++ show arity
        ++ "', which this module does not declare"
    )
    ( "':- inline' can only target a function declared with :- function / :- class"
        ++ " in the same module"
    )
resolveErrorMsg (InlineOpenFunction name arity) =
  withHint
    ( "':- inline' targets '"
        ++ T.unpack name
        ++ "/"
        ++ show arity
        ++ "', which is declared as :- open_function / :- open_class"
    )
    "an open function's equation set is not fixed here, so it cannot be inlined"
resolveErrorMsg (ConstraintUseUnknownConstraint name arity) =
  withHint
    ( "':- constraint_use' names '"
        ++ T.unpack name
        ++ "/"
        ++ show arity
        ++ "', which this module does not declare with :- chr_constraint"
    )
    "':- constraint_use' can only target a constraint declared in the same module"
resolveErrorMsg (ConstraintUseConflictingDeclaration name arity) =
  withHint
    ( "':- constraint_use' names '"
        ++ T.unpack name
        ++ "/"
        ++ show arity
        ++ "' more than once"
    )
    "give each constraint a single ':- constraint_use' entry"
resolveErrorMsg (ConstraintFunctionCollision name) =
  withHint
    ( "'"
        ++ displayName name
        ++ "' is declared as both :- chr_constraint and a function-like"
        ++ " form in the same module"
    )
    "constraints and functions share the symbol namespace; pick one form for this name"
resolveErrorMsg (ConstructorFunctionCollision name) =
  withHint
    ( "'"
        ++ displayName name
        ++ "' is declared as both a data constructor and a function-like"
        ++ " form in the same module"
    )
    ( "qualifying cannot tell them apart inside one module; rename one of"
        ++ " them (arity does not separate them either)"
    )

-- | Headline for 'UnknownBoundFunction'.
unknownBoundFunctionSentence :: T.Text -> Types.Name -> Int -> BoundTargetKind -> String
unknownBoundFunctionSentence declName boundName arity BoundTargetMissing =
  "'"
    ++ T.unpack declName
    ++ "' requires "
    ++ boundNameSlashArity boundName arity
    ++ " but no such function is declared"
unknownBoundFunctionSentence _ boundName arity BoundTargetConstraint =
  boundNameSlashArity boundName arity ++ " is a constraint, not a function"
unknownBoundFunctionSentence _ boundName arity BoundTargetConstructor =
  boundNameSlashArity boundName arity ++ " is a data constructor, not a function"

boundNameSlashArity :: Types.Name -> Int -> String
boundNameSlashArity boundName arity =
  "'" ++ T.unpack (Types.flattenName boundName) ++ "/" ++ show arity ++ "'"

-- | Hint for 'UnknownBoundFunction'. Only a missing user name can be
-- fixed by declaring it; a @host:@ name, a constraint or a
-- constructor gets 'requiringNamesAFunction'.
unknownBoundFunctionHint :: Types.Name -> Int -> BoundTargetKind -> String
unknownBoundFunctionHint _ _ BoundTargetConstraint = requiringNamesAFunction
unknownBoundFunctionHint _ _ BoundTargetConstructor = requiringNamesAFunction
unknownBoundFunctionHint (Types.Unqualified n) arity BoundTargetMissing =
  "declare ':- function "
    ++ T.unpack n
    ++ "/"
    ++ show arity
    ++ ".' (or import a module that does)"
unknownBoundFunctionHint (Types.Qualified "host" n) arity BoundTargetMissing =
  "'host:"
    ++ T.unpack n
    ++ "/"
    ++ show arity
    ++ "' is a host call, not a declared function; "
    ++ requiringNamesAFunction
unknownBoundFunctionHint (Types.Qualified m n) arity BoundTargetMissing =
  "declare ':- function "
    ++ T.unpack n
    ++ "/"
    ++ show arity
    ++ ".' in module '"
    ++ T.unpack m
    ++ "'"

requiringNamesAFunction :: String
requiringNamesAFunction =
  "'requiring' can only name a declared function (':- function',"
    ++ " ':- open_function', ':- class', or ':- open_class')"

-- | The specific problem with a 'refining' clause, as a sentence
-- fragment following the declaration's name.
refiningViolationMsg :: RefiningViolation -> String
refiningViolationMsg RefiningOnClass =
  "':- class' and ':- open_class' cannot carry one"
refiningViolationMsg RefiningOnOpenDeclaration =
  "an open declaration cannot carry one"
refiningViolationMsg RefiningOnUntyped =
  "the untyped 'name/arity' form cannot carry one"
refiningViolationMsg (RefiningArity n) =
  "a refinement predicate must be unary, but this one has arity " ++ show n
refiningViolationMsg RefiningArgNotAny =
  "the argument type must be 'any'"
refiningViolationMsg RefiningReturnNotBool =
  "the return type must be 'bool'"
refiningViolationMsg RefiningBareVariable =
  "the refined type must not be a bare type variable, which says nothing"
refiningViolationMsg RefiningAny =
  "the refined type must not be 'any', which says nothing"
refiningViolationMsg RefiningFunctionType =
  "the refined type must not be a function type"
refiningViolationMsg RefiningConcreteParameter =
  ( "the refined type must be a base type or a type constructor applied"
      ++ " to distinct type variables (a parameter is a concrete type; only"
      ++ " the outermost constructor is proved)"
  )
refiningViolationMsg (RefiningRepeatedParameter v) =
  ( "the refined type must be a base type or a type constructor applied"
      ++ " to distinct type variables (parameter '"
      ++ T.unpack v
      ++ "' is repeated)"
  )

instance Display (Diagnostic CollectError) where
  displayMsg = displayDiagnostic SevError collectErrorCode collectErrorMsg

collectErrorMsg :: CollectError -> String
collectErrorMsg (UnknownLibrary name) =
  withHint
    ("Unknown library '" ++ T.unpack name ++ "'")
    "check the library name; the built-in libraries are bundled with the compiler"
collectErrorMsg (CircularLibraryImport names) =
  "Circular library import: "
    ++ intercalate " -> " (map T.unpack names)
collectErrorMsg (SelfNamedLibraryImport name) =
  withHint
    ("Module '" ++ T.unpack name ++ "' imports a library with its own name")
    ( "the bundled library '"
        ++ T.unpack name
        ++ "' is replaced by this module; rename the module or drop the import"
    )
collectErrorMsg (DuplicateModuleName name []) =
  withHint
    ("Module '" ++ T.unpack name ++ "' is declared in more than one input")
    "a module name may be declared in exactly one input; give the modules distinct names"
collectErrorMsg (DuplicateModuleName name paths) =
  withHint
    ( "Module '"
        ++ T.unpack name
        ++ "' is declared in more than one input file: "
        ++ intercalate ", " paths
    )
    "a module name may be declared in exactly one input; give the modules distinct names"
collectErrorMsg (UnknownModuleImport name hint) =
  withHint
    ("Unknown module '" ++ T.unpack name ++ "'")
    (bareImportHintText name hint)

-- | The hint text for 'UnknownModuleImport', picked by 'BareImportHint'.
bareImportHintText :: T.Text -> BareImportHint -> String
bareImportHintText name BundledLibraryName =
  "'"
    ++ T.unpack name
    ++ "' is a bundled library; import it with ':- use_module(library("
    ++ T.unpack name
    ++ ")).'"
bareImportHintText _ HostQualifier =
  "'host:' is a built-in qualifier and needs no import"
bareImportHintText name HeaderlessModule =
  "a file without a ':- module' header is named '<"
    ++ T.unpack name
    ++ ">'; give it a ':- module("
    ++ T.unpack name
    ++ ")' header"
bareImportHintText _ NoBareImportHint =
  "a bare use_module names a module supplied to the compiler;"
    ++ " check the name, or pass the module's file"

instance Display (Diagnostic DeclMacroError) where
  displayMsg = displayDiagnostic SevError declMacroErrorCode declMacroErrorMsg

declMacroErrorMsg :: DeclMacroError -> String
declMacroErrorMsg (MacroDeclsForbiddenClause form) =
  withHint
    ("A declaration macro may not generate " ++ forbiddenFormText form)
    ( "an expansion cannot change a module's imports, exports, operators or"
        ++ " macros; write them in the module itself"
    )
  where
    forbiddenFormText f = case f of
      "--->" -> "a macro clause ('Head ---> Body')"
      _ -> "a ':- " ++ T.unpack f ++ "' directive"
declMacroErrorMsg (UnknownDirective name arity) =
  withHint
    ("Unknown directive '" ++ T.unpack name ++ "/" ++ show arity ++ "'")
    ( "a directive is a built-in one or a use of a visible declaration macro"
        ++ " (':- macro_decls'); check the spelling and the imports, and delete"
        ++ " foreign Prolog directives such as ':- dynamic'"
    )
declMacroErrorMsg (DeclMacroRenameError e) = renameErrorMsg e
declMacroErrorMsg (DeclMacroParseError e) = parseValidationErrorMsg e

instance Display (Diagnostic RenameError) where
  displayMsg = displayDiagnostic SevError renameErrorCode renameErrorMsg

-- | Hint for a bad aggregate goal conjunct.
aggregateConjunctHint :: String
aggregateConjunctHint =
  "an aggregate goal conjunct must be a constraint, a nested aggregate"
    ++ " or a '?' guard"

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
    ( "check the spelling and the export list of '"
        ++ T.unpack modName
        ++ "'"
    )
renameErrorMsg (ModuleNotImported modName name arity) =
  withHint
    ( "Module '"
        ++ T.unpack modName
        ++ "' is not imported (referenced as '"
        ++ T.unpack modName
        ++ ":"
        ++ T.unpack name
        ++ "/"
        ++ show arity
        ++ "')"
    )
    ( "add ':- use_module("
        ++ T.unpack modName
        ++ ").' (or ':- use_module(library("
        ++ T.unpack modName
        ++ ")).' for a bundled library)"
    )
renameErrorMsg (UnknownModule modName) =
  withHint
    ("No module named '" ++ T.unpack modName ++ "'")
    "check the module name, or declare the module"
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
renameErrorMsg PreludeImportList =
  withHint
    "use_module(prelude) cannot carry an import list"
    ( "the prelude is imported implicitly and in full by every module;"
        ++ " remove the import list"
    )
renameErrorMsg DisjunctionWithoutSearch =
  withHint
    "the disjunction operator ';' needs library(search)"
    ( "';' compiles to a search:alt/1 choice point; add"
        ++ " :- use_module(library(search))."
    )
renameErrorMsg DisjunctionNotInRuleBody =
  withHint
    "the disjunction operator ';' is only valid in a rule body"
    ( "';' chooses between goals, and a guard, an 'is' right-hand side"
        ++ " and a function body have none; use quote/1 to write a ';'"
        ++ " term as data"
    )
renameErrorMsg (DuplicateMacro name arity) =
  withHint
    ("Duplicate macro '" ++ T.unpack name ++ "/" ++ show arity ++ "'")
    ( "a macro has one definition: a one-line ':- macro Head ---> Body', or"
        ++ " ':- macro Name/N' followed by its clauses (same for ':- macro_decls');"
        ++ " goal and declaration macros share names; remove or rename one"
    )
renameErrorMsg (MacroKindMismatch qn arity kind) = case kind of
  P.GoalMacro ->
    withHint
      ( "Goal macro '"
          ++ displayQualifiedName qn
          ++ "/"
          ++ show arity
          ++ "' used as a directive"
      )
      ( "a goal macro (':- macro') is used in a goal position; a directive"
          ++ " can only use a declaration macro (':- macro_decls')"
      )
  P.DeclMacro ->
    withHint
      ( "Declaration macro '"
          ++ displayQualifiedName qn
          ++ "/"
          ++ show arity
          ++ "' used in a goal position"
      )
      ( "a declaration macro (':- macro_decls') is used as a directive,"
          ++ " ':- "
          ++ T.unpack qn.baseName
          ++ "(...).'; a goal position can only use a goal macro (':- macro')"
      )
renameErrorMsg (MacroNameCollision qn arity) =
  withHint
    ( "Macro '"
        ++ displayQualifiedName qn
        ++ "/"
        ++ show arity
        ++ "' collides with a constraint or function of the same name"
    )
    "a macro and a constraint/function cannot share a name/arity in one module"
renameErrorMsg (MacroOutsideGoalPosition qn arity) =
  withHint
    ( "Macro '"
        ++ displayQualifiedName qn
        ++ "/"
        ++ show arity
        ++ "' used outside a goal position"
    )
    ( "macros are recognized only in a rule head, a rule body, or a query"
        ++ " goal; use quote/1 if you meant the bare compound as data"
    )
renameErrorMsg (TellOutsideGoalPosition arity) =
  withHint
    ("tell/" ++ show arity ++ " used outside a goal position")
    ( "tell/N tells a constraint, so it is only valid as a goal of a rule"
        ++ " body or a query; use quote/1 to write a tell term as data"
    )
renameErrorMsg (TellControlGoal n arity) =
  withHint
    ( "tell's goal '"
        ++ T.unpack n
        ++ "'/"
        ++ show arity
        ++ " is a control form, not a constraint"
    )
    "write the goal directly in the rule body; tell/N only tells constraints"
renameErrorMsg (UnsupportedTellArity arity) =
  withHint
    ("tell/" ++ show arity ++ " is not supported")
    ( "tell takes a goal followed by up to "
        ++ show (R.maxTellArity - 1)
        ++ " arguments to append to it (tell/1 to tell/"
        ++ show R.maxTellArity
        ++ ")"
    )
renameErrorMsg (MacroCycle qn arity) =
  withHint
    ( "Macro '"
        ++ displayQualifiedName qn
        ++ "/"
        ++ show arity
        ++ "' expansion has no finite form"
    )
    ( "a use of this macro is reached again, with identical arguments,"
        ++ " while it is still being expanded; see the expansion chain"
    )
renameErrorMsg (NoMatchingMacroClause qn args) =
  withHint
    ( "No clause of macro '"
        ++ displayQualifiedName qn
        ++ "/"
        ++ show (length args)
        ++ "' matches the use '"
        ++ prettyTermSrc (Types.CompoundTerm (Types.Unqualified qn.baseName) args)
        ++ "'"
    )
    ( "macro clause heads are matched against the arguments as written,"
        ++ " before any evaluation or name resolution"
    )
renameErrorMsg (MacroExpansionTooDeep qn arity) =
  withHint
    ( "Macro '"
        ++ displayQualifiedName qn
        ++ "/"
        ++ show arity
        ++ "': nested expansions exceed the depth limit of "
        ++ show macroDepthLimit
    )
    ( "check that each recursive use makes progress towards a base case;"
        ++ " see the expansion chain"
    )
renameErrorMsg (MacroEmptyHead part) =
  withHint
    ("The " ++ partText ++ " of this rule is empty after macro expansion")
    ( "a macro expanded to no constraints where the rule's form requires"
        ++ " at least one"
    )
  where
    partText = case part of
      WholeHead -> "head"
      KeptPart -> "kept part"
      RemovedPart -> "removed part"
renameErrorMsg (MacroExpansionTooLarge qn arity) =
  withHint
    ( "Macro '"
        ++ displayQualifiedName qn
        ++ "/"
        ++ show arity
        ++ "': one use causes more than "
        ++ show macroExpansionBudget
        ++ " expansions"
    )
    ( "a macro whose clauses use it more than once can grow exponentially;"
        ++ " see the expansion chain"
    )
renameErrorMsg (MalformedMacroPrimitive operand received) =
  withHint
    ( "Invalid "
        ++ operandText
        ++ " of '"
        ++ T.unpack (primitiveOfOperand operand)
        ++ "': "
        ++ prettyTermSrc received
    )
    ( case primitiveOfOperand operand of
        "$compound" ->
          "'$compound'(F, [A1, ..., An]) needs an atom or a qualified name"
            ++ " M:f as F, and a proper list of arguments"
        _ ->
          "'$atom'([P1, ..., Pn]) needs a proper, non-empty list of"
            ++ " unqualified atoms and integers, whose concatenation is"
            ++ " non-empty and contains neither '__' nor '%%u'"
    )
  where
    operandText = case operand of
      CompoundFunctor -> "functor"
      CompoundArgs -> "argument list"
      AtomParts -> "part list"
      AtomPart -> "part"
      AtomResult -> "result"
renameErrorMsg (MacroPrimitiveOutsideMacro prim arity) =
  withHint
    ( "Construction primitive '"
        ++ T.unpack prim
        ++ "'/"
        ++ show arity
        ++ " is not written in a macro body"
    )
    ( "'$compound'/2 and '$atom'/1 are evaluated only where they are"
        ++ " written in a macro body; the two names are reserved"
    )
renameErrorMsg AggregateOnlyHead =
  withHint
    "A rule head consists of aggregates only"
    ( "an aggregate reads the store, so the rule needs at least one"
        ++ " regular head constraint to fire on"
    )
renameErrorMsg (AggregateOutsideHead name arity) =
  withHint
    ("Aggregate '" ++ T.unpack name ++ "/" ++ show arity ++ "' outside a rule head")
    ( "an aggregate decides whether a rule applies, so it is a head"
        ++ " conjunct; it cannot appear anywhere else"
    )
renameErrorMsg (MalformedAggregateGoal (ConjunctIsFunction name arity)) =
  withHint
    ( "'"
        ++ displayName name
        ++ "/"
        ++ show arity
        ++ "' in an aggregate goal is a function, not a constraint"
    )
    "a test on each match is a guard conjunct: write '? Guard'"
renameErrorMsg (MalformedAggregateGoal (ConjunctIsBuiltin name arity)) =
  withHint
    ( "'"
        ++ T.unpack name
        ++ "/"
        ++ show arity
        ++ "' in an aggregate goal is a built-in form, not a constraint"
    )
    aggregateConjunctHint
renameErrorMsg (MalformedAggregateGoal (ConjunctNotAGoal kind)) =
  withHint
    (what kind ++ " in an aggregate goal is not a constraint")
    aggregateConjunctHint
  where
    what NonGoalNumber = "A number"
    what NonGoalString = "A string"
    what NonGoalVariable = "A variable"
renameErrorMsg GuardOutsideAggregateGoal =
  withHint
    "'?' guard outside an aggregate goal"
    ( "a '? Guard' conjunct is recognized inside an aggregate's goal;"
        ++ " write a rule guard with '|' and a body goal directly"
    )
renameErrorMsg (ReservedAggregateName name arity) =
  withHint
    ( "'"
        ++ T.unpack name
        ++ "/"
        ++ show arity
        ++ "' is an aggregate form and cannot be declared as a"
        ++ " constraint, function or macro"
    )
    ( "aggregate/4, argmin/2, argmax/2, takemin/2 and takemax/2 are"
        ++ " recognized in every rule head without an import; choose"
        ++ " another name or arity"
    )
renameErrorMsg (MacroBodyNotExported macroName macroArity refName refArity) =
  withHint
    ( "Macro '"
        ++ displayQualifiedName macroName
        ++ "/"
        ++ show macroArity
        ++ "' refers to '"
        ++ T.unpack macroName.moduleName
        ++ ":"
        ++ T.unpack refName
        ++ "/"
        ++ show refArity
        ++ "', which its own module does not declare and export"
    )
    ( "a macro body's self-qualified references must be exported,"
        ++ " or every use of the macro would fail"
    )
renameErrorMsg (MacroInvalidInHead qn arity) =
  withHint
    ( "Macro '"
        ++ displayQualifiedName qn
        ++ "/"
        ++ show arity
        ++ "' expands to something other than a conjunction of constraints"
        ++ " in head position"
    )
    ( "a rule head is a conjunction of constraints;"
        ++ " move the macro use into the body instead"
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
renameErrorMsg (ConstructorFunctionAmbiguity name conMods funMods) =
  withHint
    ( "'"
        ++ T.unpack name
        ++ "' is both a data constructor (declared in "
        ++ intercalate ", " (map T.unpack conMods)
        ++ ") and a function (declared in "
        ++ intercalate ", " (map T.unpack funMods)
        ++ ")"
    )
    ( "qualify the reference ("
        ++ intercalate
          " or "
          [ T.unpack m ++ ":" ++ T.unpack name
          | m <- take 1 conMods ++ take 1 funMods
          ]
        ++ ") to say which you mean, or rename one of them"
        -- The prelude is imported in full by every module and its
        -- import list cannot be narrowed (YCHR-20019), so "rename
        -- yours" is the only advice that applies to a prelude clash.
        -- Say so only when the prelude is actually one of the sides.
        -- MicroHs's 'Data.List.elem' lacks a fixity declaration and
        -- defaults to 'infixl 9'; the parentheses pin the 'infix 4'
        -- parse that base already produces (dev-docs/MICROHS_GAPS.md, gap 7).
        ++ if "prelude" `elem` (conMods ++ funMods)
          then
            "; the prelude's import cannot be narrowed, so renaming your"
              ++ " own constructor is the way out of a prelude clash"
          else ""
    )
renameErrorMsg (ReservedTypeName name arity) =
  withHint
    ("Type name '" ++ T.unpack name ++ "/" ++ show arity ++ "' is reserved")
    "base types (int, float, string, any) and function-type syntax cannot be redeclared"
renameErrorMsg (DuplicateTypeDeclaration name arity) =
  withHint
    ("Type '" ++ T.unpack name ++ "/" ++ show arity ++ "' is declared more than once")
    "remove or rename one of the declarations"
renameErrorMsg (TypeShadowsImport name arity provider) =
  withHint
    ( "Type '"
        ++ T.unpack name
        ++ "/"
        ++ show arity
        ++ "' collides with a type imported from '"
        ++ T.unpack provider
        ++ "'"
    )
    "rename the local type or narrow the import list"

instance Display (Diagnostic RenameWarning) where
  displayMsg = displayDiagnostic SevWarning renameWarningCode renameWarningMsg

renameWarningMsg :: RenameWarning -> String
renameWarningMsg (UndeclaredDataConstructor name) =
  withHint
    ("Undeclared data constructor '" ++ T.unpack name ++ "'")
    "declare it with :- chr_type, or check the spelling"
renameWarningMsg (DataConstructorArityMismatch name arity declared) =
  "Data constructor '"
    ++ T.unpack name
    ++ "' used with "
    ++ show arity
    ++ " argument(s) but declared with "
    ++ displayArityList declared
renameWarningMsg (UnusedMacroParameter qn param) =
  withHint
    ( "Macro parameter '"
        ++ T.unpack param
        ++ "' of '"
        ++ displayQualifiedName qn
        ++ "' is not used"
    )
    ( "the corresponding argument is dropped; write '_' or prefix the"
        ++ " name with '_' to drop it silently"
    )

instance Display (Diagnostic ExhaustivenessWarning) where
  displayMsg =
    displayDiagnostic
      SevWarning
      exhaustivenessWarningCode
      exhaustivenessWarningMsg

exhaustivenessWarningMsg :: ExhaustivenessWarning -> String
exhaustivenessWarningMsg (NonExhaustiveMatch name witness) =
  withHint
    ( "Non-exhaustive patterns in function '"
        ++ T.unpack name
        ++ "': no equation matches "
        ++ prettyTermSrc witness
    )
    "add an equation for the missing case, or a catch-all variable/wildcard pattern"

instance Display (Diagnostic ConstraintUseError) where
  displayMsg = displayDiagnostic SevError constraintUseErrorCode constraintUseErrorMsg

constraintUseErrorMsg :: ConstraintUseError -> String
constraintUseErrorMsg (ConstraintUseViolation qn arity use role) =
  withHint
    ( "'"
        ++ displayQualifiedName qn
        ++ "/"
        ++ show arity
        ++ "' is declared "
        ++ useDescription
        ++ ", but occurs "
        ++ roleText
        ++ " in this rule head"
    )
    hint
  where
    roleText = case role of
      KeptOccurrence -> "kept"
      RemovedOccurrence -> "removed"
    useDescription = case use of
      Types.UseAny -> "any"
      Types.UseFact -> "fact (kept occurrences only)"
      Types.UseEvent -> "event (removed occurrences only)"
      Types.UseTellOnly -> "tell_only (no rule-head occurrences)"
    hint = case use of
      Types.UseTellOnly ->
        "a tell_only constraint may be told, but never matched in a rule head"
      _ ->
        "move the occurrence to the other side of the rule head,"
          ++ " or change its ':- constraint_use' declaration"

instance Display (Diagnostic DesugarError) where
  displayMsg = displayDiagnostic SevError desugarErrorCode desugarErrorMsg

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
        ++ " (host:f(args)), a function call, or '$call'(F, ...)"
    )
desugarErrorMsg DisjunctionInQuery =
  withHint
    "the disjunction operator ';' is not valid at the top level of a query"
    ( "a query has no rule to lift a disjunct out of; run it as a goal"
        ++ " instead, as in solve(quote((A ; B)))"
    )
desugarErrorMsg (NonVariableIsInFunctionBody e) =
  withHint
    ( "The left-hand side of 'is' in a function body must be a variable: "
        ++ prettyTermSrc (R.exprToTerm e)
    )
    "use 'X is E' to bind, then pattern-match on X in subsequent positions"
desugarErrorMsg (InlineNotSingleEquation qn n) =
  withHint
    ( "':- inline' function '"
        ++ displayQualifiedName qn
        ++ "' has "
        ++ show n
        ++ " equations"
    )
    ( "an inline substitution has no way to try equations in order;"
        ++ " it must have exactly one"
    )
desugarErrorMsg (InlineGuardedEquation qn) =
  withHint
    ( "':- inline' function '"
        ++ displayQualifiedName qn
        ++ "' has a guarded equation"
    )
    ( "an inlined equation cannot have a guard, including one synthesized from a"
        ++ " non-variable parameter pattern; every parameter must be a plain"
        ++ " variable or '_'"
    )
desugarErrorMsg (InlineStatefulEquation qn) =
  withHint
    ( "':- inline' function '"
        ++ displayQualifiedName qn
        ++ "' has statements before its return value"
    )
    "an inlined equation's body must be a single expression"
desugarErrorMsg (InlineCycle names) =
  withHint
    ( "':- inline' functions call each other in a cycle: "
        ++ intercalate ", " (map T.unpack names)
    )
    "remove ':- inline' from at least one function on the cycle"

instance Display (Diagnostic CompileError) where
  displayMsg = displayDiagnostic SevError compileErrorCode compileErrorMsg

compileErrorMsg :: CompileError -> String
compileErrorMsg (UnknownConstraintType name) =
  withHint
    ("Unknown constraint type '" ++ displayName name ++ "'")
    "declare it with :- chr_constraint name/arity"
compileErrorMsg (UnboundVariable var) =
  withHint
    ("Unbound variable '" ++ T.unpack var ++ "'")
    ( "variables used in a guard or body must also appear in the rule"
        ++ " head or the equation's parameters"
    )
compileErrorMsg (AggregateLocalEscapes var) =
  withHint
    ("Aggregate-local variable '" ++ T.unpack var ++ "' escapes its aggregate")
    ( "a variable only an aggregate's goal binds is not visible to the"
        ++ " rule's guard or body; bind it with '=' in the body instead"
    )
compileErrorMsg (AggregateNestedTake name) =
  withHint
    ("'" ++ T.unpack name ++ "/2' is not allowed inside an aggregate goal")
    ( "a nested selection cannot remove constraints; use argmin/argmax"
        ++ " there, or move the take form to the rule head"
    )
compileErrorMsg AggregateResultNotMaybe =
  withHint
    "No 'maybe:just/1' constructor is visible"
    ( "an aggregator's Final closure must return library(maybe)'s maybe;"
        ++ " import it with :- use_module(library(maybe))"
    )

instance Display (Diagnostic TypeCheckError) where
  displayMsg = displayDiagnostic SevError typeCheckErrorCode typeCheckErrorMsg

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
    ++ intercalate ", " [T.unpack d.typeName ++ "/" ++ show d.arity | d <- decls]
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
typeCheckErrorMsg (TypeRefArityMismatch tyName conName refName usedArity declaredArity) =
  "Type '"
    ++ T.unpack refName
    ++ "' is applied to "
    ++ show usedArity
    ++ " argument(s) but declared with "
    ++ show declaredArity
    ++ " parameter(s), in constructor '"
    ++ T.unpack conName
    ++ "' of type '"
    ++ T.unpack tyName
    ++ "'"
typeCheckErrorMsg (AggregateTypeEscapes ty) =
  withHint
    ( "A type that is chosen per match of an aggregate goal reaches the"
        ++ " rule: '"
        ++ T.unpack ty
        ++ "'"
    )
    ( "each match may be a different instance; fix the instance with a"
        ++ " guard in the goal, or link it to a variable of the rule"
    )
typeCheckErrorMsg (AggregateLinkConflict t1 t2) =
  withHint
    ( "An aggregate goal ties one type to both '"
        ++ T.unpack t1
        ++ "' and '"
        ++ T.unpack t2
        ++ "'"
    )
    "the goal can match when the two differ; make them the same type in the rule"
typeCheckErrorMsg (UndeterminedInstance con ty) =
  withHint
    ( "Constraint '"
        ++ T.unpack con
        ++ "' has a type parameter used at '"
        ++ T.unpack ty
        ++ "', a type whose values can also belong to other types"
    )
    ( "a constraint's type parameters cannot be lists, maybes, functions and"
        ++ " the like; put the structure in the declaration instead, e.g."
        ++ " 'c(list(T))' rather than 'c(T)' used at a list"
    )

instance Display (Diagnostic TypeCheckWarning) where
  displayMsg = displayDiagnostic SevWarning typeCheckWarningCode typeCheckWarningMsg

typeCheckWarningMsg :: TypeCheckWarning -> String
typeCheckWarningMsg (InaccessibleBranch t1 t2) =
  withHint
    ( "This can never fire: a guard requires '"
        ++ T.unpack t1
        ++ "' where the type is '"
        ++ T.unpack t2
        ++ "'"
    )
    "remove the dead rule or equation, or fix the type it disagrees with"
typeCheckWarningMsg (AggregateGoalInaccessible t1 t2) =
  withHint
    ( "This aggregate goal can never match: it requires '"
        ++ T.unpack t1
        ++ "' where the type is '"
        ++ T.unpack t2
        ++ "', so the aggregate always sees zero matches"
    )
    "fix the goal, or drop the aggregate if zero matches is what you want"

-- | Render a name as @name@ or @mod:name@.
displayName :: Types.Name -> String
displayName = T.unpack . Types.flattenName

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
   in displayMsgWithSrcLoc
        MsgBlock
          { code = parseErrorCode,
            severity = SevError,
            message = msg,
            loc = loc,
            label = Nothing,
            node = Nothing,
            context = []
          }

instance Display Warning where
  displayMsg (RenameWarnings ws) = displayErrors (map displayMsg ws)
  displayMsg (ExhaustivenessWarnings ws) = displayErrors (map displayMsg ws)
  displayMsg (TypeCheckWarnings ws) = displayErrors (map displayMsg ws)

instance Display Error where
  displayMsg (ParseError _ err) = displayParseError err
  displayMsg (ParseValidationErrors errs) = displayErrors (map displayMsg errs)
  displayMsg (DeclMacroErrors errs) = displayErrors (map displayMsg errs)
  displayMsg (CollectErrors errs) = displayErrors (map displayMsg errs)
  displayMsg (RenameErrors errs) = displayErrors (map displayMsg errs)
  displayMsg (ResolveErrors errs) = displayErrors (map displayMsg errs)
  displayMsg (DesugarErrors errs) = displayErrors (map displayMsg errs)
  displayMsg (CompileErrors errs) = displayErrors (map displayMsg errs)
  displayMsg (TypeErrors errs) = displayErrors (map displayMsg errs)
  displayMsg (OperatorConflict (AnnP name loc origin)) =
    displayMsgWithSrcLoc
      MsgBlock
        { code = operatorConflictCode,
          severity = SevError,
          message =
            withHint
              ( "Operator conflict: '"
                  ++ T.unpack name
                  ++ "' is declared with a different fixity or associativity"
                  ++ " than an existing operator"
              )
              ( "re-export the existing declaration instead of redeclaring it,"
                  ++ " or rename this one"
              ),
          loc = loc,
          label = Nothing,
          node = Just (prettyPExprSrc origin),
          context = []
        }
  displayMsg (LambdasInLiveQuery loc origin) =
    displayMsgWithSrcLoc
      MsgBlock
        { code = lambdasInLiveQueryCode,
          severity = SevError,
          message =
            withHint
              ( "Anonymous lambdas (fun(...) -> ... end) are not supported"
                  ++ " in live REPL sessions"
              )
              ( "lift the lambda into a named :- function declaration in a file"
                  ++ " and reload the session"
              ),
          loc = loc,
          label = Just "live session",
          node = Just (prettyPExprSrc origin),
          context = []
        }
  displayMsg (LambdasInSchemeDriver lam) =
    displayMsgWithSrcLoc
      MsgBlock
        { code = lambdasInSchemeDriverCode,
          severity = SevError,
          message =
            withHint
              ( "Anonymous lambdas (fun(...) -> ... end) are not supported"
                  ++ " in goal arguments to `ychr gen-driver`"
              )
              ( "the driver only imports an already-generated library, which"
                  ++ " has no procedure for this lambda: lift it into a named"
                  ++ " :- function declaration in the program and pass"
                  ++ " `fun name/arity` instead"
              ),
          loc = P.dummyLoc,
          label = Just "<query>",
          node = Just (prettyTermSrc lam),
          context = []
        }
  displayMsg (GoalNotAConstraint c reason) =
    displayMsgWithSrcLoc
      MsgBlock
        { code = goalNotAConstraintCode,
          severity = SevError,
          message =
            withHint
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
                      ++ displayQualifiedName qn
                      ++ "/"
                      ++ show (length c.args)
                      ++ "' is not exported by its module"
                  NotAConstraintItem qn ->
                    "Goal '"
                      ++ displayQualifiedName qn
                      ++ "/"
                      ++ show (length c.args)
                      ++ "' names a function, not a constraint"
                  MacroNotSingleGoal ->
                    "Goal '"
                      ++ nameArity
                      ++ "' is a macro that does not expand to exactly one goal"
              )
              ( case reason of
                  MacroNotSingleGoal ->
                    "macro expands to several goals or none; run it as a query in the"
                      ++ " REPL or the multi-goal query API instead of `ychr run -g`"
                  _ ->
                    "`ychr run -g GOAL` accepts only a single declared constraint."
                      ++ " For expression goals like `1 + 1` or `X is E`,"
                      ++ " conjunctions like `a, b`, or function calls,"
                      ++ " use `ychr repl` instead — or wrap them in a helper constraint."
              ),
          loc = P.dummyLoc,
          label = Just "<query>",
          node = Nothing,
          context = []
        }
    where
      nameArity = T.unpack (Types.flattenName c.name) ++ "/" ++ show (length c.args)
  displayMsg (RuntimeError msg stack) = displayErrors (renderFrames msg stack)
    where
      -- An empty stack means the error fired before any 'PushFrame'; we
      -- still produce a runtime-error block, just anchored at 'dummyLoc'.
      renderFrames m [] =
        [ displayMsgWithSrcLoc
            MsgBlock
              { code = runtimeErrorCode,
                severity = SevRuntimeError,
                message = m,
                loc = P.dummyLoc,
                label = Nothing,
                node = Nothing,
                context = []
              }
        ]
      renderFrames m (top : rest) = renderTop top m : map renderRest rest
      renderTop frame m =
        displayMsgWithSrcLoc
          MsgBlock
            { code = runtimeErrorCode,
              severity = SevRuntimeError,
              message = m,
              loc = frame.sourceLoc,
              label = Just (T.unpack frame.label),
              node = Just (T.unpack frame.sourceCode),
              context = []
            }
      renderRest frame =
        displayMsgWithSrcLoc
          MsgBlock
            { code = runtimeErrorCode,
              severity = SevStackTrace,
              message = "",
              loc = frame.sourceLoc,
              label = Just (T.unpack frame.label),
              node = Just (T.unpack frame.sourceCode),
              context = []
            }
