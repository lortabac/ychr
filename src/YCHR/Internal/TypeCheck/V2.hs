{-# LANGUAGE OverloadedStrings #-}

-- | Driver for the all-CHR type checker (@typechecker2\/@).
--
-- Where "YCHR.Internal.TypeCheck" walks the desugared AST in Haskell
-- and feeds a CHR solver constraint by constraint, this driver hands
-- the whole program over as one ground term and decodes the two
-- diagnostic lists that come back. Everything in between —
-- declaration collection, slot skeletons, the walkers, overload
-- resolution, warning suppression — happens in CHR.
--
-- The two checkers coexist while the port is in progress: nothing
-- user-facing calls this one yet, and @test\/YCHR\/TypeCheckDiffTest.hs@
-- runs both over the same corpus and compares their diagnostics. The
-- CHR side is currently a stub that reports nothing (milestone M2);
-- the decoding below is complete, so filling the stub in is all that
-- later milestones change here.
module YCHR.Internal.TypeCheck.V2
  ( typeCheckProgramV2,
    typeCheckGoalsV2,
  )
where

import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IntMap
import Data.Text (Text)
import Data.Text qualified as T
import YCHR.Internal.Desugared qualified as D
import YCHR.Internal.Diagnostic (Diagnostic (..))
import YCHR.Internal.Loc (SourceLoc (..))
import YCHR.Internal.Meta (decodeName)
import YCHR.Internal.PExpr (PExpr (Atom))
import YCHR.Internal.Parsed (AnnP (..))
import YCHR.Internal.Runtime.Monad (Chr)
import YCHR.Internal.Runtime.Session (tellConstraint, withCHR)
import YCHR.Internal.Runtime.SubSession (defaultHostCallRegistry)
import YCHR.Internal.Runtime.Types (Value (..))
import YCHR.Internal.Runtime.Var (deref, newVar)
import YCHR.Internal.TypeCheck.Compiled (typeChecker2Program)
import YCHR.Internal.TypeCheck.Encode
  ( Encoded (..),
    astAtom,
    encodeBodyGoals,
    encodeProgram,
    encodeSourceLoc,
    encodedToValue,
  )
import YCHR.Internal.TypeCheck.Error
  ( TypeCheckError (..),
    TypeCheckResult (..),
    TypeCheckWarning (..),
  )
import YCHR.Internal.TypeCheck.Render
  ( TypeAtoms (..),
    deepDerefType,
    displayQualifiedAtom,
    showType,
    showValue,
    showValueShape,
  )
import YCHR.Internal.Types (Name (..), Term (..), flattenName)

-- | This checker's solver declares its type representation in
-- @'$tc2_solver'@, so that is the qualifier the renderer strips.
tc2TypeAtoms :: TypeAtoms
tc2TypeAtoms = TypeAtoms "$tc2_solver"

-- | Runtime functor name of a constructor declared in @'$tc2_diag'@.
diagAtom :: Text -> Text
diagAtom n = "$tc2_diag__" <> n

-- ---------------------------------------------------------------------------
-- Entry points
-- ---------------------------------------------------------------------------

-- | Type-check a desugared program. The V2 counterpart of
-- 'YCHR.Internal.TypeCheck.typeCheckProgram', with the same contract:
-- an empty error list means the program is well-typed (or carries no
-- type annotations, which is the same thing to a gradual checker).
typeCheckProgramV2 :: D.Program -> IO TypeCheckResult
typeCheckProgramV2 prog =
  runChecker enc.origins $ \errorsVar warningsVar ->
    tellConstraint
      (Qualified "$tc2_main" "check_program")
      [encodedToValue enc.term, errorsVar, warningsVar]
  where
    enc = encodeProgram prog

-- | Type-check a query's body goals against an already-compiled
-- program's declarations. The V2 counterpart of
-- 'YCHR.Internal.TypeCheck.typeCheckGoals'.
--
-- Unlike its counterpart this takes the encoded program as an explicit
-- argument of the CHR entry point rather than re-telling the
-- program's signatures into the session: there is only one way into
-- the checker, and it is the program term.
typeCheckGoalsV2 ::
  D.Program ->
  SourceLoc ->
  Maybe Text ->
  [D.BodyGoal] ->
  IO TypeCheckResult
typeCheckGoalsV2 prog loc lbl goals =
  runChecker enc.origins $ \errorsVar warningsVar ->
    tellConstraint
      (Qualified "$tc2_main" "check_goals")
      [ encodedToValue enc.term,
        encodedToValue (encodeBodyGoals goals),
        encodedToValue (encodeSourceLoc loc),
        labelValue lbl,
        errorsVar,
        warningsVar
      ]
  where
    enc = encodeProgram prog

-- | A caller-supplied diagnostic label as the CHR program sees it.
labelValue :: Maybe Text -> Value
labelValue Nothing = VAtom (diagAtom "label_none")
labelValue (Just t) = VTerm (diagAtom "label_text") [VText t]

-- | Run one checking session: allocate the two out-variables, tell the
-- entry constraint, and decode what it bound them to.
runChecker :: IntMap PExpr -> (Value -> Value -> Chr ()) -> IO TypeCheckResult
runChecker origins enter =
  withCHR typeChecker2Program defaultHostCallRegistry $ do
    errorsVar <- newVar
    warningsVar <- newVar
    enter errorsVar warningsVar
    errs <- decodeDiagnostics origins "error" decodeError errorsVar
    warns <- decodeDiagnostics origins "warning" decodeWarning warningsVar
    pure TypeCheckResult {errors = errs, warnings = warns}

-- ---------------------------------------------------------------------------
-- Decoding
-- ---------------------------------------------------------------------------

-- | Everything a diagnostic's @ctx@ says about where it came from. The
-- unit id the term also carries is not decoded: warning suppression
-- already ran CHR-side, so the lists that reach here are final.
data CtxInfo = CtxInfo
  { label :: Maybe Text,
    loc :: SourceLoc,
    origin :: PExpr
  }

-- | Decode one accumulator. Errors and warnings have the same
-- @f(Ctx, Code, Detail)@ shape; @constructor@ names the expected
-- @'$tc2_diag'@ one and @decodeBody@ turns the @(Code, Detail)@ pair
-- into the diagnostic payload.
decodeDiagnostics ::
  IntMap PExpr ->
  Text ->
  (Value -> Value -> Chr a) ->
  Value ->
  Chr [Diagnostic a]
decodeDiagnostics origins constructor decodeBody var = do
  items <- derefList var
  case items of
    Nothing ->
      malformed ("the " <> constructor <> " accumulator is not a list") var
    Just xs -> traverse one xs
  where
    functor = diagAtom constructor
    one item = do
      item' <- deref item
      case item' of
        VTerm f [ctxVal, codeVal, detailVal] | f == functor -> do
          info <- decodeCtx origins ctxVal
          code <- deref codeVal
          detail <- deref detailVal
          payload <- decodeBody code detail
          pure (Diagnostic info.label (AnnP payload info.loc info.origin))
        _ -> malformed (constructor <> " entry") item'

decodeCtx :: IntMap PExpr -> Value -> Chr CtxInfo
decodeCtx origins val = do
  val' <- deref val
  case val' of
    VTerm f [_unit, annVal, labelVal, locVal] | f == diagAtom "ctx" -> do
      o <- decodeOrigin origins annVal
      lbl <- decodeLabel labelVal
      l <- decodeLoc locVal
      pure CtxInfo {label = lbl, loc = l, origin = o}
    _ -> malformed "ctx" val'

-- | Recover the p-expr an annotation id names. The id has to be one
-- the encoder handed out, or the documented @-1@ for a diagnostic with
-- no enclosing annotated node (a top-level goal's). Anything else means
-- a rule invented an id, which no rule may do.
decodeOrigin :: IntMap PExpr -> Value -> Chr PExpr
decodeOrigin origins val = do
  val' <- deref val
  case val' of
    VInt n
      | n < 0 -> pure (Atom "")
      | otherwise -> case IntMap.lookup (fromInteger n) origins of
          Just pexpr -> pure pexpr
          Nothing -> malformed "annotation id (not one this encoding handed out)" val'
    _ -> malformed "annotation id" val'

-- | Render a structured label. The wording is the old checker's, so
-- that the two produce identical diagnostic headers — including the
-- name spelling, which is why a function's mangled name goes back
-- through the real inverse rather than through 'displayQualifiedAtom'
-- (that one leaves the @%%u@ escapes of a non-ASCII name in place).
decodeLabel :: Value -> Chr (Maybe Text)
decodeLabel val = do
  val' <- deref val
  case val' of
    VTerm f [x] | f == diagAtom "label_rule" -> do
      name <- deref x
      case name of
        VText t -> pure (Just ("rule " <> t))
        _ -> malformed "label_rule payload" name
    VTerm f [x] | f == diagAtom "label_function" -> do
      name <- deref x
      case name of
        VAtom a -> pure (Just ("function " <> unmangleName a))
        _ -> malformed "label_function payload" name
    VTerm f [x] | f == diagAtom "label_text" -> do
      text <- deref x
      case text of
        VText t -> pure (Just t)
        _ -> malformed "label_text payload" text
    VAtom a | a == diagAtom "label_none" -> pure Nothing
    _ -> malformed "diag_label" val'

-- | A runtime-mangled name back in source spelling, escapes and all.
-- 'decodeName' is the inverse of the mangling; it builds a 'Term'
-- because that is what its other caller wants, and a 0-arity one is
-- exactly a name.
unmangleName :: Text -> Text
unmangleName a = case decodeName a [] of
  CompoundTerm n [] -> flattenName n
  _ -> displayQualifiedAtom a

decodeLoc :: Value -> Chr SourceLoc
decodeLoc val = do
  val' <- deref val
  case val' of
    VTerm f [fileVal, lineVal, colVal] | f == astAtom "loc" -> do
      file <- deref fileVal
      line <- deref lineVal
      col <- deref colVal
      case (textOf file, intOf line, intOf col) of
        (Just fl, Just ln, Just cl) -> pure (SourceLoc (T.unpack fl) ln cl)
        _ -> malformed "loc fields" val'
    _ -> malformed "loc" val'

decodeError :: Value -> Value -> Chr TypeCheckError
decodeError code detail = case code of
  VAtom c | c == diagAtom "inconsistent" -> do
    (t1text, t2text) <- decodeTypePair detail
    pure (InconsistentTypes t1text t2text)
  VAtom c
    | c == diagAtom "no_matching_overload" ->
        NoMatchingOverload <$> showValue detail
  VAtom c
    | c == diagAtom "bound_unsatisfied" ->
        BoundUnsatisfied <$> showValue detail
  _ -> malformed "error code" code

decodeWarning :: Value -> Value -> Chr TypeCheckWarning
decodeWarning code detail = case code of
  VAtom c | c == diagAtom "inaccessible" -> do
    (t1text, t2text) <- decodeTypePair detail
    pure (InaccessibleBranch t1text t2text)
  _ -> malformed "warning code" code

-- | Render a @tpair(T1, T2)@ detail as the two types' source syntax.
decodeTypePair :: Value -> Chr (Text, Text)
decodeTypePair detail = case detail of
  VTerm pf [t1, t2] | pf == diagAtom "tpair" -> do
    t1' <- deepDerefType t1
    t2' <- deepDerefType t2
    pure (showType tc2TypeAtoms t1', showType tc2TypeAtoms t2')
  _ -> pure ("?", "?")

-- ---------------------------------------------------------------------------
-- Value helpers
-- ---------------------------------------------------------------------------

-- | Decompose a list value, dereferencing the spine as it goes: the
-- CHR side builds these lists by unification, so a cell can be a bound
-- variable rather than a cons term.
derefList :: Value -> Chr (Maybe [Value])
derefList val = do
  val' <- deref val
  case val' of
    VAtom "prelude__[]" -> pure (Just [])
    VTerm "prelude__." [x, rest] -> fmap (x :) <$> derefList rest
    _ -> pure Nothing

textOf :: Value -> Maybe Text
textOf (VText t) = Just t
textOf _ = Nothing

intOf :: Value -> Maybe Int
intOf (VInt n) = Just (fromInteger n)
intOf _ = Nothing

-- | A shape the CHR checker is not allowed to produce. Every one of
-- these is a bug in @typechecker2\/@ or in this decoder, never
-- something a user program can trigger.
malformed :: Text -> Value -> Chr a
malformed what val =
  error
    ( "TypeCheck.V2: malformed "
        <> T.unpack what
        <> ": "
        <> showValueShape val
    )
