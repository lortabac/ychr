{-# LANGUAGE OverloadedStrings #-}

-- |
-- Module      : YCHR.Compile.Names
-- Description : Naming conventions for compiler-generated VM identifiers.
--
-- Centralizes every name the CHR-to-VM compiler bakes into the generated
-- 'YCHR.VM.Program'. Two flavours of name live here:
--
-- * /Procedure-name builders/ ('tellProcName', 'activateProcName',
--   'occProcName', 'funcProcName', 'callFunProcName'): pure functions
--   from a source name + arity (or other identifying data) to a 'Name'.
--   Backends and tests that need to predict the name of a generated
--   procedure should import this module rather than re-deriving the
--   convention.
--
-- * /Local-variable names and dispatch constants/ ('activeName',
--   'pendingName', 'suspParamName', 'dropResultName',
--   'reactivateDispatchName', 'chrErrorName', plus the partner-loop
--   helpers 'partSuspName' \/ 'partIdName' \/ 'partArgName' \/
--   'partLabel'): the vocabulary used by the bodies of generated
--   procedures.
module YCHR.Compile.Names
  ( -- * Procedure name builders
    procNameFor,
    tellProcName,
    activateProcName,
    occProcName,
    funcProcName,
    callFunProcName,

    -- * Source-name encoding
    encodeText,
    encodeIdentifier,
    isIdInitialSafe,
    vmName,

    -- * Active-constraint argument variables
    argName,
    argNames,

    -- * Partner-loop variables
    partSuspName,
    partIdName,
    partArgName,
    partLabel,

    -- * Generated-code local-variable names
    activeName,
    pendingName,
    suspParamName,
    dropResultName,

    -- * Runtime entry-point names
    reactivateDispatchName,
    chrErrorName,
  )
where

import Data.Char (isAlpha, isAscii, isDigit, ord)
import Data.Text (Text)
import Data.Text qualified as T
import Numeric (showHex)
import YCHR.Compile.Types (OccurrenceNumber (..), PartnerIndex (..))
import YCHR.Types qualified as Types
import YCHR.VM (Label (..), Name (..))

-- ---------------------------------------------------------------------------
-- Source-name encoding
-- ---------------------------------------------------------------------------

-- | Encode a text component for use in generated /symbolic/ VM names —
-- compound-term functors and lambda-closure identifiers. ASCII
-- characters pass through unchanged; non-ASCII characters are
-- rewritten to @%%u\<hex\>@ where @\<hex\>@ is the Unicode codepoint
-- padded to exactly 6 lowercase digits.
--
-- The escape marker @%%u@ is reserved by the lexer (see
-- 'YCHR.PExpr.quotedAtomP') so it can never appear in a source atom.
-- Together with the lexer's existing rejection of @__@, this makes
-- the encoding @encodeText m <> "__" <> encodeText n@ used by
-- 'vmName' /injective/: encoded text contains no @__@ at all (escapes
-- use @%%u@ instead, and source contributes none), so the only @__@
-- in the mangled form is the module/base separator. Every @%%u@ is
-- followed by exactly 6 hex digits — fixed-width with no closing
-- delimiter, so escape boundaries cannot overlap with the separator
-- or with each other. Six digits covers the whole Unicode range
-- (@U+10FFFF@). The decoder ('YCHR.Meta.decodeMangled') therefore
-- splits on the first @__@ and then expands @%%u\<6 hex digits\>@ in
-- each half.
--
-- The resulting string is treated as a symbol by the runtime (the
-- Scheme backend falls back to @(string->symbol "...")@ via
-- 'YCHR.Backend.Scheme.compileSymbol' when the encoded form isn't a
-- valid Scheme identifier), so the encoding need not produce a
-- strictly identifier-safe result.
--
-- For generated /procedure/ names — @tell_*@, @activate_*@, @func_*@
-- — use 'encodeIdentifier' instead. Those names are emitted as bare
-- identifiers in target code and must be valid in both Scheme and
-- JavaScript, neither of which accept @%@; the older
-- @__u\<hex\>__@ escape is retained there since procedure names are
-- never decoded.
encodeText :: Text -> Text
encodeText = T.concatMap encodeChar
  where
    encodeChar c
      | isAscii c = T.singleton c
      | otherwise = "%%u" <> T.pack (padHex6 (showHex (ord c) ""))
    padHex6 h = replicate (6 - length h) '0' ++ h

-- | Encode a text component into an identifier that is valid in every
-- backend's target language. ASCII letters, digits, @_@, and @$@ pass
-- through; every other character is rewritten to @__u{hex codepoint}__@.
--
-- The allowed character set is the intersection of what JavaScript
-- and R6RS Scheme accept in identifiers: function names like
-- @func_prelude__+2@ would be a valid Scheme identifier but not a
-- valid JavaScript one, so @+@ is escaped.
--
-- Used by 'procNameFor' (so generated procedures like @tell_*@ are
-- always valid identifiers in the target language) and by the alias
-- builder in 'YCHR.Backend.Scheme'.
--
-- The encoding is one-way: total, deterministic, and unambiguous.
-- Injectivity follows from the parser: 'YCHR.PExpr' rejects atoms
-- containing @__@, so no source-language name can look like an
-- escape sequence and collide with one.
encodeIdentifier :: Text -> Text
encodeIdentifier = T.concatMap encodeChar
  where
    encodeChar c
      | isAscii c && (isAlpha c || isDigit c || c == '_' || c == '$') =
          T.singleton c
      | otherwise = "__u" <> T.pack (showHex (ord c) "") <> "__"

-- | Predicate that classifies a character as safe as the /first/
-- character of an identifier. Letters, @_@, and @$@ qualify; digits
-- do not. Used by alias builders, where the encoded component lands
-- at the start of an identifier and a leading digit would be
-- syntactically illegal.
isIdInitialSafe :: Char -> Bool
isIdInitialSafe c = isAscii c && (isAlpha c || c == '_' || c == '$')

-- | Build a VM 'Name' for a source-language identifier of the given
-- arity, prefixed by a procedure-kind tag (@tell@, @activate@, @func@,
-- …). Qualified names embed both the module and the local part,
-- separated by @__@.
--
-- The module and constraint-name components are passed through
-- 'encodeIdentifier' (not 'encodeText') so the resulting procedure
-- name is always a valid identifier in every backend's target
-- language — including JavaScript, where operator characters like
-- @+@, @-@, @*@, @/@ are illegal in function names.
procNameFor :: Text -> Types.Name -> Int -> Name
procNameFor prefix (Types.Qualified m n) arity =
  Name
    ( prefix
        <> "_"
        <> encodeIdentifier m
        <> "__"
        <> encodeIdentifier n
        <> T.pack (show arity)
    )
procNameFor prefix (Types.Unqualified n) arity =
  Name (prefix <> "_" <> encodeIdentifier n <> T.pack (show arity))

-- | Encode a source-language 'Types.Name' as a VM 'Name' /without/ a
-- procedure-kind prefix. Used for compound-term functors and lambda
-- closures.
vmName :: Types.Name -> Name
vmName (Types.Unqualified n) = Name (encodeText n)
vmName (Types.Qualified m n) = Name (encodeText m <> "__" <> encodeText n)

-- ---------------------------------------------------------------------------
-- Procedure-name builders
-- ---------------------------------------------------------------------------

-- | Name of the @tell_c@ procedure for a constraint of the given source
-- name and arity.
tellProcName :: Types.Name -> Int -> Name
tellProcName = procNameFor "tell"

-- | Name of the @activate_c@ procedure for a constraint of the given
-- source name and arity.
activateProcName :: Types.Name -> Int -> Name
activateProcName = procNameFor "activate"

-- | Name of the @occurrence_c_j@ procedure for the @j@-th occurrence of
-- a constraint of the given source name and arity.
occProcName :: Types.Name -> Int -> OccurrenceNumber -> Name
occProcName name arity num =
  let Name base = procNameFor "occurrence" name arity
   in Name (base <> "_" <> T.pack (show num.unOccurrenceNumber))

-- | Name of the procedure that implements a user-defined function of
-- the given source name and arity.
funcProcName :: Types.Name -> Int -> Name
funcProcName = procNameFor "func"

-- | Name of the @call_N@ dispatch procedure for a call with @N@
-- arguments (i.e. an @N+1@-ary @call(F, arg_1, …, arg_N)@). Each
-- supported call arity gets its own dispatch procedure.
callFunProcName :: Int -> Name
callFunProcName n = Name ("call_" <> T.pack (show n))

-- ---------------------------------------------------------------------------
-- Active-constraint argument variables
-- ---------------------------------------------------------------------------

-- | List of local-variable names for the arguments of the active
-- constraint inside an @activate_c@ \/ @occurrence_c_j@ procedure.
argNames :: Int -> [Name]
argNames arity = [argName i | i <- [0 .. arity - 1]]

-- | Local-variable name for the @i@-th argument of the active
-- constraint: @X_i@.
argName :: Int -> Name
argName i = Name ("X_" <> T.pack (show i))

-- ---------------------------------------------------------------------------
-- Partner-loop variables
-- ---------------------------------------------------------------------------

-- | VM variable name for the suspension currently bound by partner
-- @k@'s 'YCHR.VM.Foreach' loop: @susp_k@.
partSuspName :: PartnerIndex -> Name
partSuspName k = Name ("susp_" <> T.pack (show k.unPartnerIndex))

-- | VM variable name for the constraint identifier of partner @k@,
-- extracted from its suspension before the body runs: @pId_k@.
partIdName :: PartnerIndex -> Name
partIdName k = Name ("pId_" <> T.pack (show k.unPartnerIndex))

-- | VM variable name for the @j@-th argument of partner @k@: @pArg_k_j@.
partArgName :: PartnerIndex -> Int -> Name
partArgName k j = Name ("pArg_" <> T.pack (show k.unPartnerIndex) <> "_" <> T.pack (show j))

-- | VM 'Label' attached to partner @k@'s 'YCHR.VM.Foreach' loop. Used
-- by 'YCHR.VM.Continue' for backjumping. Numbered from 1 so the
-- outermost loop is @L1@.
partLabel :: PartnerIndex -> Label
partLabel k = Label ("L" <> T.pack (show (k.unPartnerIndex + 1)))

-- ---------------------------------------------------------------------------
-- Generated-code local-variable names
-- ---------------------------------------------------------------------------

-- | The active constraint of an occurrence procedure (paper
-- terminology). At runtime "constraint identifier" and "constraint
-- suspension" are the same value, so this single name covers both
-- roles. See the \"Notes\" block in 'YCHR.Compile'.
activeName :: Name
activeName = "active"

-- | Suspension binder for 'YCHR.VM.DrainReactivationQueue': each
-- pending reactivation is bound to this variable in turn.
pendingName :: Name
pendingName = "pending"

-- | Suspension binder for the @reactivate_dispatch@ procedure. Distinct
-- from 'pendingName' because dispatch handles a single suspension at a
-- time without iterating.
suspParamName :: Name
suspParamName = "susp"

-- | Boolean result returned by an @occurrence_c_j@ call: @True@ when the
-- occurrence dropped the active constraint, telling the caller to
-- short-circuit (Early Drop, paper §5.3).
dropResultName :: Name
dropResultName = "dropped"

-- ---------------------------------------------------------------------------
-- Runtime entry-point names
-- ---------------------------------------------------------------------------

-- | Procedure name of @reactivate_dispatch@ — the only
-- compiler-generated procedure called by name from inside another
-- procedure's body, since the others are looked up via 'tellProcName'
-- \/ 'activateProcName' \/ 'occProcName'.
reactivateDispatchName :: Name
reactivateDispatchName = "reactivate_dispatch"

-- | Host-language error reporter, called from generated dispatch
-- procedures when no equation matches. Defined by the runtime.
chrErrorName :: Name
chrErrorName = "__chr_error"
