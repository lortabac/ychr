-- | The generated-code tree and its renderer.
--
-- The build step that precomputes the bundled resources
-- (@make resources@, see @dev-docs\/MICROHS_PERFORMANCE.md@, option B)
-- emits Haskell modules holding literal data: the decoded standard
-- library and the decoded type-checker. 'Code' is the expression tree
-- those modules are built from, and 'renderCode' prints it.
--
-- This is deliberately not Template Haskell's @Exp@. TH's pretty-printer
-- spells a 'Double' as @3.5##@ and a lifted 'Data.Text' as
-- @Data.Text.unpackCStringLen# \"\<binary data>\"@, neither of which
-- MicroHs can parse; the renderer here writes the plain surface syntax
-- MicroHs does accept, and exposes only the forms the emitter needs.
--
-- Constructors are emitted /positionally/ (never as record syntax), so
-- the package's @NoFieldSelectors@\/@DuplicateRecordFields@ defaults
-- cannot change the meaning of the output.
module YCHR.Embedded.Generate.Code
  ( -- * Expressions
    Code (..),
    renderCode,
    codeSize,

    -- * Module aliases
    aliasForModule,
    aliasTable,
  )
where

import Data.List (intercalate)

-- | A closed Haskell expression, restricted to the forms the emitter
-- produces.
data Code
  = -- | A name, written as it should appear in the generated source:
    -- a single identifier (@True@, @Nothing@), or a qualified name
    -- (@VM.Procedure@, @Map.fromList@).
    CName String
  | -- | Application: the head and its arguments.
    CApp Code [Code]
  | -- | A list literal.
    CList [Code]
  | -- | A tuple literal.
    CTuple [Code]
  | -- | An 'Integer'-valued literal.
    CInt Integer
  | -- | A 'Double'-valued literal. Only finite values are representable
    -- in source; 'renderCode' rejects the rest.
    CDouble Double
  | -- | A string literal. Rendered modules enable @OverloadedStrings@,
    -- so this is also how 'Data.Text.Text' and @String@ fields are
    -- emitted.
    CString String
  | -- | A character literal.
    CChar Char
  | -- | An explicit parenthesis. The emitter has no case that needs one
    -- today — it never writes an operator — but the renderer supports it
    -- so that adding one stays a local change.
    CParens Code
  deriving (Show, Eq)

-- | Render 'Code' as Haskell source. The output is a single line: long
-- bindings are split by the hoisting pass, not by a page layout, so
-- there is no line-wrapping here to break the emitted @where@-free
-- layout.
renderCode :: Code -> String
renderCode = go
  where
    go (CName s) = s
    go (CApp f args) = go f ++ concatMap (\a -> " " ++ argument a) args
    go (CList xs) = "[" ++ intercalate ", " (map go xs) ++ "]"
    go (CTuple xs) = "(" ++ intercalate ", " (map go xs) ++ ")"
    go (CInt n) = show n
    go (CDouble d)
      | isNaN d || isInfinite d =
          error ("ychr-codegen: cannot render a non-finite Double: " ++ show d)
      | otherwise = show d
    go (CString s) = show s
    go (CChar c) = show c
    go (CParens c) = "(" ++ go c ++ ")"

    -- An argument is written bare where the grammar allows it and
    -- parenthesised everywhere else, which means anything that is not
    -- already atomic: a nested application, or a negative literal.
    argument c = case c of
      CName _ -> go c
      CList _ -> go c
      CTuple _ -> go c
      CString _ -> go c
      CChar _ -> go c
      CParens _ -> go c
      CInt n | n >= 0 -> go c
      CDouble d | d >= 0 && not (isNegativeZero d) -> go c
      _ -> "(" ++ go c ++ ")"

-- | The rendered length of a tree, which is the size the hoisting pass
-- budgets against.
codeSize :: Code -> Int
codeSize = length . renderCode

-- ---------------------------------------------------------------------------
-- Module aliases
-- ---------------------------------------------------------------------------

-- | The import alias each defining module is rendered under, keyed by
-- the module's full name. A type's defining module comes from its
-- 'GHC.Generics' metadata, so a type re-exported by
-- "YCHR.Internal.Parsed" but defined in "YCHR.Internal.Types" is
-- aliased as @Types@, not @Parsed@.
--
-- The alias keeps the generated source short — the compiled
-- type-checker is millions of characters of constructor applications —
-- and keeps two same-named types from different modules apart:
-- @VM.Name@ is "YCHR.Internal.VM.Types.Name", @Types.Name@ is
-- "YCHR.Internal.Types.Name".
--
-- This table must cover every module a type in the emitted closures is
-- defined in; an unknown module is a hard error in the emitter, not a
-- silently wrong qualification.
aliasTable :: [(String, String)]
aliasTable =
  [ ("YCHR.Internal.Parsed", "Parsed"),
    ("YCHR.Internal.PExpr", "PExpr"),
    ("YCHR.Internal.Types", "Types"),
    ("YCHR.Internal.Loc", "Loc"),
    ("YCHR.Internal.VM.Types", "VM"),
    ("YCHR.Internal.Compile.Pipeline", "Pipeline"),
    ("YCHR.Internal.Runtime.Session", "Session"),
    ("Data.Map.Strict", "Map"),
    ("Data.IntMap.Strict", "IntMap"),
    ("Data.Set", "Set"),
    ("Data.IntSet", "IntSet"),
    ("Data.List.NonEmpty", "NE")
  ]

-- | 'aliasTable' as a lookup.
aliasForModule :: String -> Maybe String
aliasForModule m = lookup m aliasTable
