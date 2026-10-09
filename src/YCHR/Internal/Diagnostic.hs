{-# LANGUAGE OverloadedStrings #-}

-- | Diagnostic wrapper for annotated errors and warnings.
--
-- A 'Diagnostic' pairs an optional location label (e.g. @"rule transitivity"@
-- or @"function factorial\/1"@) with the 'AnnP'-wrapped error node. The label
-- is displayed between the source-location header and the message body in
-- diagnostic output.
module YCHR.Internal.Diagnostic
  ( Diagnostic (..),
    noDiag,
  )
where

import Data.Text (Text)
import YCHR.Internal.Parsed (AnnP (..))

-- | An annotated error or warning with an optional location label and
-- an optional macro-expansion chain.
data Diagnostic a = Diagnostic
  { -- | Human-readable label for the enclosing context, e.g.
    -- @"rule transitivity"@ or @"function factorial\/1"@.
    diagLabel :: Maybe Text,
    -- | The underlying annotated node.
    diagAnnotation :: AnnP a,
    -- | The chain of @:- macro@ expansions that produced the code this
    -- diagnostic points at, innermost first — each entry already
    -- rendered as one display line (@"in the expansion of m:name\/n,
    -- used at file:l:c"@). Empty for a diagnostic that did not arise
    -- inside an expansion. Built and rendered by
    -- "YCHR.Internal.Rename", which is the only phase whose
    -- diagnostics can carry one; see docs/reference/macros.md
    -- §Diagnostics.
    diagContext :: [Text]
  }
  deriving (Show, Eq)

-- | Wrap an 'AnnP' value into a 'Diagnostic' with no label and no
-- macro-expansion context.
noDiag :: AnnP a -> Diagnostic a
noDiag ann = Diagnostic Nothing ann []
