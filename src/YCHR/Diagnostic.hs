{-# LANGUAGE OverloadedStrings #-}

-- | Diagnostic wrapper for annotated errors and warnings.
--
-- A 'Diagnostic' pairs an optional location label (e.g. @"rule transitivity"@
-- or @"function factorial\/1"@) with the 'AnnP'-wrapped error node. The label
-- is displayed between the source-location header and the message body in
-- diagnostic output.
module YCHR.Diagnostic
  ( Diagnostic (..),
    noDiag,
  )
where

import Data.Text (Text)
import YCHR.Parsed (AnnP (..))

-- | An annotated error or warning with an optional location label.
data Diagnostic a = Diagnostic
  { -- | Human-readable label for the enclosing context, e.g.
    -- @"rule transitivity"@ or @"function factorial\/1"@.
    diagLabel :: Maybe Text,
    -- | The underlying annotated node.
    diagAnnotation :: AnnP a
  }
  deriving (Show, Eq)

-- | Wrap an 'AnnP' value into a 'Diagnostic' with no label.
noDiag :: AnnP a -> Diagnostic a
noDiag = Diagnostic Nothing
