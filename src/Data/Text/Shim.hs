-- |
-- Module      : Data.Text.Shim
-- Description : Provisional replacements for 'Data.Text' functions MicroHs lacks.
--
-- MicroHs's @Data.Text@ does not export 'breakOn', 'breakOnEnd',
-- 'concatMap' or 'last', so this module offers the whole @Data.Text@
-- surface plus those four, implemented over @Data.List@. It lets an
-- importer swap @Data.Text@ for this module and build under both GHC and
-- @mhs@.
--
-- The definitions replace the native @Data.Text@ ones under GHC as well:
-- one implementation then serves both compilers, and the GHC test suite
-- (@test/YCHR/TextShimTest.hs@) exercises the code @mhs@ will run,
-- pinning it to @Data.Text@ itself.
--
-- See @dev-docs/MICROHS_GAPS.md@, gap 4. Delete this module (and revert its
-- importers) once MicroHs exports the four functions.
module Data.Text.Shim
  ( module Data.Text,
    breakOn,
    breakOnEnd,
    concatMap,
    last,
  )
where

import Data.List qualified as L
import Data.Text hiding (breakOn, breakOnEnd, concatMap, last)
import Data.Text qualified as T
-- 'concatMap' and 'last' are exported by Prelude, so the export list
-- entries above would be ambiguous without this hiding.
import Prelude hiding (concatMap, last)

-- | Split @src@ before the first occurrence of @pat@, which starts the
-- second component; @(src, "")@ when @pat@ does not occur. Partial like
-- the @Data.Text@ original: an empty @pat@ is an error.
breakOn :: Text -> Text -> (Text, Text)
breakOn pat src
  | T.null pat = error "Data.Text.Shim.breakOn: empty pattern"
  | otherwise = go [] hay
  where
    p = T.unpack pat
    hay = T.unpack src
    go _ [] = (src, T.empty)
    go acc s@(c : cs)
      | p `L.isPrefixOf` s = (T.pack (L.reverse acc), T.pack s)
      | otherwise = go (c : acc) cs

-- | Split @src@ after the last occurrence of @pat@, which ends the first
-- component; @("", src)@ when @pat@ does not occur. Both sides are
-- reversed, so the pattern is reversed with them. An empty @pat@ is an
-- error, raised on the first forced component exactly as in the
-- @Data.Text@ original (hence the lazy pattern binding).
breakOnEnd :: Text -> Text -> (Text, Text)
breakOnEnd pat src = (reverseText post, reverseText pre)
  where
    (pre, post) = breakOn (reverseText pat) (reverseText src)
    -- Eta-expanded: the point-free form trips a MicroHs type-inference bug
    -- (dev-docs/MICROHS_GAPS.md, gap 4).
    reverseText t = T.pack (L.reverse (T.unpack t))

-- | Map every character to a 'Text' and concatenate the results.
-- Eta-expanded for the same reason as 'reverseText'.
concatMap :: (Char -> Text) -> Text -> Text
concatMap f t = T.concat (L.map f (T.unpack t))

-- | The last character of a text. Partial like the @Data.Text@ original:
-- an empty text is an error.
last :: Text -> Char
last t
  | T.null t = error "Data.Text.Shim.last: empty text"
  | otherwise = L.last (T.unpack t)
