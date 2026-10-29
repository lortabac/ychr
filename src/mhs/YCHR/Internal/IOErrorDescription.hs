-- | 'IOException' description access, MicroHs build.
--
-- MicroHs: @System.IO.Error@ exports the record. The twin module
-- under @src\/ghc\/YCHR\/Internal\/IOErrorDescription.hs@ reaches it
-- from @GHC.IO.Exception@ instead; the two are switched by
-- @if impl(...)@ blocks in @ychr.cabal@.
module YCHR.Internal.IOErrorDescription (ioeDescription) where

import Control.Exception (IOException)
import System.IO.Error (IOException (ioe_description))

-- | The OS-level description an 'IOException' carries, if it set one.
-- File-open errors do not set one under MicroHs at all — every
-- 'openFile'\/'openBinaryFile' failure passes an empty description —
-- so this is 'Nothing' far more often than under GHC; see
-- @dev-docs\/MICROHS_GAPS.md@ gap 11.
ioeDescription :: IOException -> Maybe String
ioeDescription e
  | null d = Nothing
  | otherwise = Just d
  where
    d = ioe_description e
