-- | 'IOException' description access, GHC build.
--
-- GHC: @ioe_description@ comes from @GHC.IO.Exception@, since base's
-- own @System.IO.Error@ keeps 'IOException' abstract. The twin module
-- under @src\/mhs\/YCHR\/Internal\/IOErrorDescription.hs@ reaches it
-- from @System.IO.Error@ instead; the two are switched by
-- @if impl(...)@ blocks in @ychr.cabal@.
module YCHR.Internal.IOErrorDescription (ioeDescription) where

import Control.Exception (IOException)
import GHC.IO.Exception (IOException (ioe_description))

-- | The OS-level description an 'IOException' carries, if it set one.
-- File-open errors do ("No such file or directory", "Is a
-- directory"); most others don't — see @dev-docs\/MICROHS_GAPS.md@
-- gap 11 for which is which under MicroHs.
ioeDescription :: IOException -> Maybe String
ioeDescription e
  | null d = Nothing
  | otherwise = Just d
  where
    d = ioe_description e
