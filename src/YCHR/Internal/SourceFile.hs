{-# LANGUAGE OverloadedStrings #-}

-- | Reading a @.chr@ source file as UTF-8, explicit of locale.
--
-- A leaf module: no dependency on the compiler, so any component
-- (the compiler, the on-disk resource loader, the TH embedders, the
-- CLI) can read a source file without pulling in the rest of the
-- pipeline.
module YCHR.Internal.SourceFile
  ( readUtf8File,
    ioExceptionReason,
  )
where

import Control.Exception (IOException, try)
import Data.ByteString qualified as BS
import Data.Char (toUpper)
import Data.Maybe (fromMaybe)
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.Encoding qualified as TE
import System.IO.Error (ioeGetErrorString)
import YCHR.Internal.IOErrorDescription (ioeDescription)

-- | Read a file's contents as UTF-8 text, decoded explicitly rather
-- than through the process locale: a valid UTF-8 source must read the
-- same way under @LC_ALL=C@ as under a UTF-8 locale. 'Left' carries a
-- human-readable reason — an 'IOException's own ('ioExceptionReason'),
-- or @"Not valid UTF-8"@ for a decoding failure — never thrown.
readUtf8File :: FilePath -> IO (Either Text Text)
readUtf8File fp = do
  r <- try @IOException (BS.readFile fp)
  pure $ case r of
    Left e -> Left (ioExceptionReason e)
    Right bytes
      | BS.isValidUtf8 bytes -> Right (TE.decodeUtf8 bytes)
      | otherwise -> Left "Not valid UTF-8"

-- | A readable reason for an 'IOException', capitalized.
--
-- 'YCHR.Internal.IOErrorDescription.ioeDescription' reaches the OS's
-- own text when the host set one — @"No such file or directory"@,
-- @"Is a directory"@ — which says a lot more than 'ioeGetErrorString'
-- alone, which only gives the generic error category ("does not
-- exist", "inappropriate type"). Falls back to that category when
-- there is no description, which is the case for a MicroHs
-- @openFile@\/@openBinaryFile@ failure (see @dev-docs\/MICROHS_GAPS.md@
-- gap 11). Capitalized because the two sources disagree on case.
ioExceptionReason :: IOException -> Text
ioExceptionReason e = T.pack (capitalizeHead reason)
  where
    reason = fromMaybe (ioeGetErrorString e) (ioeDescription e)
    capitalizeHead [] = []
    capitalizeHead (c : cs) = toUpper c : cs
