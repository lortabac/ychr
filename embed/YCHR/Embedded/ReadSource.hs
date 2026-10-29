-- | Reading a @.chr@ source file inside a TH splice.
--
-- Shared by 'YCHR.Embedded.StdLib' and 'YCHR.Embedded.TypeCheck', the
-- two embedders that splice source files in at GHC build time.
module YCHR.Embedded.ReadSource (readSourceTH) where

import Data.Text (Text)
import Data.Text qualified as T
import Language.Haskell.TH (Q, reportError)
import Language.Haskell.TH.Syntax (runIO)
import YCHR.Internal.SourceFile (readUtf8File)

-- | Read a file as UTF-8 ('readUtf8File'), at GHC build time. A
-- failure calls 'reportError' (matching 'YCHR.Embedded.StdLib's
-- 'checkSourcesMatch') and yields empty text, so the splice still
-- type-checks and the build fails once, with a clear message.
readSourceTH :: FilePath -> Q Text
readSourceTH path = do
  result <- runIO (readUtf8File path)
  case result of
    Left reason -> do
      reportError (path ++ ": " ++ T.unpack reason)
      pure T.empty
    Right contents -> pure contents
