{-# LANGUAGE TemplateHaskell #-}

-- | Standard library embedding.
--
-- Embeds all @.chr@ files from the @libraries/@ directory at compile time.
-- Each file becomes an entry in the 'stdlib' map, keyed by filename without
-- extension.
module YCHR.StdLib (stdlib) where

import Data.Map.Strict (Map)
import Data.Text (Text)
import YCHR.Parsed (Module)
import YCHR.StdLib.TH (readLibraries)

stdlib :: Map Text Module
stdlib = $$(readLibraries)
