module Data.Text.Show where

import Data.Text (Text)
import qualified Data.Text as T

tshow :: (Show a) => a -> Text
tshow = T.pack . show
