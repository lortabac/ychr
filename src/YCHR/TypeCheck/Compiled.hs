{-# LANGUAGE TemplateHaskell #-}

-- | Embeds the pre-compiled type-checker CHR program.
module YCHR.TypeCheck.Compiled (typeCheckerProgram) where

import YCHR.Runtime.Session (SessionInput)
import YCHR.TypeCheck.TH (compileTypeChecker)

typeCheckerProgram :: SessionInput
typeCheckerProgram = $$(compileTypeChecker)
