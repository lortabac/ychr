{-# LANGUAGE TemplateHaskell #-}

-- | Embeds the pre-compiled type-checker CHR program.
module YCHR.TypeCheck.Compiled (typeCheckerProgram) where

import YCHR.TypeCheck.TH (TypeCheckerProgram, compileTypeChecker)

typeCheckerProgram :: TypeCheckerProgram
typeCheckerProgram = $$(compileTypeChecker)
