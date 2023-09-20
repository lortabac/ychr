{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE OverloadedStrings #-}

module YCHR.Compiler.Compile where

import Data.Text.Show (tshow)
import YCHR.Types.Common
import YCHR.Types.Imp
import YCHR.Types.Prepared

compileOccurrence :: PrRule -> Occurrence -> Procedure Variable
compileOccurrence prRule occ = Procedure (suspId : args) procBody
  where
    suspId = Variable ("suspId")
    args = map (\i -> Variable ("arg" <> tshow i)) [1 .. length occ.arguments]
    procBody = foldr iter action (prRule.head ++ prRule.remove)
    iter constr proc =
      if occ.position /= constr.position
        then
          Foreach
            (Variable ("susp" <> tshow constr.position))
            (SuspLookup constr.constraint.name)
            proc
        else proc
    action = Noop
