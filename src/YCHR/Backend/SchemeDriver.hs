{-# LANGUAGE OverloadedStrings #-}

-- | Generate a Scheme driver script that executes a single CHR query
-- against a compiled Scheme library.
--
-- The generated script imports the compiled library, creates logical
-- variables for query variables, calls the appropriate @tell_*@
-- procedure, and prints the variable bindings in the same format as
-- 'YCHR.Pretty.prettyBindings'.
module YCHR.Backend.SchemeDriver
  ( generateDriver,
  )
where

import Data.List (nub, sort)
import Data.Text (Text)
import Data.Text qualified as T
import YCHR.Backend.Scheme (compileSymbol)
import YCHR.Compile (tellProcName)
import YCHR.SExpr (SExpr (..), printSExpr)
import YCHR.Types (Constraint (..), Term (..))
import YCHR.Types qualified as Types
import YCHR.VM.Types (Name (..))

-- | Generate a complete Scheme driver script.
--
-- The script imports the generated library, creates fresh logical
-- variables for each 'VarTerm' in the query, calls the tell procedure,
-- and prints each variable binding sorted alphabetically.
generateDriver :: Text -> Constraint -> Text
generateDriver moduleName constraint =
  let arity = length constraint.args
      tellName = tellProcName constraint.name arity
      varNames = nub [n | VarTerm n <- constraint.args]
      sortedVars = sort varNames
      argExprs = map termToScheme constraint.args
      tellCall = "(" <> tellName.unName <> " %s " <> T.intercalate " " argExprs <> ")"
      printStmts = concatMap mkPrintBinding sortedVars
      body = map ("    " <>) (tellCall : printStmts)
   in T.unlines $
        [ "(import (rnrs) (ychr runtime) (ychr pretty)",
          "        (ychr generated " <> moduleName <> "))",
          ""
        ]
          ++ case varNames of
            [] ->
              ["(let ((%s (%init!)))"]
                ++ body
                ++ [")"]
            _ ->
              [ "(let ((%s (%init!)))",
                "  (let* (" <> T.intercalate "\n         " ["(" <> v <> " (make-var %s))" | v <- varNames] <> ")"
              ]
                ++ body
                ++ ["))"]

-- | Convert a 'Term' to a Scheme expression.
termToScheme :: Term -> Text
termToScheme (IntTerm n) = T.pack (show n)
termToScheme (FloatTerm n) = printSExpr (SFloat n)
termToScheme (AtomTerm s) = printSExpr (compileSymbol s)
termToScheme (TextTerm s) = printSExpr (SString s)
termToScheme (VarTerm n) = n
termToScheme Wildcard = "*wildcard*"
termToScheme (CompoundTerm (Types.Unqualified ".") [h, t]) =
  "(%cons " <> termToScheme h <> " " <> termToScheme t <> ")"
termToScheme (CompoundTerm name ts) =
  let f = case name of
        Types.Unqualified n -> n
        Types.Qualified m n -> m <> ":" <> n
      symExpr = compileSymbol f
      argExprs = map termToScheme ts
   in "(make-term " <> printSExpr symExpr <> " (vector " <> T.intercalate " " argExprs <> "))"

-- | Generate display statements for one variable binding.
mkPrintBinding :: Text -> [Text]
mkPrintBinding var =
  [ "(display \"" <> var <> " = \")",
    "(display (pretty-term (deref " <> var <> ")))",
    "(newline)"
  ]
