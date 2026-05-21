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
import Data.List.NonEmpty qualified as NE
import Data.Text (Text)
import Data.Text qualified as T
import YCHR.Backend.Scheme (compileSymbol, qualifiedAliasIdentifier)
import YCHR.Compile (funcProcName)
import YCHR.Compile.Names (vmName)
import YCHR.Resolved qualified as R
import YCHR.SExpr (SExpr (..), printSExpr)
import YCHR.Types (HeadArg (..), QualifiedName, Term (..))
import YCHR.Types qualified as Types
import YCHR.VM.Types (Name (..))

-- | Generate a complete Scheme driver script.
--
-- The script imports the generated library, creates fresh logical
-- variables for each variable mentioned in the goal arguments, calls
-- the tell procedure, and prints each variable binding sorted
-- alphabetically. Argument expressions are evaluated like any other
-- tell-side expression: 'CallExpr' triggers a function call,
-- 'HostExpr' a host call, 'CtorExpr' builds a compound term, and so
-- on.
generateDriver :: Text -> QualifiedName -> [R.Expr] -> Text
generateDriver moduleName qn args =
  let arity = length args
      -- Use the exported friendly alias (e.g. @mod:name/2@) emitted by
      -- the Scheme backend, not the internal mangled @tell_*@ — the
      -- mangled procedures are no longer exported by generated
      -- libraries. 'qualifiedAliasIdentifier' is total: it encodes any
      -- constraint name into a well-formed Scheme identifier.
      tellAlias = qualifiedAliasIdentifier (Types.qualifiedToName qn) arity
      varNames = nub (concatMap exprVars args)
      sortedVars = sort varNames
      argExprs = map exprToScheme args
      tellCall = "(" <> tellAlias <> " %s " <> T.intercalate " " argExprs <> ")"
      bindingsCall = case sortedVars of
        [] -> []
        vs ->
          [ "(pretty-bindings (list "
              <> T.intercalate
                " "
                ["(cons (quote " <> v <> ") " <> v <> ")" | v <- vs]
              <> "))"
          ]
      body = map ("    " <>) (tellCall : bindingsCall)
      -- The generated library's program-info binding is a thunk named
      -- after the library's final segment; calling it creates a fresh
      -- session.
      openSession = "(let ((%s (" <> moduleName <> ")))"
   in T.unlines $
        [ "(import (rnrs) (ychr runtime) (ychr pretty)",
          "        (ychr generated " <> moduleName <> "))",
          ""
        ]
          ++ case varNames of
            [] ->
              [openSession]
                ++ body
                ++ [")"]
            _ ->
              [ openSession,
                "  (let* ("
                  <> T.intercalate
                    "\n         "
                    [ "("
                        <> v
                        <> " (make-var %s))"
                    | v <- varNames
                    ]
                  <> ")"
              ]
                ++ body
                ++ ["))"]

-- | Convert an 'R.Expr' to a Scheme expression. Mirrors the dispatch
-- in 'YCHR.Compile.compileExpr' / 'YCHR.Backend.Scheme.compileValExpr':
-- 'CallExpr' becomes a function call, 'HostExpr' a host bridge,
-- 'CtorExpr' a 'make-term', and so on. Variables are referenced by
-- their declared name in the surrounding @let*@ block.
exprToScheme :: R.Expr -> Text
exprToScheme (R.VarExpr v) = v
exprToScheme (R.IntExpr n) = T.pack (show n)
exprToScheme (R.FloatExpr n) = printSExpr (SFloat n)
exprToScheme (R.AtomExpr s) = printSExpr (compileSymbol s)
exprToScheme (R.TextExpr s) = printSExpr (SString s)
exprToScheme R.WildcardExpr = "*wildcard*"
-- @term(arg)@: the surface quoting form opts out of evaluation. The
-- inner term stays as a data tree; mirror 'compileTerm' here.
exprToScheme (R.CtorExpr (Types.Unqualified "term") [arg]) =
  termToScheme (R.exprToTerm arg)
exprToScheme (R.CtorExpr name args) =
  let flat = (vmName name).unName
      argExprs = map exprToScheme args
   in "(make-term "
        <> printSExpr (compileSymbol flat)
        <> " (vector "
        <> T.intercalate " " argExprs
        <> "))"
exprToScheme (R.CallExpr qn args) =
  let funcName = funcProcName (Types.qualifiedToName qn) (length args)
      argExprs = map exprToScheme args
   in "(" <> funcName.unName <> " %s " <> T.intercalate " " argExprs <> ")"
exprToScheme (R.HostExpr f args) =
  let argExprs = map exprToScheme args
   in "(" <> hostBridgeName f <> " " <> T.intercalate " " argExprs <> ")"
exprToScheme (R.ApplyExpr f args) =
  let n = length args
      dispatch = "call_" <> T.pack (show n)
      fAndArgs = map exprToScheme (f : args)
   in "(" <> dispatch <> " %s " <> T.intercalate " " fAndArgs <> ")"
exprToScheme (R.FunRefExpr qn arity) =
  -- Mirrors 'compileExpr's encoding for first-class function refs.
  let flat = (vmName (Types.qualifiedToName qn)).unName
   in "(make-term "
        <> printSExpr (compileSymbol "/")
        <> " (vector "
        <> printSExpr (compileSymbol flat)
        <> " "
        <> T.pack (show arity)
        <> "))"
exprToScheme (R.LambdaExpr _ _) =
  error
    "SchemeDriver.exprToScheme: lambdas in goal arguments \
    \are not supported in the Scheme driver"

-- | Host-call bridge name. Mirrors the encoding used by
-- 'YCHR.Backend.Scheme.compileHostCall'.
hostBridgeName :: Text -> Text
hostBridgeName f = "host__" <> f

-- | Convert a 'Term' to a Scheme expression. Used for the
-- @term(...)@ quoting form, which keeps the inner tree opaque.
termToScheme :: Term -> Text
termToScheme (IntTerm n) = T.pack (show n)
termToScheme (FloatTerm n) = printSExpr (SFloat n)
termToScheme (AtomTerm s) = printSExpr (compileSymbol s)
termToScheme (TextTerm s) = printSExpr (SString s)
termToScheme (VarTerm n) = n
termToScheme Wildcard = "*wildcard*"
termToScheme (CompoundTerm (Types.Unqualified ".") [h, t]) =
  "(%cons " <> termToScheme h <> " " <> termToScheme t <> ")"
termToScheme (CompoundTerm name@(Types.Qualified _ _) ts) =
  let flat = (vmName name).unName
      argExprs = map termToScheme ts
   in "(make-term "
        <> printSExpr (compileSymbol flat)
        <> " (vector "
        <> T.intercalate " " argExprs
        <> "))"
termToScheme (CompoundTerm (Types.Unqualified n) ts) =
  let symExpr = compileSymbol n
      argExprs = map termToScheme ts
   in "(make-term " <> printSExpr symExpr <> " (vector " <> T.intercalate " " argExprs <> "))"

-- | Collect every variable name mentioned anywhere in an expression
-- tree, so each can be declared as a logical variable in the
-- surrounding @let*@ block. Lambda parameter names are excluded
-- (they are bound locally), though lambdas are not actually supported
-- in this path — see 'exprToScheme'.
exprVars :: R.Expr -> [Text]
exprVars (R.VarExpr v) = [v]
exprVars (R.CtorExpr _ args) = concatMap exprVars args
exprVars (R.CallExpr _ args) = concatMap exprVars args
exprVars (R.ApplyExpr f args) = exprVars f ++ concatMap exprVars args
exprVars (R.HostExpr _ args) = concatMap exprVars args
exprVars (R.LambdaExpr params body) =
  filter (`notElem` [v | HeadVar v <- NE.toList params]) (exprVars body)
exprVars _ = []
