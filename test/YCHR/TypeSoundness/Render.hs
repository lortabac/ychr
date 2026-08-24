{-# LANGUAGE OverloadedStrings #-}

-- | Pretty-printing a generated program back to @.chr@ source and to a
-- query.
--
-- The generator emits concrete source text rather than an AST, so
-- every generated program goes through the real parser, renamer,
-- resolver and desugarer — and a counterexample is directly runnable.
module YCHR.TypeSoundness.Render
  ( renderModule,
    renderQuery,
    renderAdt,
    renderConstraintDecl,
    renderRule,
    renderExpr,
    renderSTerm,
    renderPat,
  )
where

import Data.List.NonEmpty (NonEmpty (..))
import Data.List.NonEmpty qualified as NE
import Data.Text (Text)
import Data.Text qualified as T
import YCHR.TypeSoundness.Preamble
import YCHR.TypeSoundness.Types

renderAnn :: Ann -> Text
renderAnn a = if a.erased then "any" else renderTy a.declared

renderLit :: Lit -> Text
renderLit l = case l of
  LInt n -> tshow n
  LBool True -> "true"
  LBool False -> "false"

args_ :: [Text] -> Text
args_ ts = "(" <> T.intercalate ", " ts <> ")"

-- | A constructor application, collapsing the nullary case to a bare
-- atom (which is how a 0-arity constructor is written in source).
applied :: Text -> [Text] -> Text
applied f [] = f
applied f as = f <> args_ as

renderModule :: Program -> Text
renderModule prog =
  T.unlines
    ( [ ":- module(gen).",
        ":- use_module(library(prelude)).",
        ""
      ]
        ++ concatMap renderAdt (fixedAdts ++ prog.adts)
        ++ [preamble]
        ++ [renderConstraintDecl prog.sigs, ""]
        ++ map renderRule prog.rules
    )

-- | A generated type declaration plus its runtime assertion predicate.
renderAdt :: AdtDef -> [Text]
renderAdt def =
  [ ":- chr_type "
      <> def.adtName
      <> " ---> "
      <> T.intercalate " ; " (map renderCtorDecl (NE.toList def.ctors))
      <> ".",
    ":- function " <> assertFn (TAdt def) <> "(" <> def.adtName <> ") -> bool."
  ]
    ++ map renderAssertEq (NE.toList def.ctors)
    ++ [""]
  where
    renderCtorDecl c = applied c.ctorName (map renderTy c.fields)
    renderAssertEq c =
      let vars = ["F" <> tshow i | i <- [0 .. length c.fields - 1]]
          checks =
            T.intercalate
              ", "
              (zipWith (\t v -> assertFn t <> "(" <> v <> ")") c.fields vars)
          guardPart = if null c.fields then "" else " | " <> checks
       in assertFn (TAdt def)
            <> "("
            <> applied c.ctorName vars
            <> ")"
            <> guardPart
            <> " -> true."

renderConstraintDecl :: NonEmpty Sig -> Text
renderConstraintDecl ss =
  ":- chr_constraint "
    <> T.intercalate ", " (map one (NE.toList ss))
    <> "."
  where
    one s = s.sigName <> args_ (map renderAnn (NE.toList s.argAnns))

renderRule :: Rule -> Text
renderRule r =
  r.ruleName
    <> " @ "
    <> headText
    <> " "
    <> guardText
    <> bodyText
    <> "."
  where
    headText = case r.ruleHead of
      HSimplify hs -> renderHeads hs <> " <=>"
      HPropagate hs -> renderHeads hs <> " ==>"
      HSimpagate ks rs -> renderHeads ks <> " \\ " <> renderHeads rs <> " <=>"
    renderHeads hs = T.intercalate ", " (map renderHeadC (NE.toList hs))
    guardText
      | null r.guards = ""
      | otherwise = T.intercalate ", " (map renderExpr r.guards) <> " | "
    bodyText
      | null r.body = "true"
      | otherwise = T.intercalate ", " (map renderBodyItem r.body)

renderHeadC :: HeadC -> Text
renderHeadC h = h.headSig.sigName <> args_ (map renderPat (NE.toList h.pats))

renderPat :: Pat -> Text
renderPat p = case p of
  PVar n _ -> n
  PWild -> "_"
  PLit l -> renderLit l
  PCtor c ps -> applied c (map renderPat ps)
  PNil -> "[]"
  PCons h t -> renderListLike (renderPat h) (renderPat t) (t == PNil)

-- | Render a cons cell as list syntax, given the head and tail already
-- rendered and whether the tail is the empty list. A spine ending in
-- @[]@ prints as @[a, b]@; anything else keeps the tail after a bar,
-- @[a | T]@.
--
-- Splicing the tail's own brackets is safe because a cons tail is
-- always list-typed, so it renders as @[]@, a @[…]@ list, a variable,
-- or @_@ — never as something unrelated that happens to end in @]@.
renderListLike :: Text -> Text -> Bool -> Text
renderListLike hd tl tailIsNil
  | tailIsNil = "[" <> hd <> "]"
  | Just inner <- T.stripPrefix "[" tl,
    Just body <- T.stripSuffix "]" inner,
    not (T.null body) =
      "[" <> hd <> ", " <> body <> "]"
  | otherwise = "[" <> hd <> " | " <> tl <> "]"

renderExpr :: Expr -> Text
renderExpr e = case e of
  ELit l -> renderLit l
  EVar n _ -> n
  EListLit es -> "[" <> T.intercalate ", " (map renderExpr es) <> "]"
  ECtor c es -> applied c (map renderExpr es)
  EArith op a b -> infix_ (arithOp op) a b
  ECmp op a b -> infix_ (cmpOp op) a b
  EEq _ a b -> infix_ "==" a b
  ENot a -> "not(" <> renderExpr a <> ")"
  ECall fn es -> libFnName fn <> args_ (map renderExpr es)
  where
    infix_ o a b = "(" <> renderExpr a <> " " <> o <> " " <> renderExpr b <> ")"
    arithOp op = case op of
      Add -> "+"
      Sub -> "-"
      Mul -> "*"
    cmpOp op = case op of
      CLt -> "<"
      CGt -> ">"
      CGe -> ">="
      CLe -> "=<"

renderSTerm :: STerm -> Text
renderSTerm t = case t of
  SLit l -> renderLit l
  SVar n _ -> n
  SNil -> "[]"
  SCons h tl -> renderListLike (renderSTerm h) (renderSTerm tl) (tl == SNil)
  SCtor c ts -> applied c (map renderSTerm ts)

renderBodyItem :: BodyItem -> Text
renderBodyItem it = case it of
  BTell s es -> s.sigName <> args_ (map renderExpr es)
  BIs w _ e -> w <> " is " <> renderExpr e
  BUnify w _ st -> w <> " = " <> renderSTerm st
  BAssert n ty -> assertFn ty <> "(" <> n <> ")"

-- | The query: the goal tells (module-qualified, as every goal in the
-- golden suite is), then each probe followed by its runtime type
-- assertion.
renderQuery :: Program -> Text
renderQuery prog =
  T.intercalate ", " (map tell_ (NE.toList prog.goal.tells) ++ probeParts) <> "."
  where
    tell_ (s, es) = "gen:" <> s.sigName <> args_ (map renderExpr es)
    probeParts =
      concat
        [ [ p.probeVar <> " is " <> renderExpr p.probeExpr,
            "B" <> tshow i <> " is " <> assertFn p.probeTy <> "(" <> p.probeVar <> ")"
          ]
        | (i, p) <- zip [0 :: Int ..] prog.goal.probes
        ]
