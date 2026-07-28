{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}

-- | An end-to-end example of embedding a CHR module in a Haskell program.
--
-- @examples/stlc/stlc.chr@ is a Curry-style simply-typed lambda-calculus
-- type inferencer written in CHR. This driver embeds it, encodes Haskell
-- 'Expr' values into CHR terms with 'ToTerm', runs the @typecheck/2@ goal
-- with 'runQueryCompiled', and decodes the result back into a Haskell
-- 'Type' (or a type error) with 'FromTerm' — the whole round trip goes
-- through "YCHR.Convert".
--
-- Run it with:
--
-- > cabal run stlc-typechecker
module Main (main) where

import Data.Text (Text)
import Data.Text qualified as T
import Embed (stlcPath, stlcSource)
import YCHR.Convert
  ( FromTerm (..),
    ToTerm (..),
    argAt,
    compound,
    decodeSum,
    runQueryCompiled,
  )
import YCHR.Run (CompiledProgram, compileModules)
import YCHR.Types (Name (..), Term (..))

-- ---------------------------------------------------------------------------
-- The object language: unannotated lambda terms
-- ---------------------------------------------------------------------------

data Expr
  = Var Text
  | Lam Text Expr
  | App Expr Expr
  | IntLit Integer
  | Add Expr Expr

-- | Encode a term as the CHR data the inferencer matches on. These are
-- plain compounds (@var@, @lam@, …), which the driver passes in quoted
-- with @term/1@ (see 'typecheckGoal') so they are treated as data rather
-- than evaluated.
instance ToTerm Expr where
  toTerm (Var x) = compound "var" [toTerm x]
  toTerm (Lam x body) = compound "lam" [toTerm x, toTerm body]
  toTerm (App f a) = compound "app" [toTerm f, toTerm a]
  toTerm (IntLit n) = compound "lit_int" [toTerm n]
  toTerm (Add a b) = compound "add" [toTerm a, toTerm b]

-- ---------------------------------------------------------------------------
-- The type language and the result of inference
-- ---------------------------------------------------------------------------

data Type
  = TInt
  | TArrow Type Type
  | TVar Int

-- | Decode a @ty@ term. The functor is matched on its local name, so the
-- module-qualified @stlc:arrow@ that comes back still decodes.
instance FromTerm Type where
  fromTerm =
    decodeSum
      [ ("tint", 0, \_ -> Right TInt),
        ("arrow", 2, \as -> TArrow <$> argAt 0 as <*> argAt 1 as),
        ("tvar", 1, \as -> TVar <$> argAt 0 as)
      ]

-- | The inferencer answers with @ok(Type)@ or @type_error(Errors)@. The
-- error list is kept as raw 'Term's (they mention pre-generalization type
-- variables that would not decode as a ground 'Type') and rendered below.
data TCResult
  = Ok Type
  | Ill [Term]

instance FromTerm TCResult where
  fromTerm =
    decodeSum
      [ ("ok", 1, \as -> Ok <$> argAt 0 as),
        ("type_error", 1, \as -> Ill <$> argAt 0 as)
      ]

-- ---------------------------------------------------------------------------
-- Driver
-- ---------------------------------------------------------------------------

main :: IO ()
main = do
  cp <- loadInferencer
  putStrLn "Curry-style STLC type inference (via a CHR module):\n"
  mapM_ (runOne cp) demos

-- | Compile the embedded inferencer once; reuse it across every query.
loadInferencer :: IO CompiledProgram
loadInferencer =
  case compileModules True [(stlcPath, $(stlcSource))] of
    Left err -> fail ("could not compile " ++ stlcPath ++ ":\n" ++ show err)
    Right (cp, _warnings) -> pure cp

runOne :: CompiledProgram -> (String, Expr) -> IO ()
runOne cp (label, e) = do
  result <- runQueryCompiled cp (typecheckGoal e) "Result"
  putStrLn (pad 22 label ++ " :  " ++ either show renderResult result)

-- | Build the goal @typecheck(term(<expr>), Result)@. The @term/1@ quote
-- keeps the expression symbolic: without it the argument would be
-- evaluated, and @var(\"x\")@ in particular would call the prelude's
-- @var/1@ predicate instead of naming a variable node.
typecheckGoal :: Expr -> Term
typecheckGoal e =
  CompoundTerm
    (Unqualified "typecheck")
    [ CompoundTerm (Unqualified "term") [toTerm e],
      VarTerm "Result"
    ]

demos :: [(String, Expr)]
demos =
  [ ("\\x. x + 1", Lam "x" (Add (Var "x") (IntLit 1))),
    ("\\x. x", Lam "x" (Var "x")),
    ("(\\x. x + 1) 5", App (Lam "x" (Add (Var "x") (IntLit 1))) (IntLit 5)),
    ("\\x. \\y. x", Lam "x" (Lam "y" (Var "x"))),
    ("\\f. \\x. f (f x)", Lam "f" (Lam "x" (App (Var "f") (App (Var "f") (Var "x"))))),
    ("\\x. x x", Lam "x" (App (Var "x") (Var "x"))),
    ("1 2", App (IntLit 1) (IntLit 2)),
    ("y", Var "y")
  ]

-- ---------------------------------------------------------------------------
-- Rendering
-- ---------------------------------------------------------------------------

renderResult :: TCResult -> String
renderResult (Ok t) = renderType False t
renderResult (Ill errs) = "TYPE ERROR: " ++ intercalate "; " (map describeError errs)

renderType :: Bool -> Type -> String
renderType _ TInt = "int"
renderType _ (TVar n) = tyVarName n
renderType paren (TArrow a b) =
  parenthesize paren (renderType True a ++ " -> " ++ renderType False b)

-- | Render a type that is still a raw 'Term' (as it appears inside an
-- error), tolerating the unbound variables an in-progress inference leaves
-- behind.
renderTypeTerm :: Term -> String
renderTypeTerm t = case t of
  CompoundTerm n [] | localName n == "tint" -> "int"
  CompoundTerm n [IntTerm k] | localName n == "tvar" -> tyVarName (fromInteger k)
  CompoundTerm n [a, b]
    | localName n == "arrow" ->
        "(" ++ renderTypeTerm a ++ " -> " ++ renderTypeTerm b ++ ")"
  TextTerm s -> T.unpack s
  -- A type variable still unbound at the point the error was raised.
  VarTerm _ -> "_"
  Wildcard -> "_"
  _ -> "?"

describeError :: Term -> String
describeError t = case t of
  CompoundTerm n [a, b]
    | localName n == "mismatch" ->
        "cannot unify " ++ renderTypeTerm a ++ " with " ++ renderTypeTerm b
  CompoundTerm n [_, ty]
    | localName n == "infinite_type" ->
        "cannot construct the infinite type " ++ renderTypeTerm ty
  CompoundTerm n [x]
    | localName n == "unbound_variable" ->
        "unbound variable " ++ renderTypeTerm x
  _ -> "?"

-- ---------------------------------------------------------------------------
-- Small helpers
-- ---------------------------------------------------------------------------

localName :: Name -> Text
localName (Unqualified n) = n
localName (Qualified _ n) = n

tyVarName :: Int -> String
tyVarName n
  | n < 26 = [toEnum (fromEnum 'a' + n)]
  | otherwise = 't' : show n

parenthesize :: Bool -> String -> String
parenthesize True s = "(" ++ s ++ ")"
parenthesize False s = s

pad :: Int -> String -> String
pad w s = s ++ replicate (max 1 (w - length s)) ' '

intercalate :: String -> [String] -> String
intercalate _ [] = ""
intercalate _ [x] = x
intercalate sep (x : xs) = x ++ sep ++ intercalate sep xs
