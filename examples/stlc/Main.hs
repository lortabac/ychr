{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}

-- | An end-to-end example of embedding a CHR module in a Haskell program.
--
-- @examples/stlc/stlc.chr@ is a Curry-style simply-typed lambda-calculus
-- type inferencer written in CHR. This driver parses a small surface
-- syntax (see "Parser"), encodes the resulting term into CHR data with the
-- @ToTerm@ instance in "Syntax", runs the @typecheck/2@ goal with
-- 'runQueryCompiled', and
-- decodes the inferred type back into a Haskell 'Type' (or a type error)
-- with 'FromTerm' — the whole round trip goes through "YCHR.Convert".
--
-- With no arguments it is a small type-inference REPL; @--demo@ prints a
-- fixed table:
--
-- > cabal run stlc-typechecker            # REPL
-- > cabal run stlc-typechecker -- --demo  # demo table
module Main (main) where

import Control.Monad (forM_, when)
import Data.Char (isSpace)
import Data.List (intercalate)
import Data.Text (Text)
import Data.Text qualified as T
import Embed (stlcPath, stlcSource)
import Parser (parseExpr)
import Syntax (Expr)
import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.IO
  ( BufferMode (NoBuffering),
    hFlush,
    hIsTerminalDevice,
    hPutStrLn,
    hSetBuffering,
    isEOF,
    stderr,
    stdin,
    stdout,
  )
import YCHR
  ( CompiledProgram,
    FromTerm (..),
    Name (..),
    Term (..),
    argAt,
    compileModules,
    compound,
    decodeSum,
    quoted,
    runQueryCompiled,
  )

-- ---------------------------------------------------------------------------
-- Decoding the result
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
  args <- getArgs
  cp <- loadInferencer
  case args of
    ["--demo"] -> runDemo cp
    [] -> runRepl cp
    _ -> hPutStrLn stderr "usage: stlc-typechecker [--demo]" >> exitFailure

-- | Compile the embedded inferencer once; reuse it across every query.
loadInferencer :: IO CompiledProgram
loadInferencer =
  case compileModules True [(stlcPath, $(stlcSource))] of
    Left err -> fail ("could not compile " ++ stlcPath ++ ":\n" ++ show err)
    Right (cp, _warnings) -> pure cp

-- | Parse, type-check, and render one line of surface syntax.
inferLine :: CompiledProgram -> String -> IO String
inferLine cp line = case parseExpr line of
  Left err -> pure ("parse error: " ++ firstLine err)
  Right e -> do
    result <- runQueryCompiled cp (typecheckGoal e) "Result"
    pure (either show renderResult result)

-- | Build the goal @typecheck(term(<expr>), Result)@. The @term/1@ quote
-- ('quoted') keeps the expression symbolic: without it the argument would
-- be evaluated, and @var(\"x\")@ in particular would call the prelude's
-- @var/1@ predicate instead of naming a variable node.
typecheckGoal :: Expr -> Term
typecheckGoal e = compound "typecheck" [quoted e, VarTerm "Result"]

-- ---------------------------------------------------------------------------
-- REPL
-- ---------------------------------------------------------------------------

runRepl :: CompiledProgram -> IO ()
runRepl cp = do
  hSetBuffering stdout NoBuffering
  interactive <- hIsTerminalDevice stdin
  when interactive $
    putStrLn "STLC type-inference REPL. Enter a lambda term (e.g. \\x. x + 1); :q to quit."
  loop interactive
  where
    loop interactive = do
      when interactive (putStr "stlc> ")
      hFlush stdout
      atEof <- isEOF
      if atEof
        then when interactive (putStrLn "")
        else do
          line <- getLine
          keepGoing <- step interactive line
          when keepGoing (loop interactive)

    step interactive line
      | command `elem` [":q", ":quit"] = pure False
      | null command = pure True
      | otherwise = do
          when (not interactive) (putStrLn ("stlc> " ++ line))
          inferLine cp line >>= putStrLn
          pure True
      where
        command = strip line

-- ---------------------------------------------------------------------------
-- Demo table
-- ---------------------------------------------------------------------------

runDemo :: CompiledProgram -> IO ()
runDemo cp = do
  putStrLn "Curry-style STLC type inference (via a CHR module):\n"
  forM_ demoInputs $ \s -> do
    rendered <- inferLine cp s
    putStrLn (pad 26 s ++ " :  " ++ rendered)

demoInputs :: [String]
demoInputs =
  [ "\\x. x + 1",
    "\\x. x",
    "(\\x. x + 1) 5",
    "\\x. \\y. x",
    "\\f. \\x. f (f x)",
    "let f = \\x. x + 1 in f 5",
    "\\x. x x",
    "1 2",
    "y"
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

strip :: String -> String
strip = f . f where f = reverse . dropWhile isSpace

-- | Collapse a multi-line parse-error message to its first non-empty line
-- so the REPL prints one tidy line.
firstLine :: String -> String
firstLine = unwords . filter (not . null) . map strip . lines
