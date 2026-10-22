{-# LANGUAGE OverloadedStrings #-}

-- | Assembling the generated modules.
--
-- Two values are emitted: the standard library ('emitStdLib') and the
-- type-checker ('emitTypeChecker'). Both are literal data — constructor
-- applications, no Template Haskell — so MicroHs can compile them
-- without a staged-compilation facility, which is the whole rationale
-- of @dev-docs\/MICROHS_PERFORMANCE.md@ option B.
--
-- One problem shapes this module: the type-checker's compiled program
-- is about 1.5 MB of @Show@ output, and MicroHs is not built for a
-- single expression that size. 'hoist' therefore flattens the tree into
-- many small top-level bindings before it is rendered:
--
--   * a list literal longer than 'chunkSize', or rendered larger than
--     'maxBindingBytes', is split into groups, each of which becomes its
--     own binding, and the groups are concatenated with @concat@;
--   * any other sub-expression rendered larger than 'maxBindingBytes'
--     is lifted to its own binding.
--
-- Every lifted expression is closed (there are no local binders in the
-- tree), so lifting one to a top-level CAF is a pure re-association, not
-- a change of meaning. Empty lists are never lifted: a bare @[]@ would
-- be polymorphic and the monomorphism restriction would have to
-- default it.
module YCHR.Embedded.Generate.Emit
  ( -- * Options
    EmitOptions (..),
    defaultEmitOptions,

    -- * Output
    TopBinding (..),
    GeneratedModule (..),

    -- * The two generated modules
    emitStdLib,
    emitTypeChecker,

    -- * Internals
    Hoisted (..),
    hoist,
  )
where

import Control.Monad.Trans.State.Strict (State, get, put, runState)
import Data.List (intercalate, nub)
import YCHR.Embedded.Generate.Code
import YCHR.Embedded.Generate.Instances ()
import YCHR.Embedded.Generate.ToCode (ToCode (..))
import YCHR.Internal.PExpr (OpTable, opTableEntries)
import YCHR.Internal.Runtime.Session (SessionInput (..))
import YCHR.Internal.StdLib (StdLib (..))

-- | Knobs for 'hoist'. They exist so that a module MicroHs chokes on
-- can be split finer without touching the emitter; the defaults were
-- chosen for the compiled type-checker.
data EmitOptions = EmitOptions
  { -- | Maximum number of elements in one list-literal binding.
    chunkSize :: Int,
    -- | Budget for one binding body, in rendered characters. 'hoist'
    -- documents the one kind of node that can exceed it.
    maxBindingBytes :: Int
  }
  deriving (Show, Eq)

-- | Thirty-two elements and 8 KB per binding. The element cap only
-- binds for short elements (constraint and rule names, which cost a
-- few characters each); anything substantial reaches the byte budget
-- first, so a wide cap mostly saves bindings without inflating any of
-- them.
defaultEmitOptions :: EmitOptions
defaultEmitOptions = EmitOptions {chunkSize = 32, maxBindingBytes = 8192}

-- | One top-level definition of a generated module.
data TopBinding = TopBinding
  { name :: String,
    -- | Written above the definition when present; used for the
    -- module's exported entry points, whose types are otherwise only
    -- visible through inference in a file nobody reads.
    signature :: Maybe String,
    body :: Code
  }

-- | A generated module, ready to be written.
data GeneratedModule = GeneratedModule
  { -- | Path relative to the output directory, e.g.
    -- @YCHR\/Embedded\/Generated\/StdLib.hs@.
    path :: FilePath,
    source :: String
  }
  deriving (Show, Eq)

-- ---------------------------------------------------------------------------
-- The two modules
-- ---------------------------------------------------------------------------

-- | The module holding the parsed standard library, as
-- @stdlib :: StdLib@.
emitStdLib :: EmitOptions -> StdLib -> GeneratedModule
emitStdLib opts (StdLib modules) =
  buildModule
    ModuleSpec
      { name = "YCHR.Embedded.Generated.StdLib",
        exports = ["stdlib"],
        prologue = "The bundled standard library, decoded by ychr-codegen.",
        fixedImports =
          [ -- Belt-and-braces: the emitter renders 'Maybe' as the bare
            -- @Just@/@Nothing@, and both hosts resolve those without this
            -- import today. It is spelled out because two compilers read
            -- the file and only one of them would notice the day that stops
            -- being true.
            "import Data.Maybe (Maybe (..))",
            "import YCHR.Internal.StdLib (StdLib (..))"
          ],
        entries =
          [ TopBinding
              { name = "stdlib",
                signature = Just "StdLib",
                body = h.body
              }
          ],
        hoisted = h.bindings
      }
  where
    h = hoist opts (CApp (CName "StdLib") [toCode modules])

-- | The module holding the precomputed type-checker, as
-- @typeCheckerProgram :: SessionInput@.
--
-- Only the parts that are not recomputable are emitted: the VM program,
-- the two export tables and the operator table (the VM program carries
-- no operator information, so the runtime reader's table has to be
-- spelled out). 'YCHR.Internal.Runtime.Session.mkSessionInput'
-- rebuilds the slot phase and the indexable positions from the program,
-- exactly as the compiler's own pipeline does, which keeps the
-- generated module about 1.3 MB smaller than serializing the full
-- 'SessionInput'.
emitTypeChecker :: EmitOptions -> SessionInput -> GeneratedModule
emitTypeChecker opts (SessionInput program _ _ exportMap exportedSet ops) =
  buildModule
    ModuleSpec
      { name = "YCHR.Embedded.Generated.TypeCheck",
        exports = ["typeCheckerProgram"],
        prologue = "The bundled type-checker, decoded by ychr-codegen.",
        fixedImports =
          [ -- Unused today, but the emitted AST is the same literal
            -- vocabulary as 'emitStdLib''s, so a field that becomes a
            -- 'Maybe' must not have to remember this import to keep
            -- MicroHs compiling.
            "import Data.Maybe (Maybe (..))",
            "import YCHR.Internal.Runtime.Session (SessionInput)"
          ],
        entries =
          [ TopBinding
              { name = "typeCheckerProgram",
                signature = Just "SessionInput",
                body = h.body
              }
          ],
        hoisted = h.bindings
      }
  where
    h =
      hoist
        opts
        ( CApp
            (CName "Session.mkSessionInput")
            [ toCode program,
              toCode exportMap,
              toCode exportedSet,
              opTableCode ops
            ]
        )

-- | Render an operator table as the @PExpr.mkOpTable@ call that rebuilds
-- it. The table is a derived structure — buckets keyed by fixity plus
-- three lookup maps — so it is emitted from 'opTableEntries' and
-- reconstructed by 'YCHR.Internal.PExpr.mkOpTable' rather than written
-- field by field. The reconstruction is behaviourally identical: a name
-- may not be declared twice at different fixities in one category, so
-- the three lookup maps and the word-operator set are reproduced
-- exactly. Only the order of entries within a fixity bucket may differ
-- ('mkOpTable' prepends with @fromListWith (++)@), which is unobservable
-- because that order is unspecified ('YCHR.Internal.Parser.opTableEntries'
-- documents it as such) and only the maps are consulted when parsing.
opTableCode :: OpTable -> Code
opTableCode table =
  CApp
    (CName "PExpr.mkOpTable")
    [toCode [(fix, [(ty, name)]) | (fix, ty, name) <- opTableEntries table]]

-- ---------------------------------------------------------------------------
-- Hoisting
-- ---------------------------------------------------------------------------

-- | What 'hoist' returns: the expression to render in place, and the
-- bindings to render around it.
data Hoisted = Hoisted
  { body :: Code,
    bindings :: [TopBinding]
  }

-- | The state of the hoisting walk: the number of the next binding, and
-- the bindings made so far, newest first.
data HoistState = HoistState
  { next :: Int,
    bindings :: [TopBinding]
  }

-- | Flatten a tree into a body and the bindings it refers to.
--
-- The invariant is that no binding body exceeds 'maxBindingBytes', with
-- one exception: a node whose bulk is literal cannot be split further
-- without giving the lifted literal a type, so a constructor application
-- (or tuple) holding a very long string is emitted whole.
hoist :: EmitOptions -> Code -> Hoisted
hoist opts root = Hoisted {body = root', bindings = reverse final.bindings}
  where
    (root', final) = runState (walk root) HoistState {next = 0, bindings = []}

    walk :: Code -> State HoistState Code
    walk c = case c of
      CApp f args -> do
        f' <- walk f
        args' <- traverse walk args
        check (CApp f' args')
      CList xs -> do
        xs' <- traverse walk xs
        if length xs' > opts.chunkSize
          || codeSize (CList xs') > opts.maxBindingBytes
          then chunk xs' >>= check
          else check (CList xs')
      CTuple xs -> traverse walk xs >>= check . CTuple
      CParens x -> CParens <$> walk x
      _ -> pure c

    -- Lift a sub-expression that is still too big. A name is already a
    -- binding, so lifting it again would only add indirection.
    check c
      | codeSize c > opts.maxBindingBytes,
        not (isName c),
        not (isEmptyList c) =
          shrink c >>= bind
      | otherwise = pure c

    -- Lifting a node does not shrink it: a constructor application of
    -- a dozen large arguments is still over budget once its binding is
    -- written. Give its structured arguments bindings of their own, so
    -- that what remains is a head and a dozen names. Literal leaves are
    -- deliberately left in place — a top-level binding holding a bare
    -- literal would be ambiguous under the monomorphism restriction.
    shrink (CApp f args) = CApp f <$> traverse liftArg args
    shrink c = pure c

    liftArg arg
      | hoistable arg = bind arg
      | otherwise = pure arg

    hoistable (CApp _ _) = True
    hoistable (CList []) = False
    hoistable (CList _) = True
    hoistable (CTuple _) = True
    hoistable _ = False

    chunk xs = concatLists <$> traverse (bind . CList) (chunkBySize opts xs)

    -- Make a new binding for @c@ and return its name.
    bind :: Code -> State HoistState Code
    bind c = do
      st <- get
      let n = st.next
      put
        HoistState
          { next = n + 1,
            bindings = TopBinding (generatedName n) Nothing c : st.bindings
          }
      pure (CName (generatedName n))

generatedName :: Int -> String
generatedName n = "generated_" ++ show n

isName :: Code -> Bool
isName (CName _) = True
isName _ = False

isEmptyList :: Code -> Bool
isEmptyList (CList []) = True
isEmptyList _ = False

-- | @concat [v0, v1, …]@, the empty list for no chunks. A flat list
-- application rather than a right-nested @v0 ++ (v1 ++ …)@: a procedure
-- list reaches about two hundred chunks, and a chain that deep is both
-- unreadable in the output and a needless recursion depth for the
-- MicroHs parser.
concatLists :: [Code] -> Code
concatLists [] = CList []
concatLists [v] = v
concatLists vars = CApp (CName "concat") [CList vars]

-- | Greedily split a list so that no group exceeds either budget, so
-- that every group can become one reasonably sized binding. The running
-- size is the /rendered/ size, separators included, and the budget
-- leaves room for the surrounding brackets.
chunkBySize :: EmitOptions -> [Code] -> [[Code]]
chunkBySize opts = goChunks [] 0 0
  where
    limit = opts.chunkSize
    budget = max 1 (opts.maxBindingBytes - 2)
    separator = 2
    goChunks cur _ _ [] = [reverse cur | not (null cur)]
    goChunks cur count size (x : xs)
      | null cur = goChunks [x] 1 (codeSize x) xs
      | count < limit,
        size + separator + codeSize x <= budget =
          goChunks (x : cur) (count + 1) (size + separator + codeSize x) xs
      | otherwise = reverse cur : goChunks [x] 1 (codeSize x) xs

-- ---------------------------------------------------------------------------
-- Rendering
-- ---------------------------------------------------------------------------

-- | What 'buildModule' assembles a module from.
data ModuleSpec = ModuleSpec
  { -- | The module name.
    name :: String,
    -- | The names in the module's export list.
    exports :: [String],
    -- | The first line of the module's Haddock.
    prologue :: String,
    -- | Imports written before the derived ones.
    fixedImports :: [String],
    -- | The exported entry points.
    entries :: [TopBinding],
    -- | The bindings the hoisting pass produced.
    hoisted :: [TopBinding]
  }

-- | Assemble a module from its spec. Imports are derived from the
-- aliases the code actually mentions.
buildModule :: ModuleSpec -> GeneratedModule
buildModule spec =
  GeneratedModule
    { path = pathFromModule spec.name,
      source = unlines sourceLines
    }
  where
    allBindings = spec.entries ++ spec.hoisted
    aliases = usedAliases allBindings
    aliasImports =
      [ "import qualified " ++ m ++ " as " ++ a
      | (m, a) <- aliasTable,
        a `elem` aliases
      ]
    sourceLines =
      [ "{-# LANGUAGE OverloadedStrings #-}",
        "",
        "-- | " ++ spec.prologue,
        "--",
        "-- Machine-generated by ychr-codegen; do not edit by hand.",
        "-- Regenerate with `make resources` (see dev-docs/MICROHS_PERFORMANCE.md).",
        "module " ++ spec.name ++ " (" ++ intercalate ", " spec.exports ++ ") where",
        ""
      ]
        ++ spec.fixedImports
        ++ aliasImports
        ++ [""]
        ++ concatMap renderBinding allBindings

renderBinding :: TopBinding -> [String]
renderBinding (TopBinding name signature body) =
  maybe [] (\sig -> [name ++ " :: " ++ sig]) signature
    ++ [name ++ " =", "  " ++ renderCode body, ""]

pathFromModule :: String -> FilePath
pathFromModule name = map toSep name ++ ".hs"
  where
    toSep '.' = '/'
    toSep c = c

-- | The import aliases the module's code mentions, deduplicated.
-- 'buildModule' re-sorts them into "YCHR.Embedded.Generate.Code.aliasTable"
-- order for the import block.
usedAliases :: [TopBinding] -> [String]
usedAliases = nub . concatMap bindingAliases
  where
    bindingAliases (TopBinding _ _ body) = aliasesOf body

aliasesOf :: Code -> [String]
aliasesOf = go
  where
    go (CName s) = [takeWhile (/= '.') s | '.' `elem` s]
    go (CApp f args) = go f ++ concatMap go args
    go (CList xs) = concatMap go xs
    go (CTuple xs) = concatMap go xs
    go (CParens x) = go x
    go _ = []
