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
    hoist,
  )
where

import Data.List (intercalate, nub)
import YCHR.Embedded.Generate.Code
import YCHR.Embedded.Generate.Instances ()
import YCHR.Embedded.Generate.ToCode (ToCode (..))
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
  { topBindingName :: String,
    -- | Written above the definition when present; used for the
    -- module's exported entry points, whose types are otherwise only
    -- visible through inference in a file nobody reads.
    topBindingSignature :: Maybe String,
    topBindingBody :: Code
  }

-- | A generated module, ready to be written.
data GeneratedModule = GeneratedModule
  { -- | Path relative to the output directory, e.g.
    -- @YCHR\/Embedded\/Generated\/StdLib.hs@.
    modulePath :: FilePath,
    moduleSource :: String
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
    "YCHR.Embedded.Generated.StdLib"
    ["stdlib"]
    "The bundled standard library, decoded by ychr-codegen."
    ["import YCHR.Internal.StdLib (StdLib (..))"]
    [ TopBinding
        { topBindingName = "stdlib",
          topBindingSignature = Just "StdLib",
          topBindingBody = body
        }
    ]
    hoisted
  where
    (body, hoisted) = hoist opts (CApp (CName "StdLib") [toCode modules])

-- | The module holding the precomputed type-checker, as
-- @typeCheckerProgram :: SessionInput@.
--
-- Only the parts that are not recomputable are emitted: the VM program
-- and the two export tables.
-- 'YCHR.Internal.Runtime.Session.mkSessionInput' rebuilds the slot phase
-- and the indexable positions from the program, exactly as the
-- compiler's own pipeline does, which keeps the generated module about
-- 1.3 MB smaller than serializing the full 'SessionInput'.
emitTypeChecker :: EmitOptions -> SessionInput -> GeneratedModule
emitTypeChecker opts (SessionInput program _ _ exportMap exportedSet) =
  buildModule
    "YCHR.Embedded.Generated.TypeCheck"
    ["typeCheckerProgram"]
    "The bundled type-checker, decoded by ychr-codegen."
    ["import YCHR.Internal.Runtime.Session (SessionInput)"]
    [ TopBinding
        { topBindingName = "typeCheckerProgram",
          topBindingSignature = Just "SessionInput",
          topBindingBody = body
        }
    ]
    hoisted
  where
    (body, hoisted) =
      hoist
        opts
        ( CApp
            (CName "Session.mkSessionInput")
            [toCode program, toCode exportMap, toCode exportedSet]
        )

-- ---------------------------------------------------------------------------
-- Hoisting
-- ---------------------------------------------------------------------------

-- | Flatten a tree into @(body, bindings)@: the expression to render in
-- place, and the bindings to render around it.
--
-- The invariant is that no binding body exceeds 'maxBindingBytes', with
-- one exception: a node whose bulk is literal cannot be split further
-- without giving the lifted literal a type, so a constructor application
-- (or tuple) holding a very long string is emitted whole.
hoist :: EmitOptions -> Code -> (Code, [TopBinding])
hoist opts root = (root', reverse bindings)
  where
    (root', _, bindings) = walk root 0 []

    walk :: Code -> Int -> [TopBinding] -> (Code, Int, [TopBinding])
    walk c n acc = case c of
      CApp f args ->
        let (f', n1, a1) = walk f n acc
            (args', n2, a2) = walkMany args n1 a1
         in check (CApp f' args') n2 a2
      CList xs ->
        let (xs', n1, a1) = walkMany xs n acc
         in if length xs' > opts.chunkSize
              || codeSize (CList xs') > opts.maxBindingBytes
              then
                let (c', n2, a2) = chunk xs' n1 a1
                 in check c' n2 a2
              else check (CList xs') n1 a1
      CTuple xs ->
        let (xs', n1, a1) = walkMany xs n acc
         in check (CTuple xs') n1 a1
      CParens x ->
        let (x', n1, a1) = walk x n acc
         in (CParens x', n1, a1)
      _ -> (c, n, acc)

    walkMany [] n acc = ([], n, acc)
    walkMany (x : xs) n acc =
      let (x', n1, a1) = walk x n acc
          (xs', n2, a2) = walkMany xs n1 a1
       in (x' : xs', n2, a2)

    -- Lift a sub-expression that is still too big. A name is already a
    -- binding, so lifting it again would only add indirection.
    check c n acc
      | codeSize c > opts.maxBindingBytes,
        not (isName c),
        not (isEmptyList c) =
          let (body, n1, acc1) = shrink c n acc
           in (CName (generatedName n1), n1 + 1, bind n1 body : acc1)
      | otherwise = (c, n, acc)

    -- \| Lifting a node does not shrink it: a constructor application of
    -- a dozen large arguments is still over budget once its binding is
    -- written. Give its structured arguments bindings of their own, so
    -- that what remains is a head and a dozen names. Literal leaves are
    -- deliberately left in place — a top-level binding holding a bare
    -- literal would be ambiguous under the monomorphism restriction.
    shrink (CApp f args) n acc =
      let (revArgs, n', acc') = foldl liftArg ([], n, acc) args
       in (CApp f (reverse revArgs), n', acc')
    shrink c n acc = (c, n, acc)

    liftArg (rev, n, acc) arg
      | hoistable arg = (CName (generatedName n) : rev, n + 1, bind n arg : acc)
      | otherwise = (arg : rev, n, acc)

    hoistable (CApp _ _) = True
    hoistable (CList []) = False
    hoistable (CList _) = True
    hoistable (CTuple _) = True
    hoistable _ = False

    chunk xs n acc =
      let groups = chunkBySize opts xs
          (vars, n', acc') = bindEach (map CList groups) n acc
       in ( concatLists vars,
            n',
            acc'
          )

    bindEach [] n acc = ([], n, acc)
    bindEach (c : cs) n acc =
      let (vars, n', acc') = bindEach cs (n + 1) (bind n c : acc)
       in (CName (generatedName n) : vars, n', acc')

    bind n c = TopBinding (generatedName n) Nothing c

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

-- | Assemble a module from its exported entry points and the bindings
-- the hoisting pass produced. Imports are derived from the aliases the
-- code actually mentions.
buildModule ::
  String ->
  [String] ->
  String ->
  [String] ->
  [TopBinding] ->
  [TopBinding] ->
  GeneratedModule
buildModule name exports prologue fixedImports entries hoisted =
  GeneratedModule
    { modulePath = pathFromModule name,
      moduleSource = unlines source
    }
  where
    allBindings = entries ++ hoisted
    aliases = usedAliases allBindings
    aliasImports =
      [ "import qualified " ++ m ++ " as " ++ a
      | (m, a) <- aliasTable,
        a `elem` aliases
      ]
    source =
      [ "{-# LANGUAGE OverloadedStrings #-}",
        "",
        "-- | " ++ prologue,
        "--",
        "-- Machine-generated by ychr-codegen; do not edit by hand.",
        "-- Regenerate with `make resources` (see dev-docs/MICROHS_PERFORMANCE.md).",
        "module " ++ name ++ " (" ++ intercalate ", " exports ++ ") where",
        ""
      ]
        ++ fixedImports
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
