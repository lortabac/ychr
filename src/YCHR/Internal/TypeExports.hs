-- | Which types and data constructors a module exports, read off a
-- compiled program. Shared by the REPL's @:info@ and @ychr scheme-types@,
-- on top of the renamer's own 'typeExportEntry': a module with no
-- @:- module(_, [...])@ export list exports everything; @type(T\/A)@
-- exports every constructor; @type(T\/A, [C1, C2])@ exports only the
-- listed names; and a type missing from the export list exports no
-- constructors at all.
module YCHR.Internal.TypeExports
  ( TypeEntry (..),
    typeExport,
    isCtorExportedByParent,
  )
where

import YCHR.Internal.Collected (CollectedModule (..))
import YCHR.Internal.Compile.Pipeline (CompiledProgram (..))
import YCHR.Internal.Parsed qualified as Parsed
import YCHR.Internal.Rename (TypeEntry (..), typeExportEntry, typeKey)
import YCHR.Internal.Types
  ( DataConstructor (..),
    Name (..),
    TypeDefinition (..),
    unqualifiedText,
  )

-- | The export entry of a type. A type whose module is not loaded, or
-- whose module has no export list, exports every constructor.
typeExport :: CompiledProgram -> TypeDefinition -> TypeEntry
typeExport prog td = case parentModule of
  Nothing -> AllConstructors
  Just m -> case m.exports of
    Nothing -> AllConstructors
    Just (Parsed.AnnP exports _ _) -> typeExportEntry (typeKey td) exports
  where
    parentModule = case td.name of
      Qualified m _ ->
        case [cm | cm <- prog.allModules, cm.name == m] of
          (cm : _) -> Just cm
          [] -> Nothing
      Unqualified _ -> Nothing

-- | Is the given data constructor visible through its parent type's
-- module export list? @:info@ uses this to refuse direct queries on
-- hidden constructors while still listing them inside the parent
-- type's declaration body.
isCtorExportedByParent ::
  CompiledProgram -> TypeDefinition -> DataConstructor -> Bool
isCtorExportedByParent prog td c = case typeExport prog td of
  NoTypeEntry -> False
  AllConstructors -> True
  TheseConstructors xs -> unqualifiedText c.conName `elem` xs
