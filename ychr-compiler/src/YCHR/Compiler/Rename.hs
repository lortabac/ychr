module YCHR.Compiler.Rename (qualifyModuleNames) where

import Data.List (find)
import Data.Maybe (mapMaybe)
import Data.Text (Text)
import YCHR.Types.Common
import YCHR.Types.Parsed
import YCHR.Types.Renamed

data RenamerError
  = NameNotFound Text
  | AmbiguousName Text
  | QualifiedNameNotFound Text Text
  deriving (Eq, Show)

qualifyModuleNames :: PsModule -> Either RenamerError RnModule
qualifyModuleNames mdl = sequenceA $ fmap qualify mdl
  where
    qualify (PsName ident) = case findConstraintDefByName mdl ident of
      Just _ -> Right $ QualifiedName (moduleName mdl) ident
      Nothing -> case listNameInImports ident (imports mdl) of
        [ModuleName modName] -> Right $ QualifiedName modName ident
        (_ : _) -> Left $ AmbiguousName ident
        [] -> Left $ NameNotFound ident
    qualify (PsQualifiedName modName ident) =
      case findImportByModuleName mdl modName of
        Just imp -> case listNameInImport ident imp of
          Just (ModuleName _) -> Right $ QualifiedName modName ident
          Nothing -> Left $ QualifiedNameNotFound modName ident
        Nothing -> Left $ QualifiedNameNotFound modName ident

findConstraintDefByName :: Module var name -> Text -> Maybe ConstraintDef
findConstraintDefByName mdl ident =
  find (\constr -> functor constr == ident) (constraints mdl)

findImportByModuleName :: Module var name -> Text -> Maybe Import
findImportByModuleName mdl modName =
  find (\imp -> getModuleName (importedModule imp) == modName) (imports mdl)

listNameInImports :: Text -> [Import] -> [ModuleName]
listNameInImports ident = mapMaybe (listNameInImport ident)

listNameInImport :: Text -> Import -> Maybe ModuleName
listNameInImport ident (Import modName defs) =
  if ident `elem` defs
    then Just modName
    else Nothing
