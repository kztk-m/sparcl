module Language.Sparcl.Class where

import Language.Sparcl.Core.Syntax
import Language.Sparcl.Value

class Monad m => HasTypeTable m where
  getTypeTable   :: m TypeTable
  localTypeTable :: (TypeTable -> TypeTable) -> m r -> m r 

class HasTypeTable m => ModifyTypeTable m where
  modifyTypeTable :: (TypeTable -> TypeTable) -> m () 

class Monad m => HasOpTable m where
  getOpTable   :: m OpTable
  localOpTable :: (OpTable -> OpTable) -> m r -> m r

class HasOpTable m => ModifyOpTable m where
  modifyOpTable :: (OpTable -> OpTable) -> m () 

class Monad m => HasSynTable m where
  getSynTable   :: m SynTable
  localSynTable :: (SynTable -> SynTable) -> m r -> m r 

class HasSynTable m => ModifySynTable m where
  modifySynTable :: (SynTable -> SynTable) -> m () 

class Monad m => HasDefinedNames m where
  getDefinedNames :: m [QName]
  localDefinedNames :: ([QName] -> [QName]) -> m r -> m r 

class HasDefinedNames m => ModifyDefinedNames m where
  modifyDefinedNames :: ([QName] -> [QName]) -> m () 

class Monad m => HasValueTable m where
  getValueTable :: m ValueTable
  localValueTable :: (ValueTable -> ValueTable) -> m r -> m r 

class HasValueTable m => ModifyValueTable m where
  modifyValueTable :: (ValueTable -> ValueTable) -> m ()

class Monad m => HasSearchPath m where
  getSearchPath :: m [FilePath]
  localSearchPath :: ([FilePath] -> [FilePath]) -> m r -> m r 
