{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE PolyKinds #-}
module Language.Sparcl.Class where

import Data.Typeable

import qualified Control.Monad.State as St
import qualified Control.Monad.Reader as Rd

-- Simplified version of Capability.Reader
class Monad m => Has (key :: k) a m | key m -> a where
  ask    :: Proxy key -> m a
  {-# MINIMAL ask #-}

class Has key a m => Local key a m where
  local  :: Proxy key -> (a -> a) -> m r -> m r 

  default local :: Modify key a m => Proxy key -> (a -> a) -> m r -> m r
  local proxy u m = do
    old <- ask proxy
    set proxy (u old)
    res <- m
    set proxy old
    return res 


class Local key a m => Modify key a m where
  modify :: Proxy key -> (a -> a) -> m ()
  modify proxy f = do
    a <- ask proxy
    set proxy $! f a

  set :: Proxy key -> a -> m ()
  set proxy a = modify proxy (const a) 

  {-# MINIMAL modify | set #-}

key :: forall a. Proxy a
key = Proxy

instance Has key a m => Has key a (St.StateT s m) where
  ask proxy = St.lift (ask proxy) 

instance Local key a m => Local key a (St.StateT s m) where
  local proxy f comp =
    St.StateT $ \st -> local proxy f $ St.runStateT comp st

instance Modify key a m => Modify key a (St.StateT s m) where
  modify proxy f = St.lift (modify proxy f) 

instance Has key a m => Has key a (Rd.ReaderT s m) where
  ask proxy = Rd.lift (ask proxy)

instance Local key a m => Local key a (Rd.ReaderT s m) where
  local proxy f comp =
    Rd.ReaderT $ \st -> local proxy f (Rd.runReaderT comp st)

instance Modify key a m => Modify key a (Rd.ReaderT s m) where
  modify proxy f = Rd.lift (modify proxy f)
  


-- class Monad m => HasTypeTable m where
--   getTypeTable   :: m TypeTable
--   localTypeTable :: (TypeTable -> TypeTable) -> m r -> m r 

-- class HasTypeTable m => ModifyTypeTable m where
--   modifyTypeTable :: (TypeTable -> TypeTable) -> m () 

-- class Monad m => HasOpTable m where
--   getOpTable   :: m OpTable
--   localOpTable :: (OpTable -> OpTable) -> m r -> m r

-- class HasOpTable m => ModifyOpTable m where
--   modifyOpTable :: (OpTable -> OpTable) -> m () 

-- class Monad m => HasSynTable m where
--   getSynTable   :: m SynTable
--   localSynTable :: (SynTable -> SynTable) -> m r -> m r 

-- class HasSynTable m => ModifySynTable m where
--   modifySynTable :: (SynTable -> SynTable) -> m () 

-- class Monad m => HasNameTable m where
--   getNameTable :: m NameTable
--   localNameTable :: (NameTable -> NameTable) -> m r -> m r 

-- class HasNameTable m => ModifyNameTable m where
--   modifyDefinedNames :: ([Name] -> [Name]) -> m () 

-- class Monad m => HasValueTable m where
--   getValueTable :: m ValueTable
--   localValueTable :: (ValueTable -> ValueTable) -> m r -> m r 

-- class HasValueTable m => ModifyValueTable m where
--   modifyValueTable :: (ValueTable -> ValueTable) -> m ()

-- class Monad m => HasSearchPath m where
--   getSearchPath :: m [FilePath]
--   localSearchPath :: ([FilePath] -> [FilePath]) -> m r -> m r 
