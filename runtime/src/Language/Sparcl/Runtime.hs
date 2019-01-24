{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE RankNTypes #-}

{-|
Runtime module
-}

module Language.Sparcl.Runtime (
  Rev, R, runRevIO, runRevUnsafe, Branch(..),

  -- * APIs 
  liftRev, unliftRev,
  
  pinRev, unitRev, pairRev, caseRev,
  ununitRev, unpairRev
  ) where

-- | Syntax of reversible computation in the finally-tagless style 
--   That will be compiled by using unembedding technique.

import Data.IORef
import Control.Monad (when)

import System.IO.Unsafe (unsafeInterleaveIO, unsafePerformIO)

import Data.Maybe (isJust)

newtype R a = R { runR :: IO a }
  deriving (Functor, Applicative, Monad)

runRevIO :: R a -> IO a 
runRevIO = runR

runRevUnsafe :: R a -> a 
runRevUnsafe = unsafePerformIO . runRevIO 

data Rev a = Rev (R a) (a -> R ())

data Branch a b =
  forall i. Branch (a -> R (Maybe i)) (i -> R (Maybe a)) (Rev i -> R (Rev b)) (b -> R Bool)


class Monad m => MonadRef ref m | m -> ref where
  newRef   :: m (ref a)
  readRef  :: ref a -> m a
  writeRef :: ref a -> a -> m ()

  unsafeInterleave :: m a -> m a 

instance MonadRef IORef IO where
  {-# INLINE newRef #-}
  newRef   = newIORef undefined
  {-# INLINE readRef #-}
  readRef  = readIORef
  {-# INLINE writeRef #-}
  writeRef = writeIORef 

  {-# INLINE unsafeInterleave #-}
  unsafeInterleave = unsafeInterleaveIO

instance MonadRef IORef R where
  {-# INLINE newRef #-}
  newRef = R newRef
  {-# INLINE readRef #-}
  readRef = R . readRef
  {-# INLINE writeRef #-}
  writeRef = (R .) . writeRef 

  {-# INLINE unsafeInterleave #-}
  unsafeInterleave = R . unsafeInterleave . runR 

{-# INLINABLE liftRev #-}
liftRev :: (a -> R b) -> (b -> R a) -> R (Rev a -> R (Rev b))
liftRev f g = return $ \(Rev fc bc) -> do 
  let fc' = fc >>= f
  let bc' b = g b >>= bc
  return $ Rev fc' bc'


{-# INLINABLE unliftRev #-}
unliftRev :: (Rev a -> R (Rev b)) -> R (a -> R b, b -> R a)
unliftRev f = do
  i <- newRef 
  o <- newRef 
  let r = Rev (readRef i) (writeRef o)
  Rev fc bc <- f r  
  let fwd a = 
        writeRef i a >> fc
  let bwd b = bc b >> readRef o 
  return (fwd, bwd)

{-# INLINE pinRev #-}
pinRev :: Rev a -> (a -> R (Rev b)) -> R (Rev (a, b))
pinRev (Rev fc bc) h = do
  let fc'' = do
        a <- fc
        Rev fc' _ <- h a
        b <- fc'
        return (a, b) 
  let bc'' (a, b) = do          
        Rev _ bc' <- h a 
        bc  a
        bc' b
  return $ Rev fc'' bc''

{-# INLINABLE caseRev #-}
caseRev :: Rev a -> [Branch a b] -> R (Rev b)
caseRev (Rev f0 b0) _alts = return $ Rev (goFwd _alts) (goBwd _alts)
  where
    goFwd _alts = do
      v0 <- f0
      go v0 [] _alts
        where
          go _  _    [] = error "caseRev: Pattern match failure (fwd)."
          go v0 chks (Branch fp _ k chk:alts) = do
            res <- fp v0 
            case res of
              Nothing -> go v0 (chk:chks) alts
              Just vp  -> do
                i <- newRef
                writeRef i vp
                let r = Rev (readRef i) ({- not important -} writeRef i)
                Rev mvr _ <- k r
                vr  <- mvr
                checkAssert chk chks vr

          checkAssert chk chks vr = do
            v  <- chk vr
            vs <- mapM (\ch -> ch vr) chks
            when (not v || or vs) $
              error "caseRev: Assertion failed (fwd)."
            return vr 
                
    goBwd _alts = go [] _alts
      where
        go _ [] _ = error "caseRev: Pattern match failure (bwd)."
        go pats (Branch fp bp k chk:alts) vr = do
          b <- chk vr
          if not b
            then go (toChecker fp:pats) alts vr
            else do
              o <- newRef
              Rev _ bk <- k $ Rev ({- not important -} readRef o) (writeRef o)
              bk vr
              vp <- readRef o
              res <- bp vp
              case res of
                Nothing -> error "caseRev: Guard condition failed."
                Just v0 -> allFail pats v0 >> b0 v0 

        toChecker fp v = isJust <$> fp v
            

        allFail pats v0 = do 
          rs <- mapM (\p -> p v0) pats
          when (or rs) $
            error "caseRev: Assertion failed (bwd)."

{-# INLINABLE unpairRev #-}
unpairRev :: Rev (a, b) -> (Rev a -> Rev b -> R (Rev r)) -> R (Rev r)
unpairRev (Rev fpair bpair) k = do
  ia <- newRef
  oa <- newRef
  ib <- newRef
  ob <- newRef
    
  (a, b) <- unsafeInterleave fpair
  writeRef ia a
  writeRef ib b 
  Rev fr br <- k (Rev (readRef ia) (writeRef oa)) (Rev (readRef ib) (writeRef ob))

  return $ Rev fr (\r -> do br r
                            a' <- readRef oa
                            b' <- readRef ob
                            bpair (a', b'))


{-# INLINABLE ununitRev #-}
ununitRev :: Rev () -> R (Rev r) -> R (Rev r)
ununitRev (Rev funit bunit) k = do
  Rev f b <- k
  return (Rev (funit >> f) (\r -> b r >> bunit ()))

{-# INLINABLE unitRev #-}
unitRev :: R (Rev ()) 
unitRev = do 
  i <- newRef
  o <- newRef
  writeRef i ()
  return $ Rev (readRef i) (writeRef o)

{-# INLINABLE pairRev #-}
pairRev :: Rev a -> Rev b -> R (Rev (a, b))
pairRev a b = pinRev a (const $ return b)


-- class Monad m => RevM m rev | rev -> m, m -> rev where
--     liftRev   :: (a -> m b) -> (b -> m a) -> m (rev a -> m (rev b))
--     unliftRev :: (rev a -> m (rev b)) -> m (a -> m b, b -> m a) 
--     pinRev    :: rev a -> (a -> m (rev b)) -> m (rev (a, b)) 

--     caseRev :: rev a -> [Branch m rev a b] -> m (rev b)

--     unpairRev :: rev (a, b) -> (rev a -> rev b -> m (rev r)) -> m (rev r)
--     ununitRev :: rev () -> m (rev r) -> m (rev r) 

--     unitRev :: m (rev ()) 

--     {-# INLINABLE pairRev #-}
--     pairRev   :: rev a -> rev b -> m (rev (a, b))
--     pairRev a b = pinRev a (const $ return b)



-- class Monad m => MonadRef ref m | m -> ref where
--   newRef   :: m (ref a)
--   readRef  :: ref a -> m a
--   writeRef :: ref a -> a -> m ()

--   unsafeInterleave :: m a -> m a 


-- data RevMonadRef (ref :: * -> *) m a = RevMonadRef (m a) (a -> m ())

-- instance MonadRef IORef IO where
--   newRef   = newIORef undefined
--   readRef  = readIORef
--   writeRef = writeIORef 

--   unsafeInterleave = unsafeInterleaveIO

-- instance MonadRef (STRef s) (ST s) where
--   newRef = newSTRef undefined
--   readRef = readSTRef
--   writeRef = writeSTRef 

--   unsafeInterleave = unsafeInterleaveST

-- newtype WrapMonadRef m a = WrapMonadRef { unWrapMonadRef :: m a }
--   deriving (Functor, Applicative, Monad)

-- instance MonadRef ref m => MonadRef ref (WrapMonadRef m) where
--   newRef = WrapMonadRef $ newRef
--   readRef = WrapMonadRef . readRef
--   writeRef = (WrapMonadRef .) . writeRef

--   unsafeInterleave (WrapMonadRef a) = WrapMonadRef $ unsafeInterleave a 

-- runRevIO :: (forall m rev. RevM m rev => m a) -> IO a
-- runRevIO = unWrapMonadRef

-- runRev :: (forall m rev. RevM m rev => m a) -> a
-- runRev c = runST (unWrapMonadRef c)


-- instance MonadRef ref m => RevM (WrapMonadRef m) (RevMonadRef ref (WrapMonadRef m)) where
--   liftRev f g = return $ \(RevMonadRef fc bc) -> do 
--     let fc' = fc >>= f
--     let bc' b = g b >>= bc
--     return $ RevMonadRef fc' bc'


--   unliftRev f = do
--     i <- newRef 
--     o <- newRef 
--     let r = RevMonadRef (readRef i) (writeRef o)
--     RevMonadRef fc bc <- f r  
--     let fwd a = 
--           writeRef i a >> fc
--     let bwd b = bc b >> readRef o 
--     return (fwd, bwd)
          

--   pinRev (RevMonadRef fc bc) h = do
--     let fc'' = do
--           a <- fc
--           RevMonadRef fc' _ <- h a
--           b <- fc'
--           return (a, b) 
--     let bc'' (a, b) = do          
--           RevMonadRef _ bc' <- h a 
--           bc  a
--           bc' b
--     return $ RevMonadRef fc'' bc''


--   {-# INLINABLE caseRev #-}
--   caseRev (RevMonadRef f0 b0) _alts = return $ RevMonadRef (goFwd _alts) (goBwd _alts)
--     where
--       goFwd _alts = do
--         v0 <- f0
--         go v0 [] _alts
--         where
--           go _  _    [] = error "pattern match failure"
--           go v0 chks (Branch fp _ k chk:alts) = do
--             res <- fp v0 
--             case res of
--               Nothing -> go v0 (chk:chks) alts
--               Just vp  -> do
--                 i <- newRef
--                 writeRef i vp
--                 let r = RevMonadRef (readRef i) ({- not important -} writeRef i)
--                 RevMonadRef mvr _ <- k r
--                 vr  <- mvr
--                 checkAssert chk chks vr

--           checkAssert chk chks vr = do
--             v  <- chk vr
--             vs <- mapM (\ch -> ch vr) chks
--             when (v && not (or vs)) $
--               error "Assertion failed."
--             return vr 
                
--       goBwd _alts = go [] _alts
--         where
--           go _ [] _ = error "pattern match failure"
--           go pats (Branch fp bp k chk:alts) vr = do
--             b <- chk vr
--             if not b
--               then go (toChecker fp:pats) alts vr
--               else do
--               o <- newRef
--               RevMonadRef _ bk <- k $ RevMonadRef ({- not important -} readRef o) (writeRef o)
--               bk vr
--               vp <- readRef o
--               res <- bp vp
--               case res of
--                 Nothing -> error "Guard condition failed."
--                 Just v0 -> allFail pats v0 >> b0 v0 

--           toChecker fp v = isJust <$> fp v
            

--           allFail pats v0 = do 
--             rs <- mapM (\p -> p v0) pats
--             when (or rs) $
--               error "Assertion failed."
            
              
--   {-# INLINABLE unpairRev #-}
--   unpairRev (RevMonadRef fpair bpair) k = do
--     ia <- newRef
--     oa <- newRef
--     ib <- newRef
--     ob <- newRef
    
--     (a, b) <- unsafeInterleave fpair
--     writeRef ia a
--     writeRef ib b 
--     RevMonadRef fr br <- k (RevMonadRef (readRef ia) (writeRef oa)) (RevMonadRef (readRef ib) (writeRef ob))

--     return $ RevMonadRef fr (\r -> do br r
--                                       a' <- readRef oa
--                                       b' <- readRef ob
--                                       bpair (a', b'))

--   {-# INLINABLE ununitRev #-}
--   ununitRev (RevMonadRef funit bunit) k = do
--     RevMonadRef f b <- k
--     return (RevMonadRef (funit >> f) (\r -> b r >> bunit ()))
      
--   {-# INLINABLE unitRev #-}
--   unitRev = do 
--     i <- newRef
--     o <- newRef
--     writeRef i ()
--     return $ RevMonadRef (readRef i) (writeRef o)
