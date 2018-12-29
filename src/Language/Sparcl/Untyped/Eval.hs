{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE RecursiveDo #-}

module Language.Sparcl.Untyped.Eval where

import Language.Sparcl.Untyped.Desugar

import Language.Sparcl.Name 
import Language.Sparcl.Literal
import Language.Sparcl.SrcLoc

import qualified Data.Map as M
import Data.Map (Map)

import Control.Monad.Except 
import Control.Monad.State

type Env = Map QName Value

type Eval = StateT Int (Either String) 
type Addr = Int 

newAddr :: Eval Addr
newAddr = do
  i <- get
  put $! i + 1
  return i

type Heap = Map Int Value 

lookupHeap :: Addr -> Heap -> Eval Value 
lookupHeap n heap = case M.lookup n heap of
  Nothing -> throwError "Undefined addr"
  Just v  -> return v

extendHeap :: Addr -> Value -> Heap -> Heap
extendHeap = M.insert 

unionHeap :: Heap -> Heap -> Heap
unionHeap = M.union

emptyHeap :: Heap
emptyHeap = M.empty 

removeHeap :: Addr -> Heap -> Heap
removeHeap x h = M.delete x h

removesHeap :: [Addr] -> Heap -> Heap
removesHeap xs h = foldl (\h x -> removeHeap x h) h xs 

singletonHeap :: Addr -> Value -> Heap 
singletonHeap = M.singleton 

lookupEnv :: QName -> Env -> Eval Value
lookupEnv n env = case M.lookup n env of
  Nothing -> throwError $ "Undefined value: " ++ show n 
    -- -- if nothing, we treat the variable were reversible one. 
    -- return $ VRes (lookupEnvR n) (return . singletonEnv n)
  Just v  -> return v

singletonEnv :: QName -> Value -> Env
singletonEnv = M.singleton 

extendEnv :: QName -> Value -> Env -> Env
extendEnv q v env = M.insert q v env 

unionEnv :: Env -> Env -> Env
unionEnv env1 env2 = M.union env1 env2 

emptyEnv :: Env
emptyEnv = M.empty 

-- lookupEnvR :: QName -> Env -> Eval Value
-- lookupEnvR n env = case M.lookup n env of
--   Nothing -> throwError $ "Undefined value: " ++ show n
--   Just  v -> return v 
  
                    
data Value = VCon QName [Value]
           | VBang Value
           | VLit Literal
           | VFun (Value -> Eval Value) 
           | VLift Value Value
           | VRes (Heap -> Eval Value) (Value -> Eval Heap) 

evalU :: Env -> LExp -> Eval Value
evalU env (Loc _loc exp) = case exp of
  Lit l -> return $ VLit l
  Var n ->
    lookupEnv n env
  App e1 e2 -> do
    v1 <- evalU env e1
    case v1 of
      VFun f -> do
        v2 <- evalU env e2
        f v2
      _ ->
        throwError $ "the first component of application must be a function."
  Abs n e ->
    return $ VFun (\v -> evalU (extendEnv (BName n) v env) e)

  Con q es -> do 
    VCon q <$> mapM (evalU env) es

  Bang e -> do 
    VBang <$> evalU env e

  Case e0 pes -> do
    v0 <- evalU env e0
    evalCase env v0 pes

  Lift ef eb -> do
    VFun vf <- evalU env ef
    VFun vb <- evalU env eb
    return $ VFun $ \(VRes f b) ->
                      return $ VRes (f >=> vf) (vb >=> b)

  Sig e _ ->
    evalU env e

  Let ds e -> do
    rec ev  <- mapM (evalD env') ds
        let env' = extends ev env
    evalU env' e

  RCon q es -> do 
    vs <- mapM (evalU env) es
    return $ VRes (\heap -> do 
                      us <- mapM (\v -> runFwd v heap) vs
                      return $ VCon q us)
                  (\v' ->
                     case v' of
                       VCon q' us' | q == q' && length us' == length es -> do 
                                       envs <- zipWithM (\v u -> runBwd v u) vs us'
                                       return $ foldr unionHeap emptyHeap envs
                       _ ->
                         throwError "out of the range.")
  
  RCase e0 pes -> do
    VRes f0 b0 <- evalU env e0
    pes' <- mapM (\(p,e,e') -> do
                     VFun ch <- evalU env e'
                     let ch' v = do
                           res <- ch v
                           case res of
                             VCon q [] | q == conTrue -> return True
                             _                        -> return False
                     return (p, e, ch')) pes                     
    return $ VRes (\hp -> evalCaseF env hp f0 pes')
                  (\v  -> evalCaseB env v b0 pes')


  RPin e1 e2 -> do
    VRes f1 b1 <- evalU env e1
    VFun h     <- evalU env e2
    let c = nameTuple 2 
    return $ VRes (\hp -> do
                      a <- f1 hp
                      VRes f2 _ <- h a
                      b <- f2 hp
                      return $ VCon c [a, b])
                  (\v -> case v of
                           VCon c' [a,b] | c' == c -> do 
                                             VRes _ b2 <- h a
                                             hp2 <- b2 b
                                             hp1 <- b1 a
                                             return $ unionHeap hp1 hp2
                           _ -> throwError "Expected a pair" 
                  )
                           


    
evalCase :: Env -> Value -> [ (LPat, LExp) ] -> Eval Value
evalCase _   _ [] = throwError "pattern match error"
evalCase env v ((p, e):pes) =
  case findMatch v p of
    Just binds -> evalU (extends binds env) e
    _          -> evalCase env v pes 

findMatch :: Value -> LPat -> Maybe [ (Name, Value) ]
findMatch v (unLoc -> PVar n) = return [(n,v)]
findMatch (VCon q vs) (unLoc -> PCon q' ps) | q == q' && length vs == length ps =
                                       concat <$> zipWithM findMatch vs ps
findMatch (VBang v) (unLoc -> PBang p) = findMatch v p
findMatch _ _ = Nothing 

evalCaseF :: Env -> Heap -> (Heap -> Eval Value) -> [ (LPat, LExp, Value -> Eval Bool) ] -> Eval Value
evalCaseF env hp f pes = do
  v0 <- f hp 
  go v0 [] pes
  where
    go :: Value -> [Value -> Eval Bool] -> [ (LPat, LExp, Value -> Eval Bool) ] -> Eval Value
    go _  _       [] = throwError "pattern match failure (fwd)"
    go v0 checker ((p,e,ch) : pes) =
      case findMatch v0 p of
        Nothing -> do
          go v0 (ch:checker) pes
        Just binds -> do
          as <- mapM (const newAddr) binds
          let hbinds = zipWith (\a (_, v) -> (a, v)) as binds 
          let binds' = zipWith (\a (x, _) ->
                                  (x, VRes (lookupHeap a) (return . singletonHeap a))) as binds
          VRes f _ <- evalU (extends binds' env) e
          res <- f (foldr (\(a,v) -> extendHeap a v) hp hbinds)
          checkAssert ch checker res

    checkAssert ch checker res = do
      v  <- ch res
      vs <- mapM (\c -> c res) checker
      when (v && not (or vs)) $
        throwError "Assertion failed (fwd)"        
      return res


evalCaseB :: Env -> Value -> (Value -> Eval Heap) -> [ (LPat, LExp, Value -> Eval Bool) ] -> Eval Heap
evalCaseB env vres b pes = do
  (v, hp) <- go [] pes
  hp' <- b v
  return $ unionHeap hp hp'
  where
    mkAssert :: LPat -> (Value -> Bool)
    mkAssert p = \v -> case findMatch v p of
                         Just _ -> True
                         _      -> False 
    
    go _ [] = throwError "pattern match failure (bwd)"
    go checker ((p,e,ch):pes) = do
      flg <- ch vres
      case not flg of
        False -> go (mkAssert p:checker) pes
        True -> do
          let xs = freeVarsP (unLoc p)
          as <- mapM (const newAddr) xs
          let binds' = zipWith (\x a ->
                                  (x, VRes (lookupHeap a) (return . singletonHeap a))) xs as
          VRes _ b <- evalU (extends binds' env) e
          hpBr <- b vres
          v0 <- fillPat (unLoc p) <$> zipWithM (\x a -> (x,) <$> lookupHeap a hpBr) xs as
          when (not (or $ map ($ v0) checker)) $
            throwError "Assertion failed (bwd)"
          return $ (v0, removesHeap as hpBr)
          

    freeVarsP :: Pat -> [Name]
    freeVarsP (PVar n) = [n]
    freeVarsP (PCon _ ps) = concatMap (freeVarsP . unLoc) ps
    freeVarsP (PBang p)   = freeVarsP $ unLoc p 
    
    fillPat :: Pat -> [ (Name, Value) ] -> Value
    fillPat (PVar n) bs = case lookup n bs of
      Just v -> v
      Nothing -> error "Shouldn't happen."
     
    fillPat (PCon c ps) bs =
      VCon c (map (flip fillPat bs . unLoc) ps)
    fillPat (PBang p) bs =
      VBang (fillPat (unLoc p) bs) 
          

runFwd :: Value -> Heap -> Eval Value
runFwd (VRes f _) = f
runFwd _          = \_ -> throwError "expected a reversible comp."

runBwd :: Value -> Value -> Eval Heap
runBwd (VRes _ b) = b 
runBwd _          = \_ -> throwError "expected a reversible comp." 
  
  
evalD :: Env -> LDecl -> Eval (Name, Value)
evalD = undefined


extends :: [(Name, Value)] -> Env -> Env
extends []          env = env
extends ((n,v):nvs) env = extendEnv (BName n) v (extends nvs env) 
   
      
  
  
  
