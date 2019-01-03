{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE RecursiveDo #-}

module Language.Sparcl.Eval where

import Language.Sparcl.Core.Syntax
import Language.Sparcl.Value
import Language.Sparcl.Exception

import Control.Monad.Except 
-- import Control.Monad.State

-- import qualified Control.Monad.Fail as Fail

import Language.Sparcl.Pretty 
import qualified Text.PrettyPrint.ANSI.Leijen as D


-- lookupEnvR :: QName -> Env -> Eval Value
-- lookupEnvR n env = case M.lookup n env of
--   Nothing -> throwError $ "Undefined value: " ++ show n
--   Just  v -> return v 
  
                    
evalUDecls :: Env -> [LDecl] -> Eval Env
evalUDecls env ds = do
    rec ev  <- mapM (evalD env') ds
        let env' = extendsEnv ev env
    return env' 

evalU :: Env -> OLExp -> Eval Value
evalU env (desugared -> Loc _loc exp) = case exp of
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
        rtError $ D.text "the first component of application must be a function."
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
    VBang (VFun vf) <- evalU env ef
    VBang (VFun vb) <- evalU env eb
    let vf' = vf . VBang
    let vb' = vb . VBang 
    return $ VBang $ VFun $ \(VRes f b) ->
                              return $ VRes (f >=> vf') (vb' >=> b)

  Sig e _ ->
    evalU env e

  Let ds e -> do
    env' <- evalUDecls env ds 
    evalU env' e

  Unlift e -> do
    VBang (VFun f) <- evalU env e
    newAddr $ \a -> do
      VRes f0 b0 <- f (VRes (\hp -> lookupHeap a hp)
                        (\v  -> return $ singletonHeap a v))
      let f0' (VBang v) = f0 (singletonHeap a v)
          f0' _         = error "expecting !"
      let b0' (VBang v) = do hp <- b0 v
                             lookupHeap a hp
          b0' _         = error "expecting !"
      let c = nameTuple 2
      return $ VCon c [VBang (VFun f0'), VBang (VFun b0')] 
  

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
                         rtError $ D.text "out of the range:" D.<+> ppr v' D.<+> D.text "for" D.<+> ppr exp)
  
  RCase e0 pes -> do
    VRes f0 b0 <- evalU env e0
    pes' <- mapM (\(p,e,e') -> do
                     VBang (VFun ch) <- evalU env e'
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
                           _ -> rtError $ D.text "Expected a pair" 
                  )
                           


    
evalCase :: Env -> Value -> [ (LPat, OLExp) ] -> Eval Value
evalCase _   _ [] = rtError $ D.text "pattern match error"
evalCase env v ((p, e):pes) =
  case findMatch v p of
    Just binds -> evalU (extendsEnv binds env) e
    _          -> evalCase env v pes 

findMatch :: Value -> LPat -> Maybe [ (QName, Value) ]
findMatch v (unLoc -> PVar n) = return [(BName n,v)]
findMatch (VCon q vs) (unLoc -> PCon q' ps) | q == q' && length vs == length ps =
                                       concat <$> zipWithM findMatch vs ps
findMatch (VBang v) (unLoc -> PBang p) = findMatch v p
findMatch _ _ = Nothing 

evalCaseF :: Env -> Heap -> (Heap -> Eval Value) -> [ (LPat, OLExp, Value -> Eval Bool) ] -> Eval Value
evalCaseF env hp f pes = do
  v0 <- f hp 
  go v0 [] pes
  where
    go :: Value -> [Value -> Eval Bool] -> [ (LPat, OLExp, Value -> Eval Bool) ] -> Eval Value
    go _  _       [] = rtError $ D.text "pattern match failure (fwd)"
    go v0 checker ((p,e,ch) : pes) =
      case findMatch v0 p of
        Nothing -> do
          go v0 (ch:checker) pes
        Just binds ->
          newAddrs (length binds) $ \as -> do 
             let hbinds = zipWith (\a (_, v) -> (a, v)) as binds 
             let binds' = zipWith (\a (x, _) ->
                                     (x, VRes (lookupHeap a) (return . singletonHeap a))) as binds
             VRes f _ <- evalU (extendsEnv binds' env) e
             res <- f (foldr (\(a,v) -> extendHeap a v) hp hbinds)
             checkAssert ch checker res

    checkAssert ch checker res = do
      v  <- ch (VBang res)
      vs <- mapM (\c -> c (VBang res)) checker
      when (v && not (or vs)) $
        rtError (D.text "Assertion failed (fwd)")
      return res


evalCaseB :: Env -> Value -> (Value -> Eval Heap) -> [ (LPat, OLExp, Value -> Eval Bool) ] -> Eval Heap
evalCaseB env vres b pes = do
  (v, hp) <- go [] pes
  hp' <- b v
  return $ unionHeap hp hp'
  where
    mkAssert :: LPat -> (Value -> Bool)
    mkAssert p = \v -> case findMatch v p of
                         Just _ -> True
                         _      -> False 
    
    go _ [] = rtError $ D.text "pattern match failure (bwd)"
    go checker ((p,e,ch):pes) = do
      flg <- ch (VBang vres) 
      case flg of
        False -> go (mkAssert p:checker) pes
        True -> do
          let xs = freeVarsP (unLoc p)
          newAddrs (length xs) $ \as -> do 
            let binds' = zipWith (\x a ->
                                    (BName x, VRes (lookupHeap a) (return . singletonHeap a))) xs as
            VRes _ b <- evalU (extendsEnv binds' env) e
            hpBr <- b vres
            v0 <- fillPat (unLoc p) <$> zipWithM (\x a -> (x,) <$> lookupHeap a hpBr) xs as
            when (not (or $ map ($ v0) checker)) $
              rtError $ D.text "Assertion failed (bwd)"
            return $ (v0, removesHeap as hpBr)
              
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
runFwd _          = \_ -> rtError $ D.text "expected a reversible comp."

runBwd :: Value -> Value -> Eval Heap
runBwd (VRes _ b) = b 
runBwd _          = \_ -> rtError $ D.text "expected a reversible comp." 
  
  
evalD :: Env -> LDecl -> Eval (QName, Value)
evalD env (unLoc -> DDef n _ e) = do
  (n,) <$> evalU env e



  
