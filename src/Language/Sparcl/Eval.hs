{-# LANGUAGE RecursiveDo #-}

module Language.Sparcl.Eval where

import           Language.Sparcl.Core.Syntax
import           Language.Sparcl.Exception
import           Language.Sparcl.Value

import           Control.Monad               ((>=>), unless, zipWithM)
import           Control.Monad.Except
import           Data.Maybe                  (fromMaybe)
-- import Control.Monad.State

-- import qualified Control.Monad.Fail as Fail

-- import Control.Monad.State

-- import qualified Control.Monad.Fail as Fail
import           Control.Monad.Reader        (MonadReader (local), ask)
-- import           Debug.Trace                 (trace)
import           Language.Sparcl.Pretty      hiding ((<$>))

-- lookupEnvR :: QName -> Env -> Eval Value
-- lookupEnvR n env = case M.lookup n env of
--   Nothing -> throwError $ "Undefined value: " ++ show n
--   Just  v -> return v


evalUBind :: Env -> Bind Name -> Eval Env
evalUBind env ds = do
    rec ev  <- mapM (\(n,_,e) -> do
                        v <- evalU env' e
                        return (n,v)) ds
        let env' = extendsEnv ev env
    return env'

evalU :: Env -> Exp Name -> Eval Value
evalU env expr = case expr of
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
        rtError $ text "the first component of application must be a function, but we got " <> ppr v1 <> text " from " <> ppr e1
  Abs n e ->
    return $ VFun (\v -> evalU (extendEnv n v env) e)

  Con q es ->
    VCon q <$> mapM (evalU env) es

  Case e0 pes -> do
    v0 <- evalU env e0
    evalCase env v0 pes

  Lift ef eb -> do
    VFun vf <- evalU env ef
    VFun vb <- evalU env eb
    return $ VFun $ \(VRes f b) -> return $ VRes (f >=> vf) (vb >=> b)
    -- VBang (VFun vf) <- evalU env ef
    -- VBang (VFun vb) <- evalU env eb
    -- let vf' = vf . VBang
    -- let vb' = vb . VBang
    -- return $ VBang $ VFun $ \(VRes f b) ->
    --                           return $ VRes (f >=> vf') (vb' >=> b)

  Let ds e -> do
    env' <- evalUBind env ds
    evalU env' e

  Unlift e -> do
    -- VBang (VFun f) <- evalU env e
    VFun f <- evalU env e
    newAddr $ \a -> do
      VRes f0 b0 <- f (VRes (lookupHeap a)
                            (return . singletonHeap a))
      let f0' v = f0 (singletonHeap a v)
      let b0' v = do hp <- b0 v
                     lookupHeap a hp
      -- let f0' (VBang v) = f0 (singletonHeap a v)
      --     f0' _         = error "expecting !"
      -- let b0' (VBang v) = do hp <- b0 v
      --                        lookupHeap a hp
      --     b0' _         = error "expecting !"
      let c = nameTuple 2
      -- return $ VCon c [VBang (VFun f0'), VBang (VFun b0')]
      return $ VCon c [VFun f0', VFun b0']


  RCon q es -> do
    vs <- mapM (evalU env) es
    return $ VRes (\heap -> do
                      us <- mapM (\v -> runFwd v heap) vs
                      return $ VCon q us)
                  (\v' ->
                     case v' of
                       VCon q' us' | q == q' && length us' == length es -> do
                                       envs <- zipWithM runBwd vs us'
                                       return $ foldr unionHeap emptyHeap envs
                       _ ->
                         rtError $ text "out of the range:" <+> ppr v' <+> text "for" <+> ppr expr)

  RCase e0 pes -> do
    VRes f0 b0 <- evalU env e0
    pes' <- mapM (\(p,e,e') -> do
                     -- VBang (VFun ch) <- evalU env e'
                     VFun ch <- evalU env e'
                     let ch' v = do
                           res <- ch v
                           case res of
                             VCon q [] | q == conTrue -> return True
                             _                        -> return False
                     return (p, e, ch')) pes
    lvl <- ask
    return $ VRes (\hp -> local (const lvl) $ evalCaseF env hp f0 pes')
                  (\v  -> local (const lvl) $ evalCaseB env v b0 pes')


  RPin e1 e2 -> do
    VRes f1 b1 <- evalU env e1
    VFun h     <- evalU env e2
    let c = nameTuple 2
    return $ VRes (\hp -> do
                      a <- f1 hp
                      VRes f2 _ <- h a -- (VBang a)
                      b <- f2 hp
                      return $ VCon c [a, b])
                  (\case
                      VCon c' [a,b] | c' == c -> do
                                        VRes _ b2 <- h a -- (VBang a)
                                        hp2 <- b2 b
                                        hp1 <- b1 a
                                        return $ unionHeap hp1 hp2
                      _ -> rtError $ text "Expected a pair"
                  )




evalCase :: Env -> Value -> [ (Pat Name, Exp Name) ] -> Eval Value
evalCase _   v [] = rtError $ text "pattern match error" <+> ppr v
evalCase env v ((p, e):pes) =
  case findMatch v p of
    Just binds -> evalU (extendsEnv binds env) e
    _          -> evalCase env v pes

findMatch :: Value -> Pat Name -> Maybe [ (Name, Value) ]
findMatch v (PVar n) = return [(n, v)]
findMatch (VCon q vs) (PCon q' ps) | q == q' && length vs == length ps =
                                       concat <$> zipWithM findMatch vs ps
findMatch _ _ = Nothing

evalCaseF :: Env -> Heap -> (Heap -> Eval Value) -> [ (Pat Name, Exp Name, Value -> Eval Bool) ] -> Eval Value
evalCaseF env hp f0 alts = do
  v0 <- f0 hp
  go v0 [] alts
  where
    go :: Value -> [Value -> Eval Bool] -> [ (Pat Name, Exp Name, Value -> Eval Bool) ] -> Eval Value
    go v0  _       [] = rtError $ text $ "pattern match failure (fwd): " ++ prettyShow v0
    go v0 checker ((p,e,ch) : pes) =
      case findMatch v0 p of
        Nothing ->
          go v0 (ch:checker) pes
        Just binds ->
          newAddrs (length binds) $ \as -> do
             let hbinds = zipWith (\a (_, v) -> (a, v)) as binds
             let binds' = zipWith (\a (x, _) ->
                                     (x, VRes (lookupHeap a) (return . singletonHeap a))) as binds
             VRes f _ <- evalU (extendsEnv binds' env) e
             res <- f (foldr (uncurry extendHeap) hp hbinds)
             checkAssert ch checker res

    checkAssert :: (Value -> Eval Bool) -> [Value -> Eval Bool] -> Value -> Eval Value
    checkAssert ch checker res = do
      -- v  <- ch (VBang res)
      -- vs <- mapM (\c -> c (VBang res)) checker
      v <- ch res
      vs <- mapM (\c -> c res) checker
      () <- unless (v && not (or vs)) $
               rtError (text "Assertion failed (fwd)")
      return res


evalCaseB :: Env -> Value -> (Value -> Eval Heap) -> [ (Pat Name, Exp Name, Value -> Eval Bool) ] -> Eval Heap
evalCaseB env vres b0 alts = do
  (v, hp) <- go [] alts
  hp' <- {- trace (show $ text "hp = " <> pprHeap hp <> comma <+> text "v = " <> ppr v) $ -} b0 v
  return $ unionHeap hp hp'
  where
    mkAssert :: Pat Name -> Value -> Bool
    mkAssert p v = case findMatch v p of
                     Just _ -> True
                     _      -> False

    go _ [] = rtError $ text "pattern match failure (bwd)"
    go checker ((p,e,ch):pes) = do
      -- flg <- ch (VBang vres)
      flg <- ch vres
      if flg
        then do
          let xs = freeVarsP p
          newAddrs (length xs) $ \as -> do
            let binds' = zipWith (\x a ->
                                    (x, VRes (lookupHeap a) (return . singletonHeap a))) xs as
            VRes _ b <- {- trace ("Evaluating bodies") $ -} evalU (extendsEnv binds' env) e
            hpBr <- {- trace ("vres = " ++ show (ppr vres)) $ -} b vres
            v0 <- {- trace ("hpBr = " ++ show (pprHeap hpBr)) $ -} fillPat p <$> zipWithM (\x a -> (x,) <$> lookupHeap a hpBr) xs as
            unless (any ($ v0) checker) $
              rtError $ text "Assertion failed (bwd)"
            return (v0, removesHeap as hpBr)
        else go (mkAssert p:checker) pes

    fillPat :: Pat Name -> [ (Name, Value) ] -> Value
    fillPat (PVar n) bs =
      fromMaybe (error "Shouldn't happen") (lookup n bs)

    fillPat (PCon c ps) bs =
      VCon c (map (flip fillPat bs) ps)


runFwd :: Value -> Heap -> Eval Value
runFwd (VRes f _) = f
runFwd _          = \_ -> rtError $ text "expected a reversible comp."

runBwd :: Value -> Value -> Eval Heap
runBwd (VRes _ b) = b
runBwd _          = \_ -> rtError $ text "expected a reversible comp."


