module Language.Sparcl.Typing.TC where

-- Type checking monad
-- Here, we use int values for meta variables
import Language.Sparcl.Untyped.Desugar.Syntax


import qualified Data.IntMap as IM
import qualified Data.Map as M

import Data.Maybe (fromMaybe)

import Control.Monad.State 
import Control.Monad.Except 

import qualified Text.PrettyPrint.ANSI.Leijen as D
import Language.Sparcl.Pretty 

class (MonadError D.Doc m, Monad m) => MonadTypeCheck m where
  typeError :: D.Doc -> m a
  askType :: SrcSpan -> QName -> m Ty

  readTyVar :: MetaTyVar -> m (Maybe Ty)
  writeTyVar :: MetaTyVar -> Ty -> m ()
  
  resolveSyn :: Ty -> m Ty 

  withLVar :: Name -> Ty -> m r -> m r
  withUVar :: Name -> Ty -> m r -> m r

  -- typing under empty linear environment 
  withoutLinear :: m () -> m () 

  newMetaTyVar :: SrcSpan -> m MetaTyVar

  getMetaTyVarsInEnv :: m [MetaTyVar] 

  newSkolemTyVar :: TyVar -> m TyVar 

data Multiplicity = Omega | One | Zero 

type TyEnv = M.Map QName (Multiplicity, Ty)

-- Instead of the reader monad, we use the state monad to
-- handle linearity. 
data TInfo
  = TInfo { tiTyEnv   :: TyEnv, 
            tiMvCount :: !Int,
            tiMap     :: IM.IntMap Ty,
            tiSyn     :: M.Map QName ([TyVar],  Ty), 
            tiSvCount :: !Int 
          }    

-- newtype TC a = TC { unTC :: StateT TInfo (Either D.Doc) a }
newtype TC a = TC { unTC :: ExceptT D.Doc (State TInfo) a }
  deriving (Functor, Applicative, Monad, MonadState TInfo, MonadError D.Doc) 

runTC :: TInfo -> TC a -> (Either D.Doc a, TInfo) 
runTC tinfo (TC m) = runState (runExceptT m) tinfo 

freeTyVars :: MonadTypeCheck m => [Ty] -> m [TyVar]
freeTyVars ts = do
  ts' <- mapM zonkType ts
  return $ go ts' []
    where
      go []     r = r
      go (t:ts) r = goT [] t (go ts r)

      goT bound (TyVar t) r
        | t `elem` bound = r
        | t `elem` r     = r
        | otherwise      = t : r
      goT bound (TyCon _ ts) r =
        foldr (goT bound) r ts
      goT bound (TyForAll bs t) r = goT (bs ++ bound) t r
      goT _bound (TyMetaV _) r = r
      goT bound (TySyn ty _) r = goT bound ty r 

initTInfo :: M.Map QName Ty -> M.Map QName ([TyVar], Ty) -> TInfo
initTInfo tenv syn = 
  TInfo { tiTyEnv   = M.map (\t -> (Omega, t)) tenv,
          tiMvCount = 0,
          tiMap     = IM.empty,
          tiSyn     = syn,
          tiSvCount = 0 } 

getTyEnv :: TC TyEnv
getTyEnv = gets tiTyEnv

putTyEnv :: TyEnv -> TC ()
putTyEnv tyEnv = do
  ti <- get
  put $ ti { tiTyEnv = tyEnv }

lookupTyEnv :: SrcSpan -> QName -> TyEnv -> TC (Ty, TyEnv)
lookupTyEnv l n tyEnv =
  case M.lookup n tyEnv of
    Just (Omega, ty) -> return (ty, tyEnv)
    Just (One,   ty) -> return (ty, M.insert n (Zero, ty) tyEnv)
    Just (Zero,  _ ) ->
      typeError $ ppr l D.<> D.nest 2 (D.line D.<> D.hsep [D.dquotes (ppr n), D.text "is used more than once."])
    _ ->
      typeError $ ppr l D.<> D.nest 2 (D.line D.<> D.dquotes (ppr n) D.<+> D.text "is undefined.")

findTy :: MetaTyVar -> IM.IntMap Ty -> (Maybe Ty, IM.IntMap Ty)
findTy (MetaTyVar i _) map =
  case IM.lookup i map of
    Just (TyMetaV mv) ->
      let (res, map') = findTy mv map
      in case res of
           Just ty -> (Just ty, IM.insert i ty map')
           _       -> (Nothing, map') 
    res -> (res, map)

metaTyVars :: [Ty] -> [MetaTyVar]
metaTyVars xs = go xs []
  where
    go [] = id 
    go (t:ts) = goTy t . go ts

    goTy (TyCon _ ts) = go ts
    goTy (TyForAll _ t) = goTy t
    goTy (TySyn _ t)    = goTy t
    goTy (TyMetaV m)    = (m:) 
    goTy _              = id 

instance MonadTypeCheck TC where
  typeError = throwError

  askType l n
    | Just k <- checkNameTuple n = do 
        let tvs = map (BoundTv . NormalName) [ 't':show i | i <- [1..k] ]
        let tys = map TyVar tvs
        return $ TyForAll tvs $ foldr (-@) (tupleTy tys) tys        
    | otherwise = do                       
        ti <- get
        let tyEnv = tiTyEnv ti
        (ty, tyEnv') <- lookupTyEnv l n tyEnv
        put (ti { tiTyEnv = tyEnv' })
        return ty

  readTyVar mv = do
    ti <- get
    let tm = tiMap ti
    let (res, tm') = findTy mv tm 
    put (ti { tiMap = tm' })
    return res

  writeTyVar (MetaTyVar i _) ty = do
    ti <- get
    let tm  = tiMap ti
    let tm' = IM.insert i ty tm
    put (ti { tiMap = tm'})


  withLVar x ty m = do
    tyEnv  <- getTyEnv
    let origX = M.lookup (BName x) tyEnv 
    putTyEnv $ M.insert (BName x) (One, ty) tyEnv 
    ret <- m
    tyEnvAfter <- getTyEnv 
    case M.lookup (BName x) tyEnvAfter of
      Just (Zero, _) ->
        case origX of
          Just ent -> do 
            putTyEnv $ M.insert (BName x) ent tyEnvAfter -- restore the original if any
            return ret 
          Nothing -> do 
            putTyEnv $ M.delete (BName x) tyEnvAfter
            return ret 
      _ -> do
        typeError $ D.text "Linear type variable" D.<+> D.dquotes (ppr x) D.<+> D.text "is not used linearly."
    
  withUVar x ty m = do
    tyEnv <- getTyEnv
    let origX = M.lookup (BName x) tyEnv
    putTyEnv $ M.insert (BName x) (Omega, ty) tyEnv 
    ret <- m
    tyEnvAfter <- getTyEnv
    case origX of
      Nothing -> do 
        putTyEnv $ M.delete (BName x) tyEnvAfter
        return ret 
      Just ent -> do 
        putTyEnv $ M.insert (BName x) ent tyEnvAfter
        return ret 

  withoutLinear m = do
    tyEnv <- getTyEnv 
    let (tyLEnv, tyUEnv) = M.partition isLinearEntry $ tyEnv 
    putTyEnv $ tyUEnv
    m
    tyEnvAfter <- getTyEnv 
    putTyEnv $ M.union tyLEnv tyEnvAfter
    where
      isLinearEntry (One, _) = True
      isLinearEntry _        = False 
    

  newMetaTyVar l = do
    ti <- get
    let sz = tiMvCount ti
    put $! ti { tiMvCount = sz + 1 }
    return $ MetaTyVar sz l

  resolveSyn ty = do
    synMap <- gets tiSyn
    go synMap ty 
    where
      go _synMap (TyVar x) = return (TyVar x)
      go synMap (TyForAll ns t) =
        TyForAll ns <$> go synMap t
      go _synMap (TyMetaV m) = return (TyMetaV m)      
      go synMap (TySyn origTy ty) =
        TySyn origTy <$> go synMap ty
      go synMap orig@(TyCon c ts) = do
        case M.lookup c synMap of
          Nothing ->
            TyCon c <$> mapM (go synMap) ts 
          Just (ns, ty)
            | length ns == length ts -> 
              TySyn orig <$> go synMap (substTy (zip ns ts) ty)
          Just _ ->
              typeError $ D.hsep [ D.text "Type synonym", D.dquotes (ppr c), D.text "must be fully-applied." ] 

  getMetaTyVarsInEnv = do
    tyEnv <- getTyEnv
    let ts = map snd $ M.elems tyEnv
    return $ metaTyVars ts 

  newSkolemTyVar ty = do
    ti <- get
    let cnt = tiSvCount ti
    put $ ti { tiSvCount = cnt + 1 }
    return $ SkolemTv ty cnt 

withLVars :: MonadTypeCheck m => [ (Name, Ty) ] -> m r -> m r
withLVars ns m = foldr (uncurry withLVar) m ns

withUVars :: MonadTypeCheck m => [ (Name, Ty) ] -> m r -> m r
withUVars ns m = foldr (uncurry withUVar) m ns 

newMetaTy :: MonadTypeCheck m => SrcSpan -> m Ty
newMetaTy = fmap TyMetaV . newMetaTyVar 

substTy :: [ (TyVar, Ty) ] -> Ty -> Ty
substTy tbl ty = case ty of
  TyVar n -> fromMaybe ty (Prelude.lookup n tbl)
  TyCon c ts ->
    TyCon c $ map (substTy tbl) ts
  TyMetaV m -> TyMetaV m
  TyForAll ns t ->
    let tbl' = filter (not . (`elem` ns) . fst) tbl
    in TyForAll ns $ substTy tbl' t 
  TySyn origTy uTy -> TySyn (substTy tbl origTy) (substTy tbl uTy)
    

  
   

zonkMetaTyVar :: MonadTypeCheck m => MetaTyVar -> m Ty
zonkMetaTyVar mv = do 
  res <- readTyVar mv 
  case res of
    Nothing -> return (TyMetaV mv) 
    Just ty -> return ty

zonkType :: MonadTypeCheck m => Ty -> m Ty
zonkType (TyVar n) = return $ TyVar n
zonkType (TyCon c ts) =
  TyCon c <$> mapM zonkType ts
zonkType (TyForAll ns t) =
  TyForAll ns <$> zonkType t
zonkType (TyMetaV m) = zonkMetaTyVar m
zonkType (TySyn origTy ty) =
  TySyn <$> zonkType origTy <*> zonkType ty 


unify :: MonadTypeCheck m => MonoTy -> MonoTy -> m ()
unify ty1 ty2 = do
  ty1' <- resolveSyn ty1
  ty2' <- resolveSyn ty2
  unifyWork ty1' ty2'

unifyWork :: MonadTypeCheck m => MonoTy -> MonoTy -> m ()
unifyWork (TySyn _ t1) t2 = unifyWork t1 t2
unifyWork t1 (TySyn _ t2) = unifyWork t1 t2
unifyWork (TyVar x1) (TyVar x2)       | x1 == x2 = return ()
unifyWork (TyMetaV mv1) (TyMetaV mv2) | mv1 == mv2 = return ()
unifyWork (TyMetaV mv) ty = unifyMetaTyVar mv ty
unifyWork ty (TyMetaV mv) = unifyMetaTyVar mv ty
unifyWork (TyCon c ts) (TyCon c' ts') | c == c' = do 
                                          when (length ts /= length ts') $
                                            typeError $ D.hsep [D.text "Type construtor", ppr c, D.text "has different numbesr of arguments."]
                                          zipWithM_ unifyWork ts ts' 
unifyWork ty1 ty2 = do
  ty1' <- zonkType ty1
  ty2' <- zonkType ty2
  typeError $ D.nest 2 $
    D.text "Types do not match:" D.<$>
    D.group (D.align (D.dquotes (ppr ty1') D.<+> D.text "vs."
                       D.<$> D.dquotes (ppr ty2')))

unifyMetaTyVar :: MonadTypeCheck m => MetaTyVar -> MonoTy -> m () 
unifyMetaTyVar mv ty2 = do 
  res <- readTyVar mv
  case res of
    Just ty -> unify ty ty2
    Nothing ->
      unifyUnboundMetaTyVar mv ty2 

unifyUnboundMetaTyVar :: MonadTypeCheck m => MetaTyVar -> MonoTy -> m ()
unifyUnboundMetaTyVar mv (TyMetaV mv2) = do 
  res <- readTyVar mv2
  case res of
    Nothing   -> writeTyVar mv (TyMetaV mv2) 
    Just ty2' -> unifyUnboundMetaTyVar mv ty2' 
unifyUnboundMetaTyVar mv ty2 = do 
  ty2' <- zonkType ty2
  let mvs = metaTyVars [ty2']
  case mv `elem` mvs of
    True  -> typeError $ D.text "Occurrence check failed:" D.<+> D.sep [ppr mv, D.text " appears in ", ppr ty2']
    False -> writeTyVar mv ty2'

        
   
  

  


    

  
