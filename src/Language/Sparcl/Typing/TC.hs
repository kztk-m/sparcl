{-# LANGUAGE ViewPatterns #-}
module Language.Sparcl.Typing.TC where

-- Type checking monad
-- Here, we use int values for meta variables
import Language.Sparcl.Core.Syntax
import qualified Language.Sparcl.Surface.Syntax as S 

import qualified Data.Map as M

import Data.Maybe (fromMaybe)

import Control.Monad.Reader
import Control.Monad.Except 

import qualified Text.PrettyPrint.ANSI.Leijen as D
import Language.Sparcl.Pretty 

-- import Control.Arrow (first) 

import qualified Data.Sequence as Seq 
import Data.IORef

-- import Debug.Trace 

data TypeError = TypeError (Maybe SrcSpan) (Seq.Seq S.LExp) ErrorDetail

data ErrorDetail
  = UnMatchTy  Ty Ty 
  | UnMatchTyD Ty Ty Ty Ty -- inferred and expected
  | OccurrenceCheck MetaTyVar Ty
  | MultipleUse QName
  | NoUse       QName
  | Undefined   QName 
  | Other       D.Doc 
  

instance Pretty TypeError where
  ppr (TypeError l es d) =
    D.bold (D.text "[TYPE ERROR]") D.<+> D.nest 2
     (maybe (D.text "*unknown place*") ppr l 
      D.<$> pprDetail d D.<> pprContexts (Seq.drop (Seq.length es - 3) es))
    where
      pprDetail (UnMatchTy ty1 ty2) = 
        D.text "Types do not match"
        D.<+> D.align (ppr ty1) D.<+> D.text "/=" D.<+> D.align (ppr ty2)

      pprDetail (UnMatchTyD ty1 ty2 ty1' ty2') =
        D.text "Types do not match" D.<> D.nest 2 
         ( D.line D.<> D.hsep [D.text "Expected: ", D.align (ppr ty1) ] D.<> 
           D.line D.<> D.hsep [D.text "Inferred: ", D.align (ppr ty2) ] )
        D.<$> D.text "More precisely, the following types do not match."
        D.</> D.align (ppr ty1') D.<+> D.text "/=" D.<+> D.align (ppr ty2')

      pprDetail (OccurrenceCheck mv ty) =
        D.text "Cannot construct an infinite type:"
        D.<$> D.hsep[ ppr mv, D.text "=", D.align (ppr ty) ]

      pprDetail (MultipleUse v) =
        D.hsep [ D.text "Variable", ppr (originalQName v), D.text "must not be used more than once." ]

      pprDetail (NoUse v) =
        D.hsep [ D.text "Variable", ppr (originalQName v), D.text "must be used at once." ]

      pprDetail (Undefined v) =
        D.hsep [ D.text "Unbound variable", ppr (originalQName v) ]
        
      pprDetail (Other d) = d         
        
      pprContexts (Seq.Empty)  = D.empty
      pprContexts (es Seq.:|> e) =
        D.line D.<> D.text "when checking expression:" D.<+> ppr (location e) 
        D.<> D.nest 2 (D.line D.<> ppr e)
        D.<> pprContexts es 
     
atLoc :: MonadTypeCheck m => SrcSpan -> m r -> m r
atLoc NoLoc m = m
atLoc loc   m =
  catchError m $ \(TypeError oloc es reason) -> throwError (TypeError (maybe (Just loc) Just oloc) es reason)

atExp :: MonadTypeCheck m => Maybe S.LExp -> m r -> m r
atExp Nothing  m = m 
atExp (Just e) m =
  catchError m $ \(TypeError oloc es reason) -> throwError (TypeError oloc (e Seq.<| es) reason)
                   
  
class (MonadError TypeError m, Monad m) => MonadTypeCheck m where
  typeError :: ErrorDetail -> m a
  askType :: SrcSpan -> QName -> m Ty

  readTyVar :: MetaTyVar -> m (Maybe Ty)
  writeTyVar :: MetaTyVar -> Ty -> m ()
  
  resolveSyn :: Ty -> m Ty 

  withLVar :: QName -> Ty -> m r -> m r
  withUVar :: QName -> Ty -> m r -> m r

  -- typing under empty linear environment 
  withoutLinear :: m () -> m () 

  newMetaTyVar :: m MetaTyVar

  getMetaTyVarsInEnv :: m [MetaTyVar] 

  newSkolemTyVar :: TyVar -> m TyVar 

data Multiplicity = Omega | One | Zero 

type TyEnv = M.Map QName (Multiplicity, Ty)

-- Instead of the reader monad, we use the state monad to
-- handle linearity. 
data TInfo
  = TInfo { tiTyEnv   :: IORef TyEnv, 
            tiMvCount :: !(IORef Int),
            tiSyn     :: IORef (M.Map QName ([TyVar],  Ty)), 
            tiSvCount :: !(IORef Int)
          }    

-- newtype TC a = TC { unTC :: StateT TInfo (Either D.Doc) a }
newtype TC a = TC { unTC :: ExceptT TypeError (ReaderT TInfo IO) a }
  deriving (Functor, Applicative, Monad, MonadReader TInfo, MonadError TypeError, MonadIO) 

initTInfo :: IO TInfo
initTInfo = do 
  r1 <- newIORef 0
  r2 <- newIORef 0
  rt <- newIORef $ M.empty
  rs <- newIORef $ M.empty 
  return $ TInfo { tiTyEnv   = rt,
                   tiMvCount = r1,
                   tiSyn     = rs,
                   tiSvCount = r2 } 

setEnvs :: TInfo -> TypeTable -> SynTable -> IO ()
setEnvs ti tenv syn = do 
  writeIORef (tiTyEnv ti) $ M.map (\t -> (Omega, t)) tenv
  writeIORef (tiSyn   ti) syn 



runTC :: TInfo -> TC a -> IO (Either D.Doc a)
runTC tinfo (TC m) = do 
  res <- runReaderT (runExceptT m) tinfo
  return $ case res of
             Left e  -> Left (ppr e)
             Right v -> Right v 

  

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

getTyEnv :: TC TyEnv
getTyEnv = do
  ti <- ask 
  liftIO $ readIORef (tiTyEnv ti) 


putTyEnv :: TyEnv -> TC ()
putTyEnv tyEnv = do
  ref <- asks tiTyEnv 
  liftIO $ writeIORef ref tyEnv

lookupTyEnv :: SrcSpan -> QName -> TyEnv -> TC (Ty, TyEnv)
lookupTyEnv l n tyEnv =
  case M.lookup n tyEnv of
    Just (Omega, ty) -> return (ty, tyEnv)
    Just (One,   ty) -> return (ty, M.insert n (Zero, ty) tyEnv)
    Just (Zero,  _ ) ->
      atLoc l $ typeError $ MultipleUse n 
    _ ->
      atLoc l $ typeError $ Undefined n 


metaTyVars :: [Ty] -> [MetaTyVar]
metaTyVars xs = go xs []
  where
    go [] = id 
    go (t:ts) = goTy t . go ts

    goTy (TyCon _ ts) = go ts
    goTy (TyForAll _ t) = goTy t
    goTy (TySyn _ t)    = goTy t
    goTy (TyMetaV m)    = \r -> if m `elem` r then r else m:r
    goTy _              = id 

instance MonadTypeCheck TC where
  typeError d = throwError (TypeError Nothing Seq.Empty d)

  askType l n
    | Just k <- checkNameTuple n = do 
        let tvs = map (BoundTv . NormalName) [ 't':show i | i <- [1..k] ]
        let tys = map TyVar tvs
        return $ TyForAll tvs $ foldr (-@) (tupleTy tys) tys        
    | otherwise = do
        tyEnv <- getTyEnv 
        (ty, tyEnv') <- lookupTyEnv l n tyEnv
        putTyEnv tyEnv' 
        return ty

  readTyVar (MetaTyVar _ ref) = TC $ do
    lift $ lift $ readIORef ref 

  writeTyVar (MetaTyVar _ ref) ty = TC $ do
    lift $ lift $ writeIORef ref (Just ty) 


  withLVar x ty m = do
    tyEnv  <- getTyEnv
    let origX = M.lookup x tyEnv 
    putTyEnv $ M.insert x (One, ty) tyEnv 
    ret <- m
    tyEnvAfter <- getTyEnv 
    case M.lookup x tyEnvAfter of
      Just (Zero, _) ->
        case origX of
          Just ent -> do 
            putTyEnv $ M.insert x ent tyEnvAfter -- restore the original if any
            return ret 
          Nothing -> do 
            putTyEnv $ M.delete x tyEnvAfter
            return ret 
      _ -> do
        typeError $ NoUse x -- D.text "Linear type variable" D.<+> D.dquotes (ppr x) D.<+> D.text "is not used linearly."
    
  withUVar x ty m = do
    tyEnv <- getTyEnv
    let origX = M.lookup x tyEnv
    putTyEnv $ M.insert x (Omega, ty) tyEnv 
    ret <- m
    tyEnvAfter <- getTyEnv
    case origX of
      Nothing -> do 
        putTyEnv $ M.delete x tyEnvAfter
        return ret 
      Just ent -> do 
        putTyEnv $ M.insert x ent tyEnvAfter
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
    

  newMetaTyVar = TC $ do
    cref <- asks tiMvCount 
    cnt <- liftIO $ atomicModifyIORef' cref $ \cnt -> (cnt + 1, cnt)
    ref <- liftIO $ newIORef Nothing 
    return $ MetaTyVar cnt ref 

  resolveSyn ty = do
    ref <- asks tiSyn
    synMap <- liftIO $ readIORef ref 
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
              typeError $ Other $ D.hsep [ D.text "Type synonym", D.dquotes (ppr c), D.text "must be fully-applied." ] 

  getMetaTyVarsInEnv = do
    tyEnv <- getTyEnv
    let ts = map snd $ M.elems tyEnv
    return $ metaTyVars ts 

  newSkolemTyVar ty = do
    cref <- asks tiSvCount
    cnt <- liftIO $ atomicModifyIORef' cref $ \cnt -> (cnt + 1, cnt)
    return $ SkolemTv ty cnt 

withLVars :: MonadTypeCheck m => [ (QName, Ty) ] -> m r -> m r
withLVars ns m = foldr (uncurry withLVar) m ns

withUVars :: MonadTypeCheck m => [ (QName, Ty) ] -> m r -> m r
withUVars ns m = foldr (uncurry withUVar) m ns 

newMetaTy :: MonadTypeCheck m => m Ty
newMetaTy = fmap TyMetaV $ newMetaTyVar 

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
zonkMetaTyVar mv = {- trace "zonk!" $ -} do 
  res <- readTyVar mv 
  case res of
    Nothing -> return (TyMetaV mv) 
    Just ty -> do
      ty' <- zonkType ty
      writeTyVar mv ty'
      return ty'

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
                                            typeError $ Other $ D.hsep [D.text "Type construtor", ppr c, D.text "has different numbesr of arguments."]
                                          zipWithM_ unifyWork ts ts' 
unifyWork ty1 ty2 = do
  ty1' <- zonkType ty1
  ty2' <- zonkType ty2
  typeError $ UnMatchTy ty1' ty2' 

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
    Nothing   ->
      unless (mv == mv2) $ 
       writeTyVar mv (TyMetaV mv2) 
    Just ty2' -> unifyUnboundMetaTyVar mv ty2' 
unifyUnboundMetaTyVar mv ty2 = do 
  ty2' <- zonkType ty2
  let mvs = metaTyVars [ty2']
  case mv `elem` mvs of
    True  -> typeError $ OccurrenceCheck mv ty2' 
    False -> -- trace (show $ D.hsep [D.text "[assign]", ppr mv, D.text "=", D.align (ppr ty2')]) $ 
      writeTyVar mv ty2'

        
   
  

  


    

  
