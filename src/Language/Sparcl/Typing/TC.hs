{-# LANGUAGE ViewPatterns #-}
module Language.Sparcl.Typing.TC where

-- Type checking monad
-- Here, we use int values for meta variables
import Language.Sparcl.Untyped.Desugar.Syntax
import qualified Language.Sparcl.Untyped.Syntax as S 

import qualified Data.IntMap as IM
import qualified Data.Map as M

import Data.Maybe (fromMaybe)

import Control.Monad.State 
import Control.Monad.Except 

import qualified Text.PrettyPrint.ANSI.Leijen as D
import Language.Sparcl.Pretty 

-- import Control.Arrow (first) 

import qualified Data.Sequence as Seq 

import Debug.Trace 

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
newtype TC a = TC { unTC :: ExceptT TypeError (State TInfo) a }
  deriving (Functor, Applicative, Monad, MonadState TInfo, MonadError TypeError) 

runTC :: TInfo -> TC a -> (Either D.Doc a, TInfo) 
runTC tinfo (TC m) =
  let (res, ti) = runState (runExceptT m) tinfo
      res' = case res of
               Left e  -> Left (ppr e)
               Right v -> Right v 
  in trace (show $ pprMap $ M.fromList $ IM.toList $ tiMap ti) (res', ti) 
  

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
      atLoc l $ typeError $ MultipleUse n 
    _ ->
      atLoc l $ typeError $ Undefined n 


findTy :: MetaTyVar -> IM.IntMap Ty -> (Maybe Ty, IM.IntMap Ty)
findTy (MetaTyVar i _) map =
  case IM.lookup i map of
    -- Just (TyMetaV mv) ->
    --   let (res, map') = findTy mv map
    --   in case res of
    --        Just ty -> (Just ty, IM.insert i ty map')
    --        Nothing -> (Nothing, map') 
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
  typeError d = throwError (TypeError Nothing Seq.Empty d)

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
    let (res, tm') = findTy mv (tiMap ti)
    put (ti { tiMap = tm' })
    return res

  writeTyVar (MetaTyVar i _) ty = do
    ti <- get
    let tm' = IM.insert i ty $ tiMap ti 
    put (ti { tiMap = tm'})


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
              typeError $ Other $ D.hsep [ D.text "Type synonym", D.dquotes (ppr c), D.text "must be fully-applied." ] 

  getMetaTyVarsInEnv = do
    tyEnv <- getTyEnv
    let ts = map snd $ M.elems tyEnv
    return $ metaTyVars ts 

  newSkolemTyVar ty = do
    ti <- get
    let cnt = tiSvCount ti
    put $ ti { tiSvCount = cnt + 1 }
    return $ SkolemTv ty cnt 

withLVars :: MonadTypeCheck m => [ (QName, Ty) ] -> m r -> m r
withLVars ns m = foldr (uncurry withLVar) m ns

withUVars :: MonadTypeCheck m => [ (QName, Ty) ] -> m r -> m r
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

        
   
  

  


    

  
