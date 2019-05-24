module Language.Sparcl.Typing.TCMonad where

import qualified Data.Map as M
import Data.Map (Map)

import qualified Data.Sequence as Seq 
import Data.Sequence (Seq)

import Control.Monad.Reader
import Control.Monad.Except 
import Control.Exception (evaluate, Exception, throw, catch)

import Data.IORef
import Data.Foldable (toList)

import Language.Sparcl.Name
import Language.Sparcl.Typing.Type 
import Language.Sparcl.Multiplicity
import Language.Sparcl.Pass
import Language.Sparcl.SrcLoc
import Language.Sparcl.Exception 
import Language.Sparcl.Pretty hiding ((<$>))
import qualified Language.Sparcl.Pretty as D 
import qualified Language.Sparcl.Surface.Syntax as S 

data AbortTyping = AbortTyping 
  deriving Show
instance Exception AbortTyping 


data WhenChecking = CheckingEquality    Ty Ty
                  | CheckingConstraint  [TyConstraint]
                  | CheckingMoreGeneral Ty Ty
                  | OtherContext        Doc 
                  | CheckingNone 
  

data TypeError = TypeError (Maybe SrcSpan) [S.LExp 'Renaming] WhenChecking ErrorDetail

data ErrorDetail
  = UnMatchTy  Ty Ty 
--  | UnMatchTyD Ty Ty Ty Ty -- inferred and expected
  | OccurrenceCheck MetaTyVar Ty
  | MultipleUse Name
  | NoUse       Name
  | Undefined   Name 
  | Other       D.Doc 
  

instance Pretty TypeError where
  ppr (TypeError l exprs ctxt doc) =
     -- D.bold (D.text "[TYPE ERROR]") D.<+> D.nest 2
     (maybe (D.text "*unknown place*") ppr l 
      D.<$> pprDetail doc <> pprWhenChecking ctxt 
      D.<$> pprContexts (drop (length exprs - 3) exprs))     
    where
      pprWhenChecking (CheckingEquality ty1 ty2) =
        D.line <> D.text "when checking the following types are equivalent:"
        D.<> D.nest 2 (line <> vsep [ hsep[text "Inferred:", ppr ty1],
                                      hsep[text "Expected:", ppr ty2] ])

      pprWhenChecking (CheckingMoreGeneral ty1 ty2) =
        D.line <> D.text "when checking the inferred type is more general than the expected."
        D.<> D.nest 2 (line <> vsep [ hsep[text "Inferred:", ppr ty1],
                                      hsep[text "Expected:", ppr ty2] ])
        
      pprWhenChecking (CheckingConstraint cs) =
        D.line <> D.text "when checking constraints:"
        D.<$> D.parens (hsep $ punctuate comma $ map ppr cs)

      pprWhenChecking (OtherContext d) =
        D.line <> D.text "when checking" <+> d

      pprWhenChecking CheckingNone = D.empty 
      
      pprDetail (UnMatchTy ty1 ty2) = 
        D.text "Types do not match:"
        D.<+> D.align (ppr ty1) D.<+> D.text "/=" D.<+> D.align (ppr ty2)

      -- pprDetail (UnMatchTyD ty1 ty2 ty1' ty2') =
      --   D.text "Types do not match" D.<> D.nest 2 
      --    ( D.line D.<> D.nest 2 (D.sep [D.text "Expected:", D.align (ppr ty1) ]) D.<> 
      --      D.line D.<> D.nest 2 (D.sep [D.text "Inferred:", D.align (ppr ty2) ]) )
      --   D.<$> D.text "More precisely, the following types do not match."
      --   <> D.nest 2 (line <> D.align (ppr ty1') D.<+> D.text "/=" D.<+> D.align (ppr ty2'))

      pprDetail (OccurrenceCheck mv ty) =
        D.text "Cannot construct an infinite type:"
        D.<$> D.hsep[ ppr mv, D.text "=", D.align (ppr ty) ]

      pprDetail (MultipleUse v) =
        D.hsep [ D.text "Variable", ppr v, D.text "must not be used more than once." ]

      pprDetail (NoUse v) =
        D.hsep [ D.text "Variable", ppr v, D.text "must be used at once." ]

      pprDetail (Undefined v) =
        D.hsep [ D.text "Unbound variable", ppr v ]
        
      pprDetail (Other d) = d         
        
      pprContexts []  = D.empty
      pprContexts (e:es) =
        D.line D.<> D.text "when checking expression:" D.<+> ppr (location e) 
        D.<> D.nest 2 (D.line D.<> ppr e)
        D.<> pprContexts es 

 

-- A typing environment just holds type information.  This reflects
-- our principle; multiplicites are synthesized instead of checked.

type TyEnv = Map Name Ty

-- A usage environment gathers how many times a variable is used.
--
-- Storing multiplicity variable is necessarly for application for a
-- function of type a # p -> b to an expression that variables used in
-- the expression has multiplicity `p` if it were used one.
type UseMap = Map Name Mul
data Mul = MulConst Multiplicity | MulVar MetaTyVar 

mergeUseMap :: UseMap -> UseMap -> UseMap
mergeUseMap = M.unionWith (\_ _ -> MulConst Omega)

-- the following information is used. The information is kept globally. 
data TypingContext =
  TypingContext { tcRefMvCount :: !(IORef Int),
                  tcRefSvCount :: !(IORef Int),
                  tcTyEnv      :: TyEnv,    -- Current typing environment
                  tcMultEnv    :: [Ty], 
                  tcSyn        :: SynTable, -- Current type synonym table
                  tcContexts   :: [S.LExp 'Renaming], -- parent expressions
                  tcLoc        :: Maybe SrcSpan,  -- focused part
                  tcChecking   :: WhenChecking, 
                  tcRefErrors  :: !(IORef (Seq TypeError))
                               -- Type errors are accumulated for better error messages 
                  }

initTypingContext :: IO TypingContext
initTypingContext = do
  r1 <- newIORef 0
  r2 <- newIORef 0
  r  <- newIORef Seq.empty 
  return $ TypingContext { tcRefMvCount = r1,
                           tcRefSvCount = r2,
                           tcRefErrors  = r ,
                           tcLoc        = Nothing, 
                           tcContexts   = [],
                           tcMultEnv    = [],
                           tcChecking   = CheckingNone, 
                           tcTyEnv      = M.empty,
                           tcSyn        = M.empty }

-- This function must be called before each session of type checking. 
refreshTC :: TypingContext -> IO TypingContext
refreshTC tc = do
  r <- newIORef Seq.empty 
  return $ tc { tcTyEnv     = M.empty,
                tcSyn       = M.empty,
                tcMultEnv   = [], 
                tcLoc       = Nothing,
                tcRefErrors = r,
                tcChecking  = CheckingNone, 
                tcContexts  = [] } 
  
setEnvs :: TypingContext -> TypeTable -> SynTable -> TypingContext 
setEnvs tc tenv syn =
  tc { tcTyEnv = tenv,
       tcSyn   = syn }

runTC :: TypingContext -> TC a -> IO a
runTC tc m = do 
  res <- runReaderT (unTC m) tc `catch` (\(_ :: AbortTyping) -> return undefined)
  errs <- readIORef (tcRefErrors tc)  
  if not (Seq.null errs) -- if this is not empty, it must be the case that res is not undefined. 
    then do
    errs' <- runReaderT (unTC $ mapM zonkTypeError $ toList errs) tc 
    staticError $ vcat (map ppr errs')    
    else
    return res

runTCWith :: TypingContext -> TypeTable -> SynTable -> TC a -> IO a 
runTCWith tc tytbl syntbl m = do 
  tc' <- refreshTC tc
  runTC (setEnvs tc' tytbl syntbl) m 
  
    

-- A concrete implementation of typing checking monad. 
newtype TC a = TC { unTC :: ReaderT TypingContext IO a }
  deriving (Functor, Applicative, Monad, MonadReader TypingContext, MonadIO)

instance MonadError AbortTyping TC where
  throwError e = TC $ ReaderT $ \_ -> throw e
  catchError (TC x) f = TC $ ReaderT $ \r ->
    catch (evaluate =<< runReaderT x r) (\y -> runReaderT (unTC $ f y) r) 
  
class MonadIO m => MonadTypeCheck m where
  -- Error reporting. The method does not abort the current computation. 
  reportError :: ErrorDetail -> m ()

  whenChecking :: WhenChecking -> m r -> m r 

  abortTyping :: m a 

  -- Ask the type of a symbol 
  askType :: SrcSpan -> Name -> m Ty 


  atLoc :: SrcSpan -> m r -> m r
  atExp :: S.LExp 'Renaming -> m r -> m r 

  newMetaTyVar :: m MetaTyVar
  readTyVar  :: MetaTyVar -> m (Maybe Ty)
  writeTyVar :: MetaTyVar -> Ty -> m ()

  getMetaTyVarsInEnv :: m [MetaTyVar] 

  resolveSyn :: Ty -> m Ty 

  newSkolemTyVar :: TyVar -> m TyVar 

  -- type checking with a new entry in the type environment. 
  withVar :: Name -> Ty -> m r -> m r

  -- type checking with a new entry in the synonym table.
  withSyn :: Name -> ([TyVar], Ty) -> m r -> m r

  -- for generalization 
  withMultVar :: Ty -> m r -> m r 

tupleConTy :: Int -> Ty
tupleConTy n =
  let tvs = map BoundTv [ Alpha i (User $ 't':show i) | i <- [1..n] ]
      tys = map TyVar tvs
  in TyForAll tvs $ TyQual [] $ foldr (-@) (tupleTy tys) tys        

arbitraryTy :: MonadTypeCheck m => m Ty
arbitraryTy = do
  t <- newMetaTyVar
  return $ TyMetaV t 

instance MonadTypeCheck m => MonadTypeCheck (ReaderT r m) where
  abortTyping = lift abortTyping

  reportError mes = lift (reportError mes)
  whenChecking t m = ReaderT $ whenChecking t . runReaderT m 

  atLoc loc m = ReaderT $ \r -> atLoc loc (runReaderT m r)
  atExp ex m = ReaderT $ \r -> atExp ex (runReaderT m r)

  askType l n = lift (askType l n)

  newMetaTyVar = lift newMetaTyVar
  newSkolemTyVar = lift . newSkolemTyVar

  readTyVar tv = lift (readTyVar tv)
  writeTyVar tv t = lift (writeTyVar tv t)

  withVar n t m = ReaderT $ \r -> withVar n t (runReaderT m r) 
  withSyn tv t m = ReaderT $ \r -> withSyn tv t (runReaderT m r)

  withMultVar ty m = ReaderT $ withMultVar ty . runReaderT m 

  getMetaTyVarsInEnv = lift getMetaTyVarsInEnv
  resolveSyn ty = lift (resolveSyn ty) 

instance MonadTypeCheck TC where
  abortTyping = throwError AbortTyping 

  reportError mes = do
    tc <- ask
    let err = TypeError (tcLoc tc) (tcContexts tc) (tcChecking tc) mes 
    liftIO $ modifyIORef (tcRefErrors tc) $ \s -> s Seq.:|> err

  whenChecking t =
    local (\tc -> tc { tcChecking = t })

  atLoc NoLoc m = m
  atLoc loc   m =
    local (\tc -> tc { tcLoc = Just loc }) m

  atExp e m =
    local (\tc -> tc { tcContexts = e : tcContexts tc }) m 

  askType l n
    | Just k <- checkNameTuple n = do
        return $ tupleConTy k
    | otherwise = do        
        tyEnv <- asks tcTyEnv
        case M.lookup n tyEnv of
          Just ty -> return ty
          Nothing -> do 
            atLoc l (reportError $ Undefined n)
            arbitraryTy

  newMetaTyVar = do
    cref <- asks tcRefMvCount
    cnt <- liftIO $ atomicModifyIORef' cref $ \cnt -> (cnt + 1, cnt)
    ref <- liftIO $ newIORef Nothing
    return $ MetaTyVar cnt ref

  readTyVar (MetaTyVar _ ref) = TC $ do
    liftIO $ readIORef ref 

  writeTyVar (MetaTyVar _ ref) ty = TC $ do
    liftIO $ writeIORef ref (Just ty) 


  newSkolemTyVar ty = do
    cref <- asks tcRefSvCount
    cnt <- liftIO $ atomicModifyIORef' cref $ \cnt -> (cnt + 1, cnt)
    return $ SkolemTv ty cnt 


  resolveSyn ty = do
    synMap <- asks tcSyn
    go synMap ty 
    where
      goQ synMap (TyQual cs t) = 
        TyQual <$> mapM (goC synMap) cs <*> go synMap t

      goC synMap (MEqMax t1 t2 t3) =
        MEqMax <$> go synMap t1 <*> go synMap t2 <*> go synMap t3 
      
      go _synMap (TyVar x) = return (TyVar x)
      go synMap (TyForAll ns t) =
        TyForAll ns <$> goQ synMap t
      go _synMap (TyMetaV m) = return (TyMetaV m)      
      go synMap (TySyn origTy actualTy) =
        TySyn origTy <$> go synMap actualTy
      go synMap orig@(TyCon c ts) = do
        case M.lookup c synMap of
          Nothing ->
            TyCon c <$> mapM (go synMap) ts 
          Just (ns, tyBody)
            | length ns == length ts -> 
              TySyn orig <$> go synMap (substTy (zip ns ts) tyBody)
          Just _ -> do 
            reportError $ Other $ D.hsep [ D.text "Type synonym", D.dquotes (ppr c), D.text "must be fully-applied." ] 
            abortTyping
      go _ (TyMult m) = return $ TyMult m 

  withVar x ty m = 
    local (\tc -> tc { tcTyEnv = M.insert x ty (tcTyEnv tc) }) m 

  withSyn tv v m = 
    local (\tc -> tc { tcSyn = M.insert tv v (tcSyn tc) }) m 

  withMultVar ty = local (\tc -> tc { tcMultEnv = ty : tcMultEnv tc }) 

  getMetaTyVarsInEnv = do
    tyEnv <- asks tcTyEnv
    let ts = M.elems tyEnv
    multEnv <- asks tcMultEnv
    ts' <- mapM zonkType (ts ++ multEnv) 
    return $ metaTyVars ts' -- (ts ++ multEnv)


newMetaTy :: MonadTypeCheck m => m Ty
newMetaTy = fmap TyMetaV $ newMetaTyVar 

withVars :: MonadTypeCheck m => [ (Name, Ty) ] -> m r -> m r
withVars ns m = foldr (uncurry withVar) m ns

withSyns :: MonadTypeCheck m => [ (Name, ([TyVar], Ty)) ] -> m r -> m  r
withSyns xs m = foldr (uncurry withSyn) m xs  

withMultVars :: MonadTypeCheck m => [Ty] -> m r -> m r
withMultVars xs m = foldr withMultVar m xs 

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
  TyForAll ns <$> zonkTypeQ t
zonkType (TyMetaV m) = zonkMetaTyVar m
zonkType (TySyn origTy ty) =
  TySyn <$> zonkType origTy <*> zonkType ty 
zonkType (TyMult m) = return (TyMult m) 

zonkTypeQ :: MonadTypeCheck m => QualTy -> m QualTy
zonkTypeQ (TyQual cs t) = TyQual <$> mapM zonkTypeC cs <*> zonkType t

zonkTypeC :: MonadTypeCheck m => TyConstraint -> m TyConstraint
zonkTypeC (MEqMax t1 t2 t3) = MEqMax <$> zonkType t1 <*> zonkType t2 <*> zonkType t3

zonkTypeError :: MonadTypeCheck m => TypeError -> m TypeError
zonkTypeError (TypeError loc es wc res) = do
  wc'  <- zonkWhenChecking wc
  res' <- zonkErrorDetail  res
  return $ TypeError loc es wc' res' 

zonkWhenChecking :: MonadTypeCheck m => WhenChecking -> m WhenChecking
zonkWhenChecking (CheckingEquality t1 t2) = 
  CheckingEquality <$> zonkType t1 <*> zonkType t2
zonkWhenChecking (CheckingMoreGeneral t1 t2) =
  CheckingMoreGeneral <$> zonkType t1 <*> zonkType t2 
zonkWhenChecking (CheckingConstraint cs) =
  CheckingConstraint <$> mapM zonkTypeC cs
zonkWhenChecking (OtherContext d) = return (OtherContext d)   
zonkWhenChecking CheckingNone = return CheckingNone

zonkErrorDetail :: MonadTypeCheck m => ErrorDetail -> m ErrorDetail
zonkErrorDetail (UnMatchTy t1 t2) = UnMatchTy <$> zonkType t1 <*> zonkType t2
zonkErrorDetail (OccurrenceCheck tv ty) =
  OccurrenceCheck tv <$> zonkType ty
zonkErrorDetail res = pure res   
  

freeTyVars :: MonadTypeCheck m => [Ty] -> m [TyVar]
freeTyVars types = do
  ts' <- mapM zonkType types
  return $ go ts' []
    where
      go []     r = r
      go (t:ts) r = goT [] t (go ts r)

      goT :: [TyVar] -> Ty -> [TyVar] -> [TyVar] 
      goT bound (TyVar t) r
        | t `elem` bound = r
        | t `elem` r     = r
        | otherwise      = t : r
      goT bound (TyCon _ ts) r =
        foldr (goT bound) r ts
      goT bound (TyForAll bs t) r = goQ (bs ++ bound) t r
      goT _bound (TyMetaV _) r = r
      goT bound (TySyn ty _) r = goT bound ty r 
      goT _bound (TyMult _) r = r 

      goQ :: [TyVar] -> QualTy -> [TyVar] -> [TyVar] 
      goQ bound (TyQual cs t) r = foldr (goC bound) (goT bound t r) cs

      goC :: [TyVar] -> TyConstraint -> [TyVar] -> [TyVar]
      goC bound (MEqMax t1 t2 t3) r = goT bound t1 $ goT bound t2 $ goT bound t3 r 


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
                                            reportError $ Other $ D.hsep [D.text "Type construtor", ppr c, D.text "has different number of arguments."]
                                          zipWithM_ unifyWork ts ts'
unifyWork (TyMult m) (TyMult m') | m == m' = return ()                                           
unifyWork ty1 ty2 = do
  ty1' <- zonkType ty1
  ty2' <- zonkType ty2
  reportError $ UnMatchTy ty1' ty2' 

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
    True  -> do 
      reportError $ OccurrenceCheck mv ty2'
      -- We abort typing when occurrence check fails; otherwise, zonkType can diverge. 
      abortTyping 
    False -> -- trace (show $ D.hsep [D.text "[assign]", ppr mv, D.text "=", D.align (ppr ty2')]) $ 
      writeTyVar mv ty2'

        
