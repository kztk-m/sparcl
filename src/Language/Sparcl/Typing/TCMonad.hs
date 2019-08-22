{-# LANGUAGE TupleSections #-}

module Language.Sparcl.Typing.TCMonad where

import qualified Data.Map as M
import Data.Map (Map)
import Data.Map.Merge.Lazy as M 

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

import qualified Language.Sparcl.Class as C

import Language.Sparcl.DebugPrint 

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
  ppr (TypeError l exprs ctxt doc) = nest 2 $ 
     -- D.bold (D.text "[TYPE ERROR]") D.<+> D.nest 2
    D.bold (maybe (D.text "<*unknown place*>") ppr l <> text ":" <+> D.red (text "type error"))
    <> line 
    <> pprDetail doc
    <> pprWhenChecking ctxt
    <> (if null exprs then empty else item (group $ pprContexts (drop (length exprs - 3) exprs)))
    where
      item d = text "-" <+> align d <> line 
      
      pprWhenChecking (CheckingEquality ty1 ty2) =
        D.line <> 
        item (D.text "when checking the following types are equivalent:"
              D.<> D.nest 2 (line <> vsep [ hsep[text "Inferred:", align $ ppr ty1],
                                            hsep[text "Expected:", align $ ppr ty2] ]))

      pprWhenChecking (CheckingMoreGeneral ty1 ty2) =
        D.line <>
        item (D.text "when checking the inferred type is more general than the expected."
              D.<> D.nest 2 (line <> vsep [ hsep[text "Inferred:", align $ ppr ty1],
                                            hsep[text "Expected:", align $ ppr ty2] ]))
        
      pprWhenChecking (CheckingConstraint cs) =
        D.line <>
        item (D.text "when checking constraints:"
              D.<$> D.parens (hsep $ punctuate comma $ map ppr cs))

      pprWhenChecking (OtherContext d) =
        D.line <>
        item (D.text "when checking" <+> d)

      pprWhenChecking CheckingNone = D.empty 


      pprDetail = item . go
        where 
          go (UnMatchTy ty1 ty2) = 
            D.text "Types do not match:"
            D.<+> D.align (ppr ty1) D.<+> D.text "/=" D.<+> D.align (ppr ty2)

      -- pprDetail (UnMatchTyD ty1 ty2 ty1' ty2') =
      --   D.text "Types do not match" D.<> D.nest 2 
      --    ( D.line D.<> D.nest 2 (D.sep [D.text "Expected:", D.align (ppr ty1) ]) D.<> 
      --      D.line D.<> D.nest 2 (D.sep [D.text "Inferred:", D.align (ppr ty2) ]) )
      --   D.<$> D.text "More precisely, the following types do not match."
      --   <> D.nest 2 (line <> D.align (ppr ty1') D.<+> D.text "/=" D.<+> D.align (ppr ty2'))

          go (OccurrenceCheck mv ty) = 
            D.text "Cannot construct an infinite type:"
            D.<$> D.hsep[ ppr mv, D.text "=", D.align (ppr ty) ]

          go (MultipleUse v) =
            D.hsep [ D.text "Variable", ppr v, D.text "must not be used more than once." ]

          go (NoUse v) =
            D.hsep [ D.text "Variable", ppr v, D.text "must be used at once." ]

          go (Undefined v) =
            D.hsep [ D.text "Unbound variable", ppr v ]
        
          go (Other d) = d         
        
      pprContexts []     = D.empty
      pprContexts [e]    = pprContext e
      pprContexts (e:es) = pprContext e D.<$> pprContexts es

      pprContext e =
        D.text "In:" D.<+> ppr (location e) 
        D.<> D.nest 2 (D.line D.<> ppr e)

  

-- A typing environment just holds type information.  This reflects
-- our principle; multiplicites are synthesized instead of checked.
type TyEnv = Map Name Ty

dummyName :: Name 
dummyName = Original (ModuleName "") (User "") (Bare (User ""))

-- A usage environment gathers how many times a variable is used.
--
-- Storing multiplicity variable is necessarly for application for a
-- function of type a # p -> b to an expression that variables used in
-- the expression has multiplicity `p` if it were used one.
type UseMap = Map Name Multiplication

data Multiplication = Multiply Multiplication Multiplication
                    | MSingle Mul 

instance MultiplicityLike Multiplication where
  one   = MSingle one 
  omega = MSingle omega
  fromMultiplicity = MSingle . fromMultiplicity 

instance Lub Multiplication where
  lub (MSingle (MulConst Omega)) _ = MSingle (MulConst Omega)
  lub (MSingle (MulConst One))   t = t
  lub _ (MSingle (MulConst Omega)) = MSingle (MulConst Omega)
  lub t (MSingle (MulConst One))   = t
  lub t1 t2 = Multiply t1 t2

ty2mult :: MonadTypeCheck m => MultTy -> m Multiplication
ty2mult = zonkType >=> go 
    where
      go (TyMult t)  = return $ MSingle (MulConst t)
      go (TyMetaV t) = return $ MSingle (MulVar t)
      go _           = do
        reportError $ Other $ text "Expected multiplicity"
        m <- newMetaTyVar
        return $ MSingle (MulVar m) 

data Mul = MulConst Multiplicity | MulVar MetaTyVar 

instance MultiplicityLike Mul where
  one   = MulConst One
  omega = MulConst Omega
  fromMultiplicity = MulConst 


m2ty :: Multiplication -> [Ty]
m2ty ms = case go ms [] of
            Nothing -> [omega]
            Just v  -> v 
  where
    go :: Multiplication -> [Ty] -> Maybe [Ty]
    go (Multiply t1 t2) r = go t1 =<< go t2 r
    go (MSingle m) r =
      case m of
        MulConst Omega -> Nothing 
        MulConst One   -> return r
        MulVar   t     -> return (TyMetaV t : r)
        
        
-- (Multiply t1 t2) = mult t1 t2
--   where
--     mult [TyMult Omega] _ = TyMult Omega 
--     mult []             t = t
--     mult 
    
-- m2ty MUnit            = [one]
-- m2ty (MSingle t)      = [t] 

singletonUseMap :: Name -> UseMap
singletonUseMap n = M.singleton n one 

lookupUseMap :: Name -> UseMap -> Maybe Multiplication
lookupUseMap = M.lookup 

multiplyUseMap :: UseMap -> UseMap -> UseMap
multiplyUseMap = M.merge (M.mapMissing $ \_ _ -> MSingle (MulConst Omega))
                         (M.mapMissing $ \_ _ -> MSingle (MulConst Omega))
                         (M.zipWithMatched $ \_ -> Multiply)

mergeUseMap :: UseMap -> UseMap -> UseMap
mergeUseMap = M.unionWith (\_ _ -> MSingle $ MulConst Omega)

raiseUse :: Multiplication -> UseMap -> UseMap
raiseUse m = fmap (lub m) 

emptyUseMap :: UseMap 
emptyUseMap = M.empty

deleteUseMap :: Name -> UseMap -> UseMap
deleteUseMap = M.delete 

-- the following information is used. The information is kept globally. 
data TypingContext =
  TypingContext { tcRefMvCount :: !(IORef Int),
                  tcRefSvCount :: !(IORef Int),
                  tcTcLevel    :: TcLevel,
                  tcConstraint :: !(IORef [TyConstraint]), 
                  tcTyEnv      :: TyEnv,    -- Current typing environment
                  tcSyn        :: SynTable, -- Current type synonym table
                  tcContexts   :: [S.LExp 'Renaming], -- parent expressions
                  tcLoc        :: Maybe SrcSpan,  -- focused part
                  tcChecking   :: WhenChecking,
                  tcDebugLevel :: !Int, 
                  tcRefErrors  :: !(IORef (Seq TypeError))
                               -- Type errors are accumulated for better error messages 
                  }


instance C.Has KeyDebugLevel Int TC where
  ask _ = TC $ asks tcDebugLevel

initTypingContext :: IO TypingContext
initTypingContext = do
  r1 <- newIORef 0
  r2 <- newIORef 0
  r  <- newIORef Seq.empty
  rc <- newIORef [] 
  return TypingContext { tcRefMvCount = r1,
                         tcRefSvCount = r2,
                         tcTcLevel    = 0 , 
                         tcRefErrors  = r ,
                         tcConstraint = rc, 
                         tcLoc        = Nothing, 
                         tcContexts   = [],
                         tcChecking   = CheckingNone,
                         tcDebugLevel = 0, 
                         tcTyEnv      = M.empty,
                         tcSyn        = M.empty }

-- This function must be called before each session of type checking. 
refreshTC :: TypingContext -> IO TypingContext
refreshTC tc = do
  r <- newIORef Seq.empty
  rc <- newIORef [] 
  return $ tc { tcTyEnv     = M.empty,
                tcSyn       = M.empty,
                tcLoc       = Nothing,
                tcConstraint = rc,
                tcRefErrors = r,
                tcChecking  = CheckingNone, 
                tcContexts  = [] } 

setEnvs :: TypingContext -> TypeTable -> SynTable -> TypingContext 
setEnvs tc tenv syn =
  tc { tcTyEnv = tenv,
       tcSyn   = syn }

setDebugLevel :: TypingContext -> Int -> TypingContext
setDebugLevel tc lv = tc { tcDebugLevel = lv } 

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

class (C.Has KeyDebugLevel Int m, MonadIO m) => MonadTypeCheck m where
  -- Error reporting. The method does not abort the current computation. 
  reportError :: ErrorDetail -> m ()

  whenChecking :: WhenChecking -> m r -> m r 

  abortTyping :: m a 

  -- Ask the type of a symbol 
  askType :: SrcSpan -> Name -> m Ty 

  askCurrentTcLevel :: m TcLevel 

  atLoc :: SrcSpan -> m r -> m r
  atExp :: S.LExp 'Renaming -> m r -> m r 


  addConstraint  :: [TyConstraint] -> m ()
  readConstraint :: m [TyConstraint]
  setConstraint  :: [TyConstraint] -> m () 

  newMetaTyVar :: m MetaTyVar
  readTyVar  :: MetaTyVar -> m (Maybe Ty)
  writeTyVar :: MetaTyVar -> Ty -> m ()

  -- getMetaTyVarsInEnv :: m [MetaTyVar] 

  resolveSyn :: Ty -> m Ty 

  newSkolemTyVar :: TyVar -> m TyVar 

  -- type checking with a new entry in the type environment. 
  withVar :: Name -> Ty -> m r -> m r

  -- m r is performed in the next level. 
  pushLevel :: m r -> m r 

  -- type checking with a new entry in the synonym table.
  withSyn :: Name -> ([TyVar], Ty) -> m r -> m r


tupleConTy :: Int -> Ty
tupleConTy n =
  let tvs = map BoundTv [ Alpha i (User $ 't':show i) | i <- [1..n] ]
      tys = map TyVar tvs
  in TyForAll tvs $ TyQual [] $ foldr (-@) (tupleTy tys) tys        

arbitraryTy :: MonadTypeCheck m => m Ty
arbitraryTy = TyMetaV <$> newMetaTyVar


instance MonadTypeCheck m => MonadTypeCheck (ReaderT r m) where
  abortTyping = lift abortTyping

  reportError mes = lift (reportError mes)
  whenChecking t m = ReaderT $ whenChecking t . runReaderT m 

  atLoc loc m = ReaderT $ \r -> atLoc loc (runReaderT m r)
  atExp ex m = ReaderT $ \r -> atExp ex (runReaderT m r)


  addConstraint c = lift (addConstraint c)
  readConstraint = lift readConstraint

  setConstraint cs = lift (setConstraint cs)
  

  askType l n = lift (askType l n)

  askCurrentTcLevel = lift askCurrentTcLevel

  newMetaTyVar = lift newMetaTyVar
  newSkolemTyVar = lift . newSkolemTyVar

  readTyVar tv = lift (readTyVar tv)
  writeTyVar tv t = lift (writeTyVar tv t)

  pushLevel m = ReaderT $ \r -> pushLevel (runReaderT m r) 

  -- withVar n t mult m = ReaderT $ \r -> withVar n t mult (runReaderT m r)
  withVar n t m = ReaderT $ \r -> withVar n t (runReaderT m r) 
  withSyn tv t m = ReaderT $ \r -> withSyn tv t (runReaderT m r)

  -- getMetaTyVarsInEnv = lift getMetaTyVarsInEnv
  resolveSyn ty = lift (resolveSyn ty) 

instance MonadTypeCheck TC where
  abortTyping = throwError AbortTyping 

  reportError mes = do
    tc <- ask
    let err = TypeError (tcLoc tc) (tcContexts tc) (tcChecking tc) mes 
    liftIO $ modifyIORef (tcRefErrors tc) $ \s -> s Seq.:|> err

  whenChecking t =
    local (\tc -> tc { tcChecking = t })

  atLoc NoLoc = id
  atLoc loc   = local (\tc -> tc { tcLoc = Just loc })

  atExp e = local (\tc -> tc { tcContexts = e : tcContexts tc }) 

  askCurrentTcLevel = asks tcTcLevel

  readConstraint = do
    csRef <- asks tcConstraint
    liftIO $ readIORef csRef

  addConstraint cs = do
    csRef <- asks tcConstraint
    liftIO $ modifyIORef csRef (cs ++) 

  setConstraint cs = do
    csRef <- asks tcConstraint
    liftIO $ writeIORef csRef cs
    
  

  askType l n
    | Just k <- checkNameTuple n = 
        return $ tupleConTy k
    | otherwise = do        
        tyEnv <- asks tcTyEnv
        case M.lookup n tyEnv of
          Just ty -> do 
            ty' <- zonkType ty
            debugPrint 4 $ ppr n <+> text ":" <+> ppr ty'
            return ty' 
          Nothing -> do 
            atLoc l (reportError $ Undefined n)
            arbitraryTy

  newMetaTyVar = do
    cref <- asks tcRefMvCount
    lv   <- asks tcTcLevel 
    cnt <- liftIO $ atomicModifyIORef' cref $ \cnt -> (cnt + 1, cnt)
    ref <- liftIO $ newIORef Nothing
    lref <- liftIO $ newIORef lv 
    return $ MetaTyVar cnt ref lref  

  readTyVar (MetaTyVar _ ref _) = TC $ 
    liftIO $ readIORef ref 

  writeTyVar (MetaTyVar _ ref _) ty = TC $ 
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

      -- goC synMap (MEqMax t1 t2 t3) =
      --   MEqMax <$> go synMap t1 <*> go synMap t2 <*> go synMap t3 

      goC synMap (MSub ts1 ts2) =
        MSub <$> go synMap ts1 <*> traverse (go synMap) ts2 
      
      go _synMap (TyVar x) = return (TyVar x)
      go synMap (TyForAll ns t) =
        TyForAll ns <$> goQ synMap t
      go _synMap (TyMetaV m) = return (TyMetaV m)      
      go synMap (TySyn origTy actualTy) =
        TySyn origTy <$> go synMap actualTy
      go synMap orig@(TyCon c ts) = 
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

  -- withVar x ty mult = 
  --   local (\tc -> tc { tcTyEnv = M.insert x (ty, mult) (tcTyEnv tc) }) 

  pushLevel =
    local (\tc -> tc { tcTcLevel = succ (tcTcLevel tc) })

  withVar x ty =
    local (\tc -> tc { tcTyEnv = M.insert x ty (tcTyEnv tc) })

  withSyn tv v = 
    local (\tc -> tc { tcSyn = M.insert tv v (tcSyn tc) }) 

  -- getMetaTyVarsInEnv = do
  --   tyEnv <- asks tcTyEnv
  --   let ts = concatMap (\(t,m) -> [t,m]) $ M.elems tyEnv
  --   ts' <- mapM zonkType ts
  --   return $ metaTyVars ts' -- (ts ++ multEnv)


newMetaTy :: MonadTypeCheck m => m Ty
newMetaTy = TyMetaV <$> newMetaTyVar 

-- withVars :: MonadTypeCheck m => [ (Name, Ty, MultTy) ] -> m r -> m r
-- withVars ns m = foldr (\(n,t,mult) -> withVar n t mult) m ns

-- withMultVar :: MonadTypeCheck m => MultTy -> m r -> m r
-- withMultVar mult = withVar dummyName mult mult 

-- withMultVars :: MonadTypeCheck m => [MultTy] -> m r -> m r
-- withMultVars ms m = foldr withMultVar m ms 

withVars :: MonadTypeCheck m => [ (Name, Ty) ] -> m r -> m r
withVars ns m = foldr (\(n,t) -> withVar n t) m ns 

-- withUnrestrictedVars :: MonadTypeCheck m => [ (Name, Ty) ] -> m r -> m r
-- withUnrestrictedVars = withVars . map (\(n,t) -> (n, t, TyMult Omega))

withSyns :: MonadTypeCheck m => [ (Name, ([TyVar], Ty)) ] -> m r -> m  r
withSyns xs m = foldr (uncurry withSyn) m xs  

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
  TyCon c <$> traverse zonkType ts
zonkType (TyForAll ns t) =
  TyForAll ns <$> zonkTypeQ t
zonkType (TyMetaV m) = zonkMetaTyVar m
zonkType (TySyn origTy ty) =
  TySyn <$> zonkType origTy <*> zonkType ty 
zonkType (TyMult m) = return (TyMult m) 

zonkTypeQ :: MonadTypeCheck m => QualTy -> m QualTy
zonkTypeQ (TyQual cs t) = TyQual <$> traverse zonkTypeC cs <*> zonkType t

zonkTypeC :: MonadTypeCheck m => TyConstraint -> m TyConstraint
zonkTypeC (MSub t1 ts2) = MSub <$> zonkType t1 <*> traverse zonkType ts2 

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
  CheckingConstraint <$> traverse zonkTypeC cs
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
      go ts r = foldr (goT []) r ts

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
      goC bound (MSub t1 ts2) r = goT bound t1 (foldr (goT bound) r ts2) 
--       goC bound (MEqMax t1 t2 t3) r = goT bound t1 $ goT bound t2 $ goT bound t3 r 


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
  lv  <- readTcLevelMv mv
  lv2 <- readTcLevelMv mv2 
  case res of
    Nothing   ->
      if | mv == mv2 -> return ()
         | lv < lv2 ->
             writeTyVar mv2 (TyMetaV mv) 
         | otherwise -> 
           writeTyVar mv (TyMetaV mv2) 
    Just ty2' -> unifyUnboundMetaTyVar mv ty2' 
unifyUnboundMetaTyVar mv ty2 = do 
  ty2' <- zonkType ty2
  let mvs = metaTyVars [ty2']
  if mv `elem` mvs 
    then do
      reportError $ OccurrenceCheck mv ty2'
      -- We abort typing when occurrence check fails; otherwise, zonkType can diverge. 
      abortTyping 
    else do
      lvl <- readTcLevelMv mv
      ty2'LevelAdjusted <- capLevel lvl ty2' 
      writeTyVar mv ty2'LevelAdjusted

        
