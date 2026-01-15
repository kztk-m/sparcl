{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TupleSections   #-}

module Language.Sparcl.Typing.TCMonad where

import           Data.List                      (foldl')
import           Data.Map                       (Map)
import qualified Data.Map                       as M
import           Data.Map.Merge.Lazy            as M
import           Data.Sequence                  (Seq)
import qualified Data.Sequence                  as Seq

import           Data.Semigroup                 (Max (..), Min (..))

import           Data.Foldable                  (toList)
import           Data.IORef

import           Text.Printf

import           Control.Monad
import           Control.Monad.Reader
-- import Control.Monad.Except
-- import Control.Exception (evaluate, Exception, throw, catch)
import           Control.Monad.Catch

import           Language.Sparcl.Exception
import           Language.Sparcl.Multiplicity
import           Language.Sparcl.Name
import           Language.Sparcl.Pass
import           Language.Sparcl.Pretty         hiding ((<$>))
import qualified Language.Sparcl.Pretty         as D
import           Language.Sparcl.SrcLoc
import qualified Language.Sparcl.Surface.Syntax as S
import           Language.Sparcl.Typing.Type

import qualified Language.Sparcl.Class          as C

import           Language.Sparcl.DebugPrint

import           System.Clock

data AbortTyping = AbortTyping
  deriving Show
instance Exception AbortTyping


data WhenChecking = CheckingEquality    !Ty !Ty
                  | CheckingConstraint  ![TyConstraint]
                  | CheckingMoreGeneral !Ty !Ty
                  | OtherContext        !Doc
                  | CheckingNone


data TypeError = TypeError !(Maybe SrcSpan) ![S.LExp 'Renaming] !WhenChecking !ErrorDetail

data ErrorDetail
  = UnMatchTy   !Ty !Ty
  | OccurrenceCheck !MetaTyVar !Ty
  | MultipleUse !Name
  | NoUse       !Name
  | Undefined   !Name
  | Untouchable !MetaTyVar !Ty
  | ImplicationCheckFail ![TyConstraint] ![TyConstraint]
  | Escape      !MetaTyVar !Ty
  | GeneralizeFail !Ty !Ty ![TyVar]
  | Other       !D.Doc


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
            D.hsep [ D.text "Unbound", ppr v ]

          -- TODO: Show what guards the unifnication
          go (Untouchable mv ty) =
            D.vcat [ D.text "Cannot unify" <+> ppr mv <+> text "with" <+> ppr ty,
                     D.text "because variable" <+> ppr mv <+> text "is untouchable" ]
          go (ImplicationCheckFail cs cs') =
            D.vcat [ D.text "Cannot deduce" <+> ppr cs'
                   , D.text "under" <+> ppr cs ]


          go (Escape mv ty) =
            D.vcat [ text "Cannot unify:" <+> ppr mv <+> text "with" <+> ppr ty,
                     text "because skolemized variable(s)" <+> hsep (punctuate comma $ map ppr sks) <+> text "escape." ]
            where sks = [ s | s@(SkolemTv _ _ _) <- S.freeTyVars ty ]

          go (GeneralizeFail ty1 ty2 escapedMetaVars) =
            D.hcat [ D.text "The inferred type",
                     D.nest 2 (D.line D.<> D.dquotes (D.align $ ppr ty1)),
                     D.line <> D.text "is not polymorphic enough for:",
                     D.nest 2 (D.line D.<> D.dquotes (D.align $ ppr ty2)),
                     D.line <> D.text "because variable(s)" <+> hsep (punctuate comma $ map ppr escapedMetaVars) <+> text "are monomorphic."
                   ]

          go (Other d) = d

      pprContexts []     = D.empty
      pprContexts [e]    = pprContext e
      pprContexts (e:es) = pprContext e D.<$> pprContexts es

      pprContext e =
        D.text "In:" D.<+> ppr (location e)
        D.<> D.nest 2 (D.line D.<> ppr e)



-- A typing environment just holds type information.  This reflects
-- our principle; multiplicites are synthesized instead of checked.
type TyEnv  = Map Name Ty
type ConEnv = Map Name ConTy

dummyName :: Name
dummyName = Original (ModuleName "") (User "") (Bare (User ""))

-- A usage environment gathers how many times a variable is used.
--
-- Storing multiplicity variable is necessarly for application for a
-- function of type a # p -> b to an expression that variables used in
-- the expression has multiplicity `p` if it were used one.
type UseMap = Map Name Multiplication

data Multiplication = Multiply !Multiplication !Multiplication
                    | MSingle  !Mul

instance MultiplicityLike Multiplication where
  one   = MSingle one
  omega = MSingle omega
  fromMultiplicity = MSingle . fromMultiplicity

instance Lub Multiplication where
  lub (MSingle (MulConst Omega)) _ = MSingle (MulConst Omega)
  lub (MSingle (MulConst One))   t = t
  lub _ (MSingle (MulConst Omega)) = MSingle (MulConst Omega)
  lub t (MSingle (MulConst One))   = t
  lub t1 t2                        = Multiply t1 t2

ty2mult :: MonadTypeCheck m => MultTy -> m Multiplication
ty2mult = zonkType >=> go
    where
      go (TyMult t)  = return $ MSingle (MulConst t)
      go (TyMetaV t) = return $ MSingle (MulVar t)
      go _           = do
        reportError $ Other $ text "Expected multiplicity"
        m <- newMetaTyVar
        return $ MSingle (MulVar m)

data Mul = MulConst !Multiplicity | MulVar !MetaTyVar

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


data InferredConstraint
  = ICNormal  !TyConstraint
  | ICGuarded ![TyConstraint]       -- Given
              ![InferredConstraint] -- Wanted


instance MetaTyVars InferredConstraint where
  metaTyVarsGen f (ICNormal  t)      = metaTyVarsGen f t
  metaTyVarsGen f (ICGuarded cs ics) = metaTyVarsGen f (cs, ics)

instance Pretty InferredConstraint where
  ppr (ICNormal tc) = ppr tc
  ppr (ICGuarded cs ics) =
    angles (ppr cs <+> text "==>" <+> ppr ics)



type TypeErrorContext = ([S.LExp 'Renaming], WhenChecking)

data SuspendedCheck =
  SuspendedCheck { scCheck    :: forall m. MonadTypeCheck m => m () }


data BenchInfo = BenchInfo { biCount :: !Int,     -- the number of total check happened
                             biTotal :: !Integer  -- the total elapsed time (in nano sec)
                           }

-- We may want to count some informations depending on keys.
type BMap = M.Map String BenchInfo


pprBi :: BenchInfo -> Doc
pprBi bi =
  let elapsedInNanoSecs :: Double = fromIntegral (biTotal bi) / (10 ** 6)
  in text "#happened" <+> ppr (biCount bi) <+> text "/" <+> text "elapsed(ms)" <+> text (printf "%2.4f" elapsedInNanoSecs)

pprBMap :: BMap -> Doc
pprBMap bm =
  vcat $ map (\(k,v) -> text "Ev" <+> text k <> text ":" <+> pprBi v) $ M.toList bm


resetBench :: (MonadIO m, C.Has KeyTC TypingContext m) => m ()
resetBench = do
  tc <- C.ask (C.key @KeyTC)
  liftIO $ writeIORef (tcBLog tc) M.empty


reportBench :: (MonadIO m, C.Has KeyTC TypingContext m) => m ()
reportBench = do
  tc <- C.ask (C.key @KeyTC)
  bm <- liftIO $ readIORef (tcBLog tc)

  liftIO $ putStrLn "-- report --"
  liftIO $ print $ pprBMap bm


-- the following information is used. The information is kept globally.
data TypingContext =
  TypingContext { tcRefMvCount :: !(IORef Int),
                  tcRefSvCount :: !(IORef Int),
                  tcTcLevel    :: !TcLevel,
                  tcIcLevel    :: !IcLevel,
                  tcConstraint :: !(IORef [InferredConstraint]),
                  tcBLog       :: !(IORef BMap),
                  tcTyEnv      :: !TyEnv,    -- Current typing environment
                  tcConEnv     :: !ConEnv,
                  tcSyn        :: !SynTable, -- Current type synonym table
                  tcContexts   :: ![S.LExp 'Renaming], -- parent expressions
                  tcLoc        :: !(Maybe SrcSpan),  -- focused part
                  tcChecking   :: !WhenChecking,
                  tcDebugLevel :: !Int,
                  tcRefErrors  :: !(IORef (Seq TypeError)),
                  tcDeferredIC :: !(IORef [(TypeErrorContext, SuspendedCheck)])
                               -- Type errors are accumulated for better error messages
                  }

data KeyTC


initTypingContext :: IO TypingContext
initTypingContext = do
  r1 <- newIORef 0
  r2 <- newIORef 0
  r  <- newIORef Seq.empty
  rc <- newIORef []
  ric <- newIORef []
  rbm <- newIORef M.empty
  return TypingContext { tcRefMvCount = r1,
                         tcRefSvCount = r2,
                         tcIcLevel = 0,
                         tcTcLevel    = 0 ,
                         tcRefErrors  = r ,
                         tcConstraint = rc,
                         tcLoc        = Nothing,
                         tcContexts   = [],
                         tcChecking   = CheckingNone,
                         tcDebugLevel = 0,
                         tcConEnv = M.empty,
                         tcTyEnv      = M.empty,
                         tcSyn        = M.empty,
                         tcBLog       = rbm,
                         tcDeferredIC = ric }

-- This function must be called before each session of type checking.
refreshTC :: TypingContext -> IO TypingContext
refreshTC tc = do
  r <- newIORef Seq.empty
  rc <- newIORef []
  ric <- newIORef []
  return $ tc { tcTyEnv     = M.empty,
                tcConEnv    = M.empty,
                tcSyn       = M.empty,
                tcLoc       = Nothing,
                tcConstraint = rc,
                tcRefErrors = r,
                tcChecking  = CheckingNone,
                tcContexts  = [],
                tcDeferredIC = ric}

setEnvs :: TypingContext -> ConEnv -> TypeTable -> SynTable -> TypingContext
setEnvs tc kenv tenv syn =
  tc { tcConEnv = kenv,
       tcTyEnv = tenv,
       tcSyn   = syn }

setDebugLevel :: TypingContext -> Int -> TypingContext
setDebugLevel tc lv = tc { tcDebugLevel = lv }


type MonadTypeCheck m =
  (C.Has KeyDebugLevel Int m,
   C.Local KeyTC TypingContext m,
   MonadIO m,
   MonadCatch m)


-- | A concrete instance of 'MonadTypeCheck'
--
--   Currently, @ask (key \@KeyDebugLevel)@ always returns @0@.
newtype SimpleTC a = SimpleTC (ReaderT TypingContext IO a)
  deriving (Functor, Applicative, Monad, MonadIO, MonadThrow, MonadCatch)

runSimpleTC :: TypingContext -> SimpleTC a -> IO a
runSimpleTC tc (SimpleTC m) = runReaderT m tc

instance C.Has KeyDebugLevel Int SimpleTC where
  ask _ = return 0

instance C.Has KeyTC TypingContext SimpleTC where
  ask _ = SimpleTC $ ReaderT $ \tc -> return tc

instance C.Local KeyTC TypingContext SimpleTC where
  local _ f (SimpleTC m) = SimpleTC $ local f m

runTC :: MonadTypeCheck m => m a -> m a
runTC m = do
  res <- m `catch` (\(_ :: AbortTyping) -> do
                        return undefined)
  tc   <- C.ask (C.key @KeyTC)
  errs <- liftIO $ readIORef (tcRefErrors tc)
  if not (Seq.null errs)
    then do
    errs' <- mapM zonkTypeError $ toList errs
    staticError $ vcat (map ppr errs')
    else do
    return res

logBench :: MonadTypeCheck m => String -> m a -> m a
logBench key comp = logBenchN key 1 comp

logBenchN :: MonadTypeCheck m => String -> Int -> m a -> m a
logBenchN key cnt comp = do
  tc  <- C.ask (C.key @KeyTC)

  !s <- liftIO $ getTime Monotonic
  !r <- comp
  !e <- liftIO $ getTime Monotonic

  let diff = toNanoSecs (e `diffTimeSpec` s)


  liftIO $ modifyIORef (tcBLog tc) $ M.insertWith mrg key (BenchInfo cnt diff)

  return r
  where
    mrg (BenchInfo i m) (BenchInfo i' m') = BenchInfo (i + i') (m + m')



runTCWith :: MonadTypeCheck m => CTypeTable -> TypeTable -> SynTable -> m a -> m a
runTCWith ctbl tytbl syntbl m = do
  tc <- C.ask (C.key @KeyTC)
  tc' <- liftIO $ refreshTC tc
  C.local (C.key @KeyTC) (\_ -> setEnvs tc' ctbl tytbl syntbl) $ runTC m


tupleConTy :: Int -> ConTy
tupleConTy n =
  let tvs = map BoundTv [ Alpha i (User $ 't':show i) | i <- [1..n] ]
      tys = map TyVar tvs
  in -- ConTy tvs [] [] $ foldr (-@) (tupleTy tys) tys
    ConTy tvs [] [] [ (t , one) | t <- tys ] (tupleTy tys)
--  in TyForAll tvs $ TyQual [] $ foldr (-@) (tupleTy tys) tys

arbitraryTy :: MonadTypeCheck m => m Ty
arbitraryTy = TyMetaV <$> newMetaTyVar


abortTyping :: MonadTypeCheck m => m a
abortTyping = throwM AbortTyping

reportError :: MonadTypeCheck m => ErrorDetail -> m ()
reportError mes = do
  tc <- C.ask (C.key @KeyTC)
  let err = TypeError (tcLoc tc) (tcContexts tc) (tcChecking tc) mes
  liftIO $ modifyIORef (tcRefErrors tc) $ \s -> s Seq.:|> err

whenChecking ::  MonadTypeCheck m => WhenChecking -> m a -> m a
whenChecking t =
  C.local (C.key @KeyTC) (\tc -> tc { tcChecking = t })

whatIsChecking :: MonadTypeCheck m => m WhenChecking
whatIsChecking = C.asks (C.key @KeyTC) tcChecking

restoreTypeErrorContext :: MonadTypeCheck m => TypeErrorContext -> m r -> m r
restoreTypeErrorContext (exps, wc) m =
  C.local (C.key @KeyTC) (\tc -> tc { tcContexts = exps, tcChecking = wc }) m

currentTypeErrorContext :: MonadTypeCheck m => m TypeErrorContext
currentTypeErrorContext = do
  wc <- C.asks (C.key @KeyTC) tcChecking
  es <- C.asks (C.key @KeyTC) tcContexts
  return (es, wc)

atLoc :: MonadTypeCheck m => SrcSpan -> m a -> m a
atLoc NoLoc = id
atLoc loc   = C.local (C.key @KeyTC) (\tc -> tc { tcLoc = Just loc })

atExp :: MonadTypeCheck m => S.LExp 'Renaming -> m r -> m r
atExp e = C.local (C.key @KeyTC) (\tc -> tc { tcContexts = e : tcContexts tc })

askCurrentTcLevel :: MonadTypeCheck m => m TcLevel
askCurrentTcLevel = C.asks (C.key @KeyTC) tcTcLevel

readConstraint :: MonadTypeCheck m => m [InferredConstraint]
readConstraint = do
  csRef <- C.asks (C.key @KeyTC) tcConstraint
  liftIO $ readIORef csRef

addConstraint :: MonadTypeCheck m => [TyConstraint] -> m ()
addConstraint cs = do
  csRef <- C.asks (C.key @KeyTC) tcConstraint
  liftIO $ modifyIORef csRef (map ICNormal cs ++)

addImpConstraint :: MonadTypeCheck m => [TyConstraint] -> [InferredConstraint] -> m ()
addImpConstraint cs ics = do
  csRef <- C.asks (C.key @KeyTC) tcConstraint
  liftIO $ modifyIORef csRef (ICGuarded cs ics :)


setConstraint :: MonadTypeCheck m => [InferredConstraint] -> m ()
setConstraint cs = do
  csRef <- C.asks (C.key @KeyTC) tcConstraint
  liftIO $ writeIORef csRef cs

gatherConstraint :: MonadTypeCheck m => m a -> m (a, [InferredConstraint])
gatherConstraint m = do
  csPrev <- readConstraint
  setConstraint []
  res <- m
  cs <- readConstraint
  setConstraint csPrev
  return (res, cs)

askConTypeMaybe :: MonadTypeCheck m => Name -> m (Maybe ConTy)
askConTypeMaybe n
  | Just k <- checkNameTuple n =
      return $ Just (tupleConTy k)
  | otherwise = do
      conEnv <- C.asks (C.key @KeyTC) tcConEnv
      return (M.lookup n conEnv)

askConType :: MonadTypeCheck m => SrcSpan -> Name -> m ConTy
askConType loc n = do
  res <- askConTypeMaybe n
  case res of
    Just cty -> return cty
    Nothing  -> do
      atLoc loc (reportError $ Undefined n)
      abortTyping

askType :: MonadTypeCheck m => SrcSpan -> Name -> m Ty
askType l n = do
  res <- askConTypeMaybe n
  case res of
    Just cty -> return (conTy2Ty cty)
    Nothing  -> do
      tyEnv <- C.asks (C.key @KeyTC) tcTyEnv
      case M.lookup n tyEnv of
        Just ty -> do
          ty' <- zonkType ty
          -- debugPrint 4 $ ppr n <+> text ":" <+> ppr ty'
          return ty'
        Nothing -> do
          atLoc l (reportError $ Undefined n)
          arbitraryTy

newMetaTyVar :: MonadTypeCheck m => m MetaTyVar
newMetaTyVar = do
  cref <- C.asks (C.key @KeyTC) tcRefMvCount
  lv   <- C.asks (C.key @KeyTC) tcTcLevel
  ilv  <- C.asks (C.key @KeyTC) tcIcLevel
  cnt <- liftIO $ atomicModifyIORef' cref $ \cnt -> (cnt + 1, cnt)
  ref <- liftIO $ newIORef Nothing
  lref <- liftIO $ newIORef lv
  return $ MetaTyVar cnt ref lref ilv

readTyVar :: MonadTypeCheck m => MetaTyVar -> m (Maybe Ty)
readTyVar mv =
  liftIO $ readIORef (metaRef mv)

writeTyVar :: MonadTypeCheck m => MetaTyVar -> Ty -> m ()
writeTyVar mv ty =
  liftIO $ writeIORef (metaRef mv) (Just ty)


newSkolemTyVar :: MonadTypeCheck m => TyVar -> m TyVar
newSkolemTyVar ty = do
  cref <- C.asks (C.key @KeyTC) tcRefSvCount
  ilv  <- C.asks (C.key @KeyTC) tcIcLevel
  cnt <- liftIO $ atomicModifyIORef' cref $ \cnt -> (cnt + 1, cnt)
  return $ SkolemTv ty cnt ilv

defer :: MonadTypeCheck m => SuspendedCheck -> m ()
defer sc = do
  ref <- C.asks (C.key @KeyTC) tcDeferredIC
  tec <- currentTypeErrorContext
  liftIO $ modifyIORef ref $ ((tec, sc):)


resolveSyn :: MonadTypeCheck m => Ty -> m Ty
resolveSyn ty = do
  synMap <- C.asks (C.key @KeyTC) tcSyn
  go synMap ty
    where
      goQ synMap (TyQual cs t) =
        TyQual <$> mapM (goC synMap) cs <*> go synMap t

      -- goC synMap (MEqMax t1 t2 t3) =
      --   MEqMax <$> go synMap t1 <*> go synMap t2 <*> go synMap t3

      goC synMap (MSub ts1 ts2) =
        MSub <$> go synMap ts1 <*> traverse (go synMap) ts2
      goC synMap (TyEq t1 t2) =
        TyEq <$> go synMap t1 <*> go synMap t2

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

currentLevel :: MonadTypeCheck m => m TcLevel
currentLevel = do
  C.asks (C.key @KeyTC) tcTcLevel

pushLevel :: MonadTypeCheck m => m a -> m a
pushLevel m = do
  -- perform computation.
  res <- C.local (C.key @KeyTC) (\tc -> tc { tcTcLevel = succ (tcTcLevel tc) }) m


  tref <- C.asks (C.key @KeyTC) tcDeferredIC
  -- deferred
  deferred <- liftIO $ readIORef tref

  debugPrint 4 $ red $ text "#deferred checks:" <+> (ppr $ length deferred)

  procDeferred deferred

  return res
  where
    procDeferred []            = return ()
    procDeferred ((tyc, q):qs) = do
      restoreTypeErrorContext tyc $ scCheck q
      procDeferred qs


currentIcLevel :: MonadTypeCheck m => m IcLevel
currentIcLevel =
  C.asks (C.key @KeyTC) tcIcLevel

pushIcLevel :: MonadTypeCheck m => m a -> m a
pushIcLevel = localIcLevel succ

localIcLevel :: MonadTypeCheck m => (IcLevel -> IcLevel) -> m a -> m a
localIcLevel f =
  C.local (C.key @KeyTC) $ \tc -> tc { tcIcLevel = f (tcIcLevel tc) }


withVar :: MonadTypeCheck m => Name -> Ty -> m a -> m a
withVar x ty =
  C.local (C.key @KeyTC) (\tc -> tc { tcTyEnv = M.insert x ty (tcTyEnv tc) })

withSyn :: MonadTypeCheck m => Name -> ([TyVar], Ty) -> m r -> m r
withSyn tv v =
  C.local (C.key @KeyTC) (\tc -> tc { tcSyn = M.insert tv v (tcSyn tc) })

withCon :: MonadTypeCheck m => Name -> ConTy -> m a -> m a
withCon c ty =
  C.local (C.key @KeyTC) (\tc -> tc { tcConEnv = M.insert c ty (tcConEnv tc) })


newMetaTy :: MonadTypeCheck m => m Ty
newMetaTy = TyMetaV <$> newMetaTyVar

withVars :: MonadTypeCheck m => [ (Name, Ty) ] -> m r -> m r
withVars ns m = foldr (uncurry withVar) m ns

withCons :: MonadTypeCheck m => [ (Name, ConTy) ] -> m r -> m r
withCons ns m = foldr (uncurry withCon) m ns

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
zonkTypeC (TyEq t1 t2)  = TyEq <$> zonkType t1 <*> zonkType t2

zonkTypeIC :: MonadTypeCheck m => InferredConstraint -> m InferredConstraint
zonkTypeIC (ICNormal c) = ICNormal <$> zonkTypeC c
zonkTypeIC (ICGuarded cs ics) = ICGuarded <$> mapM zonkTypeC cs <*> mapM zonkTypeIC ics

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
zonkErrorDetail (ImplicationCheckFail cs cs') =
  ImplicationCheckFail <$> mapM zonkTypeC cs <*> mapM zonkTypeC cs'
zonkErrorDetail (Untouchable m t) =
  Untouchable <$> pure m <*> zonkType t
zonkErrorDetail (GeneralizeFail ty1 ty2 tyvs) =
  GeneralizeFail <$> zonkType ty1 <*> zonkType ty2 <*> pure tyvs
zonkErrorDetail res = pure res


unify :: MonadTypeCheck m => MonoTy -> MonoTy -> m ()
unify ty1 ty2 = do
  ty1' <- resolveSyn ty1
  ty2' <- resolveSyn ty2
  unifyWork ty1' ty2'

unifyWork :: MonadTypeCheck m => MonoTy -> MonoTy -> m ()
unifyWork (TySyn _ t1) t2 = unifyWork t1 t2
unifyWork t1 (TySyn _ t2) = unifyWork t1 t2
unifyWork (TyMetaV mv1) (TyMetaV mv2) | mv1 == mv2 = return ()
unifyWork (TyMetaV mv) ty = unifyMetaTyVar mv ty
unifyWork ty (TyMetaV mv) = unifyMetaTyVar mv ty
unifyWork (TyCon c ts) (TyCon c' ts') | c == c' = do
                                          when (length ts /= length ts') $
                                            reportError $ Other $ D.hsep [D.text "Type construtor", ppr c, D.text "has different number of arguments."]
                                          zipWithM_ unifyWork ts ts'
unifyWork (TyMult m) (TyMult m') | m == m' = return ()
unifyWork (TyVar x1) (TyVar x2)       | x1 == x2 = return ()
unifyWork (TyVar x) t = addConstraint [TyEq (TyVar x) t]
unifyWork t (TyVar x) = addConstraint [TyEq t (TyVar x)]
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

shouldBeSwapped :: MonadTypeCheck m => MetaTyVar -> MetaTyVar -> m Bool
shouldBeSwapped mv1 mv2 = do
  lv1 <- readTcLevelMv mv1
  lv2 <- readTcLevelMv mv2
  return $ if | metaIcLevel mv1 < metaIcLevel mv2 ->
                -- NB: mv1 := mv2 is possible a's IC-level is equivalent or greater to the current.
                -- Thus, this swapping increases chance for the substitution to succeed.
                True
              | lv1 < lv2 ->
                -- No technical reason, but we prioritise outer level variables to survive.
                True
              | otherwise ->
                False



unifyUnboundMetaTyVar :: MonadTypeCheck m => MetaTyVar -> MonoTy -> m ()
unifyUnboundMetaTyVar mv (TyMetaV mv2) = do
  res <- readTyVar mv2
  sw  <- shouldBeSwapped mv mv2
  cIcLevel <- C.asks (C.key @KeyTC) tcIcLevel
  case res of
    Nothing   ->
      if | mv == mv2 -> return ()
         | sw ->
             substituteUnif cIcLevel mv2 (TyMetaV mv)
         | otherwise ->
             substituteUnif cIcLevel mv (TyMetaV mv2)
    Just ty2' -> unifyUnboundMetaTyVar mv ty2'
unifyUnboundMetaTyVar mv ty2 = do
  ty2' <- zonkType ty2
  let mvs = metaTyVars [ty2']
  cIcLevel <- C.asks (C.key @KeyTC) tcIcLevel
  if mv `elem` mvs
    then do
      reportError $ OccurrenceCheck mv ty2'
      -- We abort typing when occurrence check fails; otherwise, zonkType can diverge.
      abortTyping
    else do
      substituteUnif cIcLevel mv ty2'


-- Assumption: ty is already zonked.
substituteUnif :: MonadTypeCheck m => IcLevel -> MetaTyVar -> MonoTy -> m ()
-- TODO: Implement escape checking (substituting variables more than the current IC level should be disabled
substituteUnif cIcLevel mv ty
  | metaIcLevel mv < cIcLevel =
    -- keep the constraint to hope that it will be resolved by `given` constraints
    addConstraint [TyEq (TyMetaV mv) ty]
    -- reportError $ Untouchable mv ty
  | metaIcLevel mv <= skIcLevel ty =
    reportError $ Escape mv ty
  | otherwise = do
    debugPrint 4 $ red $ brackets (ppr cIcLevel) <> text "unifying" <+> ppr mv <+> text "with" <+> ppr ty
    lvl <- readTcLevelMv mv
    ty'Adjusted <- capLevel lvl ty
    writeTyVar mv ty'Adjusted

{-# INLINE minimum' #-}
{-# SPECIALIZE INLINE minimum' :: [TcLevel] -> TcLevel #-}
minimum' :: (Ord a, Bounded a) => [a] -> a
minimum' = foldl' min maxBound

newtype MM f a = MM { runMM :: f a }

instance (Applicative f , Monoid a) => Semigroup (MM f a) where
  MM m1 <> MM m2 = MM $ (<>) <$> m1 <*> m2

instance (Applicative f , Monoid a) => Monoid (MM f a) where
  mempty = MM $ pure mempty

tcLevel :: (MonadTypeCheck m, MetaTyVars t) => t -> m TcLevel
tcLevel t =
  getMin <$> (runMM $ metaTyVarsGen (\mv -> MM $ Min <$> liftIO (readTcLevelMv mv)) t)


skIcLevel :: S.FreeTyVars t TyVar => t -> IcLevel
skIcLevel = getMax . S.foldMapVars (\x -> case x of
                                       SkolemTv _ _ lv -> Max lv
                                       _               -> mempty) (\_ m -> m)

