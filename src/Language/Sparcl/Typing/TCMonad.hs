{-# LANGUAGE ConstraintKinds #-}

module Language.Sparcl.Typing.TCMonad where

import Data.List (foldl')
import Data.Map (Map)
import qualified Data.Map as M
import Data.Map.Merge.Lazy as M
import Data.Sequence (Seq)
import qualified Data.Sequence as Seq

import Data.Semigroup (Max (..), Min (..))

import Data.Foldable (toList)
import Data.IORef

import Text.Printf

import Control.Monad
import Control.Monad.Reader

-- import Control.Monad.Except
-- import Control.Exception (evaluate, Exception, throw, catch)
import Control.Monad.Catch

import Language.Sparcl.DebugPrint
import Language.Sparcl.Exception
import Language.Sparcl.Multiplicity
import Language.Sparcl.Name
import Language.Sparcl.Pass
import Language.Sparcl.Pretty hiding ((<$>))
import qualified Language.Sparcl.Pretty as D
import Language.Sparcl.SrcLoc
import qualified Language.Sparcl.Surface.Syntax as S
import Language.Sparcl.Typing.Type

import Data.Maybe (isNothing)
import Data.String (IsString (fromString))
import GHC.Stack
import System.Clock

data AbortTyping = AbortTyping
  deriving Show
instance Exception AbortTyping

data MCContext = MCLinearity | MCUnrestrictedness | MCUnknown

data WhenChecking
  = CheckingEquality !Ty !Ty
  | CheckingConstraint ![TyConstraint]
  | CheckingMoreGeneral !Ty !Ty
  | CheckingMultiplicities Name MCContext ![Ty] ![Ty]
  | CheckingType Name !Ty
  | OtherContext !Doc
  | CheckingNone

data TypeError = TypeError !(Maybe SrcSpan) (Maybe Doc) ![S.LExp 'Renaming] !WhenChecking !ErrorDetail

data ErrorDetail
  = UnMatchTy !Ty !Ty
  | OccurrenceCheck !MetaTyVar !Ty
  | MultipleUse !Name
  | NoUse !Name
  | Undefined !Name
  | Untouchable !MetaTyVar !Ty
  | ImplicationCheckFail ![MetaTyVar] ![TyConstraint] ![TyConstraint]
  | Escape !MetaTyVar !Ty
  | GeneralizeFail !Ty !Ty ![TyVar]
  | CannotHavePolyTy !PolyTy ![TyVar]
  | LessPolymorphic !PolyTy !PolyTy ![TyVar]
  | CannotUnifyPolyTy !MetaTyVar !PolyTy
  | Other !D.Doc

instance Pretty TypeError where
  ppr (TypeError l snippet exprs ctxt doc) =
    -- D.bold (D.text "[TYPE ERROR]") D.<+> D.nest 2
    D.bold (maybe (D.text "<*unknown place*>") ppr l <> text ":" <+> D.red (text "type error"))
      <> line
      <> maybe mempty (<> line <> nest 2 line) snippet
      <> nest
        2
        ( pprDetail doc
            <> pprWhenChecking ctxt
            <> (if null exprs then empty else item (group $ pprContexts (drop (length exprs - 3) exprs)))
        )
    where
      item d = text "-" <+> align d <> line

      pprWhenChecking (CheckingEquality ty1 ty2) =
        D.line
          <> item
            ( D.text "when checking the following types are equivalent:"
                <> D.nest
                  2
                  ( line
                      <> vsep
                        [ hsep [text "Inferred:", align $ ppr ty1]
                        , hsep [text "Expected:", align $ ppr ty2]
                        ]
                  )
            )
      pprWhenChecking (CheckingMoreGeneral ty1 ty2) =
        D.line
          <> item
            ( D.text "when checking the inferred type is more general than the expected."
                <> D.nest
                  2
                  ( line
                      <> vsep
                        [ hsep [text "Inferred:", align $ ppr ty1]
                        , hsep [text "Expected:", align $ ppr ty2]
                        ]
                  )
            )
      pprWhenChecking (CheckingConstraint cs) =
        D.line
          <> item
            ( D.text "when checking constraints:"
                D.<$> D.parens (hsep $ punctuate comma $ map ppr cs)
            )
      pprWhenChecking (CheckingMultiplicities x _mc used provided) =
        D.line
          <> item
            ( D.text "when checking multiplicity of" <+> ppr x
                <> D.nest 2 (line <> vsep [hsep [text "Given:", align $ pprMults provided], hsep [text "Used: ", align $ pprMults used]])
            )
        where
          pprMults [] = text "One"
          pprMults ms = hcat $ punctuate (text "*") (map ppr ms)
      pprWhenChecking (OtherContext d) =
        D.line
          <> item (D.text "when checking" <+> d)
      pprWhenChecking (CheckingType n ty) =
        D.line <> item (D.text "when checking if" <+> ppr n <+> text "has type" <+> ppr ty)
      pprWhenChecking CheckingNone = D.empty

      pprDetail = item . go
        where
          go (UnMatchTy ty1 ty2) =
            D.text "Types do not match:"
              D.<+> D.align (ppr ty1)
              D.<+> D.text "/="
              D.<+> D.align (ppr ty2)
          -- pprDetail (UnMatchTyD ty1 ty2 ty1' ty2') =
          --   D.text "Types do not match" D.<> D.nest 2
          --    ( D.line D.<> D.nest 2 (D.sep [D.text "Expected:", D.align (ppr ty1) ]) D.<>
          --      D.line D.<> D.nest 2 (D.sep [D.text "Inferred:", D.align (ppr ty2) ]) )
          --   D.<$> D.text "More precisely, the following types do not match."
          --   <> D.nest 2 (line <> D.align (ppr ty1') D.<+> D.text "/=" D.<+> D.align (ppr ty2'))

          go (OccurrenceCheck mv ty) =
            D.text "Cannot construct an infinite type:"
              D.<$> D.hsep [ppr mv, D.text "=", D.align (ppr ty)]
          go (MultipleUse v) =
            D.hsep [D.text "Variable", ppr v, D.text "must not be used more than once."]
          go (NoUse v) =
            D.hsep [D.text "Variable", ppr v, D.text "must be used at once."]
          go (Undefined v) =
            D.hsep [D.text "Unbound", ppr v]
          -- TODO: Show what guards the unifnication
          go (Untouchable mv ty) =
            D.vcat
              [ D.text "Cannot unify" <+> ppr mv <+> text "with" <+> ppr ty
              , D.text "because variable" <+> ppr mv <+> text "is untouchable"
              ]
          go (ImplicationCheckFail ex cs cs') =
            D.vcat
              [ D.text "Cannot deduce" <+> ppr cs'
              , D.text "under" <+> ppr cs
              , if null ex then mempty else D.text "with arbitrary choice of " <+> hsep (punctuate comma $ map ppr ex)
              ]
          go (Escape mv ty) =
            D.vcat
              [ text "Cannot unify:" <+> ppr mv <+> text "with" <+> ppr ty
              , text "because skolem variable(s)" <+> hsep (punctuate comma $ map ppr sks) <+> text "escape."
              ]
            where
              sks = [s | s@(SkolemTv _ _ _) <- S.freeTyVars ty]
          go (GeneralizeFail ty1 ty2 _escapedMetaVars) =
            D.hcat
              [ D.text "The inferred type"
              , D.nest 2 (D.line D.<> D.align (ppr ty1))
              , D.line <> D.text "is not polymorphic enough for:"
              , D.nest 2 (D.line D.<> D.align (ppr ty2))
              -- , D.line <> D.text "because variable(s)" <+> hsep (punctuate comma $ map ppr escapedMetaVars) <+> text "are monomorphic."
              ]
          go (LessPolymorphic ty1 ty2 escaped) =
            D.hcat
              [ D.text "Type"
              , D.nest 2 (D.line D.<> D.align (ppr ty1))
              , D.line <> D.text "is less polymorphic than"
              , D.nest 2 (D.line D.<> D.align (ppr ty2))
              , D.line <> D.text "because skolem variable(s)" <+> hsep (punctuate comma $ map ppr escaped) <+> text "escape."
              ]
          go (CannotHavePolyTy polyTy escaped) =
            D.hcat
              [ D.text "the expression cannot have the given type"
              , D.nest 2 (D.line <> D.dquotes (D.align $ ppr polyTy))
              , D.line <> D.text "as skolemized variables(s)" <+> hsep (punctuate comma $ map ppr escaped) <+> text "escape."
              ]
          go (CannotUnifyPolyTy mv polyTy) =
            D.hcat
              [ D.text "Cannot unify polytype"
              , D.nest 2 (D.line <> D.align (ppr polyTy))
              , D.line <> D.text "with an unification variable" <+> ppr mv
              ]
          go (Other d) = d

      pprContexts [] = D.empty
      pprContexts [e] = pprContext e
      pprContexts (e : es) = pprContext e D.<$> pprContexts es

      pprContext e =
        D.text "In:"
          D.<+> ppr (location e)
          D.<> D.nest 2 (D.line D.<> ppr e)

-- A typing environment just holds type information.  This reflects
-- our principle; multiplicites are synthesized instead of checked.
type TyEnv = Map Name Ty
type ConEnv = Map Name ConTy

dummyName :: Name
dummyName = Original (ModuleName "") (User "") (Bare (User ""))

-- A usage environment gathers how many times a variable is used.
--
-- Storing multiplicity variable is necessarly for application for a
-- function of type a # p -> b to an expression that variables used in
-- the expression has multiplicity `p` if it were used one.
type UseMap = Map Name Multiplication

data Multiplication
  = Multiply !Multiplication !Multiplication
  | MSingle !Mul

instance MultiplicityLike Multiplication where
  one = MSingle one
  omega = MSingle omega
  fromMultiplicity = MSingle . fromMultiplicity

instance Lub Multiplication where
  lub (MSingle (MulConst Omega)) _ = MSingle (MulConst Omega)
  lub (MSingle (MulConst One)) t = t
  lub _ (MSingle (MulConst Omega)) = MSingle (MulConst Omega)
  lub t (MSingle (MulConst One)) = t
  lub t1 t2 = Multiply t1 t2

ty2mult :: MultTy -> TC Multiplication
ty2mult = zonkType >=> go
  where
    go (TyMult t) = return $ MSingle (MulConst t)
    go (TyMetaV t) = return $ MSingle (MulVar t)
    go (TyVar t) = pure $ MSingle (MulVarRigid t)
    go t = do
      reportError $ Other $ text "Expected multiplicity, but received" <+> ppr t
      m <- newMetaTyVar
      return $ MSingle (MulVar m)

data Mul = MulConst !Multiplicity | MulVar !MetaTyVar | MulVarRigid !TyVar

instance MultiplicityLike Mul where
  one = MulConst One
  omega = MulConst Omega
  fromMultiplicity = MulConst

m2ty :: Multiplication -> [Ty]
m2ty ms = case go ms [] of
  Nothing -> [omega]
  Just v -> v
  where
    go :: Multiplication -> [Ty] -> Maybe [Ty]
    go (Multiply t1 t2) r = go t1 =<< go t2 r
    go (MSingle m) r =
      case m of
        MulConst Omega -> Nothing
        MulConst One -> return r
        MulVar t -> return (TyMetaV t : r)
        MulVarRigid t -> pure (TyVar t : r)

singletonUseMap :: Name -> UseMap
singletonUseMap n = M.singleton n one

lookupUseMap :: Name -> UseMap -> Maybe Multiplication
lookupUseMap = M.lookup

multiplyUseMap :: UseMap -> UseMap -> UseMap
multiplyUseMap =
  M.merge
    (M.mapMissing $ \_ _ -> MSingle (MulConst Omega))
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
  = ICNormal !TyConstraint
  | ICGuarded
      !(Maybe SrcSpan)
      -- ^ Source location under which this constraint is produced (for error message)
      !WhenChecking
      -- ^ Context under which this constraint is produced (for error message)
      ![MetaTyVar]
      -- ^ Existential type variables
      ![TyConstraint]
      -- ^ Given
      ![InferredConstraint]
      -- ^ Wanted

instance MetaTyVars InferredConstraint where
  metaTyVarsGen f (ICNormal t) = metaTyVarsGen f t
  metaTyVarsGen f (ICGuarded _ _ ex cs ics) = metaTyVarsGen f (ex, cs, ics)

instance Pretty InferredConstraint where
  ppr (ICNormal tc) = ppr tc
  ppr (ICGuarded _ _ ex cs ics) =
    angles (align $ sep [text "Ex" <+> ppr ex, ppr cs, text "==>", ppr ics])

type TypeErrorContext = ([S.LExp 'Renaming], WhenChecking)

data SuspendedCheck = SuspendedCheck {scCheck :: TC ()}

data BenchInfo = BenchInfo
  { biCount :: !Int -- the number of total check happened
  , biTotal :: !Integer -- the total elapsed time (in nano sec)
  }

-- We may want to count some informations depending on keys.
type BMap = M.Map String BenchInfo

pprBi :: BenchInfo -> Doc
pprBi bi =
  let elapsedInNanoSecs :: Double = fromIntegral (biTotal bi) / (10 ** 6)
  in  text "#happened" <+> ppr (biCount bi) <+> text "/" <+> text "elapsed(ms)" <+> text (printf "%2.4f" elapsedInNanoSecs)

pprBMap :: BMap -> Doc
pprBMap bm =
  vcat $ map (\(k, v) -> text "Ev" <+> text k <> text ":" <+> pprBi v) $ M.toList bm

resetBench :: TC ()
resetBench = do
  tc <- ask
  liftIO $ writeIORef (tcBLog tc) M.empty

reportBench :: TC ()
reportBench = do
  tc <- ask
  bm <- liftIO $ readIORef (tcBLog tc)

  liftIO $ putStrLn "-- report --"
  liftIO $ print $ pprBMap bm

-- the following information is used. The information is kept globally.
data TypingContext
  = TypingContext
  { tcRefMvCount :: !(IORef Int)
  , tcRefSvCount :: !(IORef Int)
  , tcTcLevel :: !TcLevel
  , tcIcLevel :: !IcLevel
  , tcConstraint :: !(IORef [InferredConstraint])
  , tcBLog :: !(IORef BMap)
  , tcTyEnv :: !TyEnv -- Current typing environment
  , tcConEnv :: !ConEnv
  , tcSyn :: !SynTable -- Current type synonym table
  , tcContexts :: ![S.LExp 'Renaming] -- parent expressions
  , tcLoc :: !(Maybe SrcSpan) -- focused part
  , tcChecking :: !WhenChecking
  , tcDebugLevel :: !Int
  , tcRefErrors :: !(IORef (Seq TypeError))
  , tcDeferredIC :: !(IORef [(TypeErrorContext, SuspendedCheck)])
  -- Type errors are accumulated for better error messages
  , tcExpandLast :: !ExpandLast
  -- Whether the spine being checked inserts trailing instance arguments
  -- (as Agda's envExpandLast); see 'ExpandLast'.
  }

-- | Whether trailing instance arguments are inserted after the arguments of
--   an application are used up (as Agda's ExpandHidden). The flag is set by
--   the caller: checking ('Check') sets 'ExpandLast'; plain inference sets
--   'DontExpandLast'; inference of a value that is matched against patterns
--   (the bound expression of @let p <- e1 in e2@, the scrutinee of @case@)
--   sets 'ExpandLast'. Inference passes the flag on to the parts that are
--   the value of the whole (parentheses, the body of @let@, ...).
data ExpandLast = ExpandLast | DontExpandLast
  deriving (Eq, Show)

withExpandLast :: ExpandLast -> TC r -> TC r
withExpandLast e = local (\tc -> tc{tcExpandLast = e})

data KeyTC

initTypingContext :: IO TypingContext
initTypingContext = do
  r1 <- newIORef 0
  r2 <- newIORef 0
  r <- newIORef Seq.empty
  rc <- newIORef []
  ric <- newIORef []
  rbm <- newIORef M.empty
  return
    TypingContext
      { tcRefMvCount = r1
      , tcRefSvCount = r2
      , tcIcLevel = 0
      , tcTcLevel = 0
      , tcRefErrors = r
      , tcConstraint = rc
      , tcLoc = Nothing
      , tcContexts = []
      , tcChecking = CheckingNone
      , tcDebugLevel = 0
      , tcConEnv = M.empty
      , tcTyEnv = M.empty
      , tcSyn = M.empty
      , tcBLog = rbm
      , tcDeferredIC = ric
      , tcExpandLast = DontExpandLast
      }

-- This function must be called before each session of type checking.
refreshTC :: TypingContext -> IO TypingContext
refreshTC tc = do
  r <- newIORef Seq.empty
  rc <- newIORef []
  ric <- newIORef []
  return $
    tc
      { tcTyEnv = M.empty
      , tcConEnv = M.empty
      , tcSyn = M.empty
      , tcLoc = Nothing
      , tcConstraint = rc
      , tcRefErrors = r
      , tcChecking = CheckingNone
      , tcContexts = []
      , tcDeferredIC = ric
      }

setEnvs :: TypingContext -> ConEnv -> TypeTable -> SynTable -> TypingContext
setEnvs tc kenv tenv syn =
  tc
    { tcConEnv = kenv
    , tcTyEnv = tenv
    , tcSyn = syn
    }

setDebugLevel :: TypingContext -> Int -> TypingContext
setDebugLevel tc lv = tc{tcDebugLevel = lv}

-- | A concrete instance of 'MonadTypeCheck'
--
--   Currently, @ask (key \@KeyDebugLevel)@ always returns @0@.
newtype TC a = TC (ReaderT TypingContext IO a)
  deriving (Functor, MonadReader TypingContext, Applicative, Monad, MonadIO, MonadThrow, MonadCatch)

instance MonadFail TC where
  fail s = do
    liftIO $ putStrLn (prettyCallStack callStack)
    cannotHappen (fromString s)

runSimpleTC :: TypingContext -> TC a -> IO a
runSimpleTC tc (TC m) = runReaderT m tc

instance MonadDebug TC where
  askDebugLevel = asks tcDebugLevel

runTC :: TC a -> TC a
runTC m = do
  res <-
    m
      `catch` ( \(_ :: AbortTyping) -> do
                  return undefined
              )
  tc <- ask
  errs <- liftIO $ readIORef (tcRefErrors tc)
  if not (Seq.null errs)
    then do
      errs' <- mapM zonkTypeError $ toList errs
      staticError $ vcat (map ppr errs')
    else do
      return res

execTC :: TypingContext -> TC a -> IO a
execTC tc m | TC m' <- runTC m = runReaderT m' tc

-- Benchmarking
logBench :: String -> TC a -> TC a
logBench key = logBenchN key 1

logBenchN :: String -> Int -> TC a -> TC a
logBenchN key cnt comp = do
  tc <- ask

  !s <- liftIO $ getTime Monotonic
  !r <- comp
  !e <- liftIO $ getTime Monotonic

  let diff = toNanoSecs (e `diffTimeSpec` s)

  liftIO $ modifyIORef (tcBLog tc) $ M.insertWith mrg key (BenchInfo cnt diff)

  return r
  where
    mrg (BenchInfo i m) (BenchInfo i' m') = BenchInfo (i + i') (m + m')

runTCWith :: CTypeTable -> TypeTable -> SynTable -> TC a -> TC a
runTCWith ctbl tytbl syntbl m = do
  tc <- ask
  tc' <- liftIO $ refreshTC tc
  local (\_ -> setEnvs tc' ctbl tytbl syntbl) $ runTC m

execTCWith :: TypingContext -> CTypeTable -> TypeTable -> SynTable -> TC a -> IO a
execTCWith tc ctbl tytbl syntbl m | TC m' <- runTCWith ctbl tytbl syntbl m = runReaderT m' tc

tupleConTy :: Int -> ConTy
tupleConTy n =
  let tvs = map BoundTv [Alpha i (User $ 't' : show i) | i <- [1 .. n]]
      tys = map TyVar tvs
  in  -- ConTy tvs [] [] $ foldr (-@) (tupleTy tys) tys
      ConTy tvs [] [] [(t, one) | t <- tys] (tupleTy tys)

--  in TyForAll tvs $ TyQual [] $ foldr (-@) (tupleTy tys) tys

-- | Make a unifiable type varible
arbitraryTy :: TC Ty
arbitraryTy = TyMetaV <$> newMetaTyVar

abortTyping :: TC a
abortTyping = throwM AbortTyping

-- | Register an error and continue
reportError :: ErrorDetail -> TC ()
reportError mes = do
  tc <- ask
  snippet <- liftIO $ fmap join $ traverse retrieveAndRender (tcLoc tc)
  let err = TypeError (tcLoc tc) snippet (tcContexts tc) (tcChecking tc) mes
  liftIO $ modifyIORef (tcRefErrors tc) $ \s -> s Seq.:|> err

whenChecking :: WhenChecking -> TC a -> TC a
whenChecking t = local (\tc -> tc{tcChecking = t})

whatIsChecking :: TC WhenChecking
whatIsChecking = asks tcChecking

restoreTypeErrorContext :: TypeErrorContext -> TC r -> TC r
restoreTypeErrorContext (exps, wc) = local (\tc -> tc{tcContexts = exps, tcChecking = wc})

currentTypeErrorContext :: TC TypeErrorContext
currentTypeErrorContext = do
  wc <- asks tcChecking
  es <- asks tcContexts
  return (es, wc)

atLoc :: SrcSpan -> TC a -> TC a
atLoc NoLoc = id
atLoc loc = local (\tc -> tc{tcLoc = Just loc})

atExp :: S.LExp 'Renaming -> TC r -> TC r
atExp e = local (\tc -> tc{tcContexts = e : tcContexts tc})

askCurrentTcLevel :: TC TcLevel
askCurrentTcLevel = asks tcTcLevel

readConstraint :: TC [InferredConstraint]
readConstraint = do
  csRef <- asks tcConstraint
  liftIO $ readIORef csRef

addConstraint :: [TyConstraint] -> TC ()
addConstraint cs = do
  csRef <- asks tcConstraint
  liftIO $ modifyIORef csRef (map ICNormal cs ++)

addImpConstraint :: [MetaTyVar] -> [TyConstraint] -> [InferredConstraint] -> TC ()
addImpConstraint ex cs ics = do
  whenC <- asks tcChecking
  srcLoc <- asks tcLoc
  csRef <- asks tcConstraint
  liftIO $ modifyIORef csRef (ICGuarded srcLoc whenC ex cs ics :)

setConstraint :: [InferredConstraint] -> TC ()
setConstraint cs = do
  csRef <- asks tcConstraint
  liftIO $ writeIORef csRef cs

gatherConstraint :: TC a -> TC (a, [InferredConstraint])
gatherConstraint m = do
  csPrev <- readConstraint
  setConstraint []
  res <- m
  cs <- readConstraint
  setConstraint csPrev
  return (res, cs)

askConTypeMaybe :: Name -> TC (Maybe ConTy)
askConTypeMaybe n
  | Just k <- checkNameTuple n =
      return $ Just (tupleConTy k)
  | otherwise = do
      conEnv <- asks tcConEnv
      return (M.lookup n conEnv)

askConType :: SrcSpan -> Name -> TC ConTy
askConType loc n = do
  res <- askConTypeMaybe n
  case res of
    Just cty -> return cty
    Nothing -> do
      atLoc loc (reportError $ Undefined n)
      abortTyping

askType :: SrcSpan -> Name -> TC Ty
askType l n = do
  res <- askConTypeMaybe n
  case res of
    Just cty -> return (conTy2Ty cty)
    Nothing -> do
      tyEnv <- asks tcTyEnv
      case M.lookup n tyEnv of
        Just ty -> do
          ty' <- zonkType ty
          -- debugPrint 4 $ ppr n <+> text ":" <+> ppr ty'
          return ty'
        Nothing -> do
          atLoc l (reportError $ Undefined n)
          arbitraryTy

newMetaTyVar :: TC MetaTyVar
newMetaTyVar = do
  cref <- asks tcRefMvCount
  lv <- asks tcTcLevel
  ilv <- asks tcIcLevel
  cnt <- liftIO $ atomicModifyIORef' cref $ \cnt -> (cnt + 1, cnt)
  ref <- liftIO $ newIORef Nothing
  lref <- liftIO $ newIORef lv
  return $ MetaTyVar cnt ref lref ilv

readTyVar :: MetaTyVar -> TC (Maybe Ty)
readTyVar mv =
  liftIO $ readIORef (metaRef mv)

writeTyVar :: MetaTyVar -> Ty -> TC ()
writeTyVar mv ty =
  liftIO $ writeIORef (metaRef mv) (Just ty)

newSkolemTyVar :: TyVar -> TC TyVar
newSkolemTyVar ty = do
  cref <- asks tcRefSvCount
  ilv <- asks tcIcLevel
  cnt <- liftIO $ atomicModifyIORef' cref $ \cnt -> (cnt + 1, cnt)
  return $ SkolemTv ty cnt ilv

-- | Used to implement bidirectional type checking.
-- @Check t@ means that a term's type is checked against @t@.
-- @Infer alpha@ means that a term's type is inferred to be unified with @alpha@.
data Expected t = Check t | Infer (TCRef Ty)

newtype TCRef a = TCRef (IORef a)

newTCRef :: a -> TC (TCRef a)
newTCRef = fmap TCRef . liftIO . newIORef

readTCRef :: TCRef a -> TC a
readTCRef (TCRef ref) = liftIO (readIORef ref)

writeTCRef :: TCRef a -> a -> TC ()
writeTCRef (TCRef ref) v = liftIO $ writeIORef ref v

defer :: SuspendedCheck -> TC ()
defer sc = do
  ref <- asks tcDeferredIC
  tec <- currentTypeErrorContext
  liftIO $ modifyIORef ref ((tec, sc) :)

resolveSyn :: Ty -> TC Ty
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
          reportError $ Other $ D.hsep [D.text "Type synonym", D.dquotes (ppr c), D.text "must be fully-applied."]
          abortTyping
    go _ (TyMult m) = return $ TyMult m

-- withVar x ty mult =
--   local (\tc -> tc { tcTyEnv = M.insert x (ty, mult) (tcTyEnv tc) })

currentLevel :: TC TcLevel
currentLevel = asks tcTcLevel

pushLevel :: TC a -> TC a
pushLevel m = do
  -- perform computation.
  res <- local (\tc -> tc{tcTcLevel = succ (tcTcLevel tc)}) m

  tref <- asks tcDeferredIC
  -- deferred
  deferred <- liftIO $ readIORef tref

  debugPrint 4 $ red $ text "#deferred checks:" <+> ppr (length deferred)

  procDeferred deferred

  return res
  where
    procDeferred [] = return ()
    procDeferred ((tyc, q) : qs) = do
      restoreTypeErrorContext tyc $ scCheck q
      procDeferred qs

currentIcLevel :: TC IcLevel
currentIcLevel = asks tcIcLevel

pushIcLevel :: TC a -> TC a
pushIcLevel = localIcLevel succ

localIcLevel :: (IcLevel -> IcLevel) -> TC a -> TC a
localIcLevel f = local $ \tc -> tc{tcIcLevel = f (tcIcLevel tc)}

withVar :: Name -> Ty -> TC a -> TC a
withVar x ty = local (\tc -> tc{tcTyEnv = M.insert x ty (tcTyEnv tc)})

withSyn :: Name -> ([TyVar], Ty) -> TC r -> TC r
withSyn tv v = local (\tc -> tc{tcSyn = M.insert tv v (tcSyn tc)})

withCon :: Name -> ConTy -> TC a -> TC a
withCon c ty = local (\tc -> tc{tcConEnv = M.insert c ty (tcConEnv tc)})

newMetaTy :: TC Ty
newMetaTy = TyMetaV <$> newMetaTyVar

withVars :: [(Name, Ty)] -> TC r -> TC r
withVars ns m = foldr (uncurry withVar) m ns

withCons :: [(Name, ConTy)] -> TC r -> TC r
withCons ns m = foldr (uncurry withCon) m ns

withSyns :: [(Name, ([TyVar], Ty))] -> TC r -> TC r
withSyns xs m = foldr (uncurry withSyn) m xs

zonkMetaTyVar :: MetaTyVar -> TC Ty
zonkMetaTyVar mv = {- trace "zonk!" $ -} do
  res <- readTyVar mv
  case res of
    Nothing -> return (TyMetaV mv)
    Just ty -> do
      ty' <- zonkType ty
      writeTyVar mv ty'
      return ty'

zonkType :: Ty -> TC Ty
zonkType (TyVar n) = return $ TyVar n
zonkType (TyCon c ts) =
  TyCon c <$> traverse zonkType ts
zonkType (TyForAll ns t) =
  TyForAll ns <$> zonkTypeQ t
zonkType (TyMetaV m) = zonkMetaTyVar m
zonkType (TySyn origTy ty) =
  TySyn <$> zonkType origTy <*> zonkType ty
zonkType (TyMult m) = return (TyMult m)

zonkTypeQ :: QualTy -> TC QualTy
zonkTypeQ (TyQual cs t) = TyQual <$> traverse zonkTypeC cs <*> zonkType t

zonkTypeC :: TyConstraint -> TC TyConstraint
zonkTypeC (MSub t1 ts2) = MSub <$> zonkType t1 <*> traverse zonkType ts2
zonkTypeC (TyEq t1 t2) = TyEq <$> zonkType t1 <*> zonkType t2

zonkTypeIC :: InferredConstraint -> TC InferredConstraint
zonkTypeIC (ICNormal c) = ICNormal <$> zonkTypeC c
zonkTypeIC (ICGuarded loc wc ex cs ics) = ICGuarded loc wc ex <$> mapM zonkTypeC cs <*> mapM zonkTypeIC ics

zonkTypeError :: TypeError -> TC TypeError
zonkTypeError (TypeError loc snippet es wc res) = do
  wc' <- zonkWhenChecking wc
  res' <- zonkErrorDetail res
  return $ TypeError loc snippet es wc' res'

zonkWhenChecking :: WhenChecking -> TC WhenChecking
zonkWhenChecking (CheckingEquality t1 t2) =
  CheckingEquality <$> zonkType t1 <*> zonkType t2
zonkWhenChecking (CheckingMoreGeneral t1 t2) =
  CheckingMoreGeneral <$> zonkType t1 <*> zonkType t2
zonkWhenChecking (CheckingConstraint cs) =
  CheckingConstraint <$> traverse zonkTypeC cs
zonkWhenChecking (CheckingMultiplicities x mc ts1 ts2) =
  CheckingMultiplicities x mc <$> mapM zonkType ts1 <*> mapM zonkType ts2
zonkWhenChecking (CheckingType n ty) =
  CheckingType n <$> zonkType ty
zonkWhenChecking (OtherContext d) = return (OtherContext d)
zonkWhenChecking CheckingNone = return CheckingNone

zonkErrorDetail :: ErrorDetail -> TC ErrorDetail
zonkErrorDetail (UnMatchTy t1 t2) = UnMatchTy <$> zonkType t1 <*> zonkType t2
zonkErrorDetail (OccurrenceCheck tv ty) =
  OccurrenceCheck tv <$> zonkType ty
zonkErrorDetail (ImplicationCheckFail ex cs cs') = do
  ex' <- filterM (\mv -> do res <- readTyVar mv; pure $ isNothing res) ex
  ImplicationCheckFail ex' <$> mapM zonkTypeC cs <*> mapM zonkTypeC cs'
zonkErrorDetail (Untouchable m t) =
  Untouchable <$> pure m <*> zonkType t
zonkErrorDetail (GeneralizeFail ty1 ty2 tyvs) =
  GeneralizeFail <$> zonkType ty1 <*> zonkType ty2 <*> pure tyvs
zonkErrorDetail (LessPolymorphic ty1@(TyMetaV mv) ty2 escaped) = do
  ty2' <- zonkType ty2
  if containsForAll ty2'
    then
      pure $ CannotUnifyPolyTy mv ty2'
    else
      LessPolymorphic <$> zonkType ty1 <*> pure ty2' <*> pure escaped
  where
    containsForAll (TyForAll _ _) = True
    containsForAll (TyCon _ ts) = any containsForAll ts
    containsForAll (TySyn _ t) = containsForAll t
    containsForAll _ = False
zonkErrorDetail (LessPolymorphic ty1 ty2 escaped) =
  LessPolymorphic <$> zonkType ty1 <*> zonkType ty2 <*> pure escaped
zonkErrorDetail res = pure res

skolemize :: PolyTy -> TC ([TyVar], QualTy)
skolemize (TyForAll tvs ty) = do
  sks1 <- localIcLevel (const (-1)) $ mapM newSkolemTyVar tvs
  (sks2, TyQual cs2 ty2) <- skolemizeQ $ substTyQ (zip tvs $ map TyVar sks1) ty
  return (sks1 ++ sks2, TyQual cs2 ty2)
skolemize (FunTy m argTy resTy) = do
  (sks, TyQual cs resTy') <- skolemize resTy
  pure (sks, TyQual cs (FunTy m argTy resTy'))
skolemize ty = return ([], TyQual [] ty)

skolemizeQ :: QualTy -> TC ([TyVar], QualTy)
skolemizeQ (TyQual cs ty) = do
  (sks, TyQual cs' ty') <- skolemize ty
  pure (sks, TyQual (cs ++ cs') ty')

unify :: MonoTy -> MonoTy -> TC ()
unify ty1 ty2 = do
  ty1' <- resolveSyn ty1
  ty2' <- resolveSyn ty2
  -- Check: is it ok that ty1' and ty2' are not zonked?
  unifyWork ty1' ty2'

unifyWork :: MonoTy -> MonoTy -> TC ()
unifyWork (TySyn _ t1) t2 = unifyWork t1 t2
unifyWork t1 (TySyn _ t2) = unifyWork t1 t2
unifyWork (TyMetaV mv1) (TyMetaV mv2) | mv1 == mv2 = return ()
unifyWork (TyMetaV mv) ty = unifyMetaTyVar mv ty
unifyWork ty (TyMetaV mv) = unifyMetaTyVar mv ty
unifyWork (TyCon c ts) (TyCon c' ts') | c == c' = do
  when (length ts /= length ts') $
    reportError $
      Other $
        D.hsep [D.text "Type construtor", ppr c, D.text "has different number of arguments."]
  zipWithM_ unifyWork ts ts'
unifyWork (TyMult m) (TyMult m') | m == m' = return ()
unifyWork (TyVar x1) (TyVar x2) | x1 == x2 = return ()
unifyWork (TyVar x) t = do
  icLevel <- currentIcLevel
  when (icLevel == 0) $ reportError $ UnMatchTy (TyVar x) t
  addConstraint [TyEq (TyVar x) t]
unifyWork t (TyVar x) = do
  icLevel <- currentIcLevel
  when (icLevel == 0) $ reportError $ UnMatchTy (TyVar x) t
  addConstraint [TyEq t (TyVar x)]
unifyWork pty1@(TyForAll tvs1 _) (TyForAll tvs2 qty2)
  | length tvs1 == length tvs2 = do
      (skVars, TyQual cs1 ty1) <- skolemize pty1
      let TyQual cs2 ty2 = substTyQ (zip tvs2 $ map TyVar skVars) qty2

      addImpConstraint [] cs1 (map ICNormal cs2)
      addImpConstraint [] cs2 (map ICNormal cs1)

      unifyWork ty1 ty2
unifyWork ty1 ty2 = do
  ty1' <- zonkType ty1
  ty2' <- zonkType ty2
  reportError $ UnMatchTy ty1' ty2'

unifyMetaTyVar :: MetaTyVar -> MonoTy -> TC ()
unifyMetaTyVar mv ty2 = do
  res <- readTyVar mv
  case res of
    Just ty -> unify ty ty2
    Nothing ->
      unifyUnboundMetaTyVar mv ty2

-- Inspired from GHC's implementation.
shouldBeSwapped :: MetaTyVar -> MetaTyVar -> TC Bool
shouldBeSwapped mv1 mv2 = do
  lv1 <- readTcLevelMv mv1
  lv2 <- readTcLevelMv mv2
  return $
    if
      | metaIcLevel mv1 < metaIcLevel mv2 ->
          -- NB: mv1 := mv2 is possible a's IC-level is equivalent or greater to the current.
          -- Thus, this swapping increases chance for the substitution to succeed.
          True
      | lv1 < lv2 ->
          -- No technical reason, but we prioritise outer level variables to survive.
          True
      | otherwise ->
          False

unifyUnboundMetaTyVar :: MetaTyVar -> MonoTy -> TC ()
unifyUnboundMetaTyVar mv (TyMetaV mv2) = do
  res <- readTyVar mv2
  sw <- shouldBeSwapped mv mv2
  cIcLevel <- asks tcIcLevel
  case res of
    Nothing ->
      if
        | mv == mv2 -> return ()
        | sw ->
            substituteUnif cIcLevel mv2 (TyMetaV mv)
        | otherwise ->
            substituteUnif cIcLevel mv (TyMetaV mv2)
    Just ty2' -> unifyUnboundMetaTyVar mv ty2'
unifyUnboundMetaTyVar mv ty2 = do
  ty2' <- zonkType ty2
  let mvs = metaTyVars [ty2']
  cIcLevel <- asks tcIcLevel
  if mv `elem` mvs
    then do
      reportError $ OccurrenceCheck mv ty2'
      -- We abort typing when occurrence check fails; otherwise, zonkType can diverge.
      abortTyping
    else do
      substituteUnif cIcLevel mv ty2'

-- Assumption: ty is already zonked.
substituteUnif :: IcLevel -> MetaTyVar -> MonoTy -> TC ()
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

newtype MM f a = MM {runMM :: f a}

instance (Applicative f, Monoid a) => Semigroup (MM f a) where
  MM m1 <> MM m2 = MM $ (<>) <$> m1 <*> m2

instance (Applicative f, Monoid a) => Monoid (MM f a) where
  mempty = MM $ pure mempty

tcLevel :: (MetaTyVars t) => t -> TC TcLevel
tcLevel t =
  getMin <$> (runMM $ metaTyVarsGen (\mv -> MM $ Min <$> liftIO (readTcLevelMv mv)) t)

skIcLevel :: (S.FreeTyVars t TyVar) => t -> IcLevel
skIcLevel =
  getMax
    . S.foldMapVars
      ( \x -> case x of
          SkolemTv _ _ lv -> Max lv
          _ -> mempty
      )
      (\_ m -> m)
