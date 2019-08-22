{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE DerivingStrategies #-}
module Language.Sparcl.Typing.Type where

import qualified Data.Map as M

import Language.Sparcl.Pretty as D hiding ((<$>))
import qualified Language.Sparcl.Pretty as D 
import Language.Sparcl.Name
import Language.Sparcl.Multiplicity

import Data.IORef
import Data.Maybe (fromMaybe) 

import Control.Monad.IO.Class (MonadIO(..))

import System.IO.Unsafe

newtype TcLevel = TcLevel Int
  deriving (Eq, Ord, Enum, Num)
  deriving newtype Show 

data Ty = TyCon   Name [Ty]       -- ^ Type constructor 
        | TyVar   TyVar           -- ^ Type variable         
        | TyMetaV MetaTyVar       -- ^ Metavariables (to be substituted in type inf.) 
        | TyForAll [TyVar] QualTy -- ^ polymorphic types 
        | TySyn   Ty Ty           -- ^ type synonym (@TySym o u@ means @u@ but @o@ will be used for error messages)
        | TyMult  Multiplicity    -- ^ 1 or ω
         deriving (Eq, Ord, Show)

instance MultiplicityLike Ty where
  one   = TyMult One
  omega = TyMult Omega 
  fromMultiplicity = TyMult 

data QualTy = TyQual [TyConstraint] BodyTy
  deriving (Eq, Ord, Show)

data TyConstraint = MSub Ty [Ty] 
  deriving (Eq, Ord, Show)

data TyVar = BoundTv  Name
           | SkolemTv TyVar Int -- used only for checking of which type is more general. 
  deriving Show 

instance Eq TyVar where
  BoundTv n == BoundTv m = n == m
  SkolemTv _ i == SkolemTv _ j = i == j
  _ == _ = False

instance Ord TyVar where 
  BoundTv n <= BoundTv m = n <= m
  BoundTv _ <= _         = True
  SkolemTv _ _ <= BoundTv _  = False 
  SkolemTv _ i <= SkolemTv _ j = i <= j 


instance Pretty TyVar where
  ppr (BoundTv n)    = ppr n
  ppr (SkolemTv n i) = ppr n D.<> D.text "@" D.<> D.int i 


readTcLevelMv :: MonadIO m => MetaTyVar -> m TcLevel
readTcLevelMv mv = liftIO $ readIORef (metaTcLevelRef mv)

setTcLevelMv :: MonadIO m => MetaTyVar -> TcLevel -> m () 
setTcLevelMv mv lvl = liftIO $ writeIORef (metaTcLevelRef mv) lvl 

capLevel :: MonadIO m => TcLevel -> Ty -> m Ty
capLevel n = go
  where
    cap = min n

    goQ (TyQual cs t) = TyQual <$> traverse goC cs <*> go t

    goC (MSub t ts) = MSub <$> go t <*> traverse go ts
    
    go (TyCon c ts) = TyCon c <$> traverse go ts
    go (TyVar x)    = return $ TyVar x
    go (TyMetaV mv) = do
      lv <- readTcLevelMv mv
      setTcLevelMv mv (cap lv) 
      return $ TyMetaV mv 
    go (TyForAll qs ts) = TyForAll qs <$> goQ ts
    go (TySyn o u) = TySyn o <$> go u
    go (TyMult p)  = return $ TyMult p 

    

instance Pretty Ty where
  pprPrec _ (TyCon c ts)
    | c == nameTyTuple (length ts) =
        D.parens $ D.hsep $ D.punctuate D.comma $ map (pprPrec 0) ts
  pprPrec k (TyCon c [t])
    | c == nameTyBang =
        parensIf (k > 1) $ D.text "!" D.<> pprPrec 1 t
    | c == nameTyRev =
        parensIf (k > 1) $ D.text "rev" D.<+> pprPrec 2 t 

  pprPrec _ (TyCon c []) = ppr c
  pprPrec k (TyCon c [m,a,b]) | c == nameTyArr = parensIf (k > 0) $ 
    case m of
      TyMult One   -> D.group (D.align (pprPrec 1 a) D.<$> D.text "-o" D.<+> pprPrec 0 b)
      TyMult Omega -> D.group (D.align (pprPrec 1 a) D.<$> D.text "->" D.<+> pprPrec 0 b)
      _            -> D.group (D.align (pprPrec 1 a) <+> D.text "#" <+> pprPrec 0 m D.<$> text "->" <+> pprPrec 0 b)

  pprPrec k (TyCon c ts) = parensIf (k > 1) $
    ppr c D.<+> D.align (D.hsep (map (pprPrec 2) ts))

  pprPrec _ (TyVar x) = ppr x 

  pprPrec _ (TyMetaV m) = ppr m

  pprPrec k (TyForAll [] t) = pprPrec k t 
  pprPrec k (TyForAll ns t) = D.group $ D.align $ parensIf (k > 0) $ 
    D.text "forall" D.<+>
      D.hsep (map ppr ns) D.<> D.text "."
      D.<> nest 2 (line <> D.align (pprPrec 0 t))

  pprPrec k (TySyn t _) = pprPrec k t 

  pprPrec _ (TyMult p) = ppr p 

instance Pretty QualTy where
  pprPrec k (TyQual [] t) = pprPrec k t 
  pprPrec k (TyQual cs t) = parensIf (k > 0) $ align $ 
    sep [d, text "=>" <+> pprPrec 0 t]
    where
      d = parens $ hsep $ punctuate comma (map ppr cs)

instance Pretty TyConstraint where
  ppr (MSub ty1 tys2) = ppr ty1 <+> text "<=" <+> pprMs tys2
    where
      pprMs []  = ppr One
      pprMs (x:xs) = pprMs' x xs

      pprMs' x []     = ppr x
      pprMs' x (y:ys) = ppr x <+> text "*" <+> pprMs' y ys 
    

data MetaTyVar = MetaTyVar { metaID :: !Int, metaRef :: !TyRef, metaTcLevelRef ::  !(IORef TcLevel)}
 
type TyRef = IORef (Maybe MonoTy)

instance Pretty MetaTyVar where
  ppr (MetaTyVar i _ r) =
    let l = unsafePerformIO (readIORef r) 
    in D.text $ "_" ++ show i ++ "[" ++ show l ++ "]" 

instance Show MetaTyVar where
  show = prettyShow 

instance Eq MetaTyVar where
  -- MetaTyVar i _ == MetaTyVar j _ = i == j
  MetaTyVar _ i _ == MetaTyVar _ j _ = i == j 

instance Ord MetaTyVar where
  MetaTyVar i _ _ <= MetaTyVar j _ _ = i <= j 

type BodyTy = MonoTy  -- forall body. only consider rank 1
type PolyTy = Ty      -- polymorphic types
type MonoTy = Ty      -- monomorphic types

type MultTy = Ty 

substTy :: [ (TyVar, Ty) ] -> Ty -> Ty
substTy tbl ty = case ty of
  TyVar n -> fromMaybe ty (Prelude.lookup n tbl)
  TyCon c ts ->
    TyCon c $ map (substTy tbl) ts
  TyMetaV m -> TyMetaV m
  TyForAll ns t ->
    let tbl' = filter (not . (`elem` ns) . fst) tbl
    in TyForAll ns $ substTyQ tbl' t 
  TySyn origTy uTy -> TySyn (substTy tbl origTy) (substTy tbl uTy)
  TyMult m -> TyMult m 

substTyQ :: [ (TyVar, Ty) ] -> QualTy -> QualTy 
substTyQ tbl' (TyQual cs t) = TyQual (map (substTyC tbl') cs) (substTy tbl' t)

substTyC :: [ (TyVar, Ty) ] -> TyConstraint -> TyConstraint 
substTyC tbl' (MSub t1 ts2)  = MSub (substTy tbl' t1) (map (substTy tbl') ts2)

metaTyVars :: [Ty] -> [MetaTyVar]
metaTyVarsQ :: [QualTy] -> [MetaTyVar]
metaTyVarsC :: [TyConstraint] -> [MetaTyVar]

(metaTyVars, metaTyVarsQ, metaTyVarsC) =
  (flip (apps goTy) [], flip (apps goQ) [], flip (apps goC) [])
  where
    apps _f []     r = r
    apps f  (t:ts) r = f t (apps f ts r) 
    
    goTy (TyCon _ ts)   r = apps goTy ts r
    goTy (TyForAll _ t) r = goQ t r
    goTy (TySyn _ t)    r = goTy t r
    goTy (TyMetaV m)    r = if m `elem` r then r else m:r
    goTy _              r = r 

    goQ (TyQual cs t) r = apps goC cs $ goTy t r 

    goC :: TyConstraint -> [MetaTyVar] -> [MetaTyVar]
    goC (MSub ts1 ts2) r = goTy ts1 $ apps goTy ts2 r 

bangTy :: Ty -> Ty
bangTy ty = TyCon nameTyBang [ty]

revTy :: Ty -> Ty
revTy ty = TyCon nameTyRev [ty]

(-@) :: Ty -> Ty -> Ty
t1 -@ t2 = TyCon nameTyArr [TyMult One, t1, t2]

pattern (:-@) :: Ty -> Ty -> Ty 
pattern t1 :-@ t2 <- TyCon ((== nameTyArr) -> True) [TyMult One, t1, t2] 
  where
    t1 :-@ t2 = TyCon nameTyArr [TyMult One, t1, t2]

boolTy :: Ty
boolTy = TyCon nameTyBool []

charTy :: Ty
charTy = TyCon nameTyChar []

tupleTy :: [Ty] -> Ty
tupleTy ts = TyCon (nameTyTuple $ length ts) ts 

typeKi :: Ty
typeKi = TyCon nameKindType []

arrKi :: Ty -> Ty -> Ty
arrKi k1 k2 = TyCon nameKiArr [k1, k2]

infixr 4 -@
infixr 4 :-@

(*->) :: Ty -> Ty -> Ty   
a *-> b = TyCon nameTyArr [TyMult Omega, a, b]
infixr 4 *-> 

(*-@) :: Ty -> Ty -> Ty
a *-@ b = a -@ b 
infixr 4 *-@

tyarr :: MultTy -> Ty -> Ty -> Ty 
tyarr m a b = TyCon nameTyArr [m, a, b]
  
  
type TypeTable = M.Map Name Ty
type SynTable  = M.Map Name ([TyVar], Ty)
