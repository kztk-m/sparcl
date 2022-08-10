{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE ViewPatterns       #-}
module Language.Sparcl.Typing.Type where

import qualified Data.Map                     as M

import           Language.Sparcl.FreeTyVars
import           Language.Sparcl.Multiplicity
import           Language.Sparcl.Name
import           Language.Sparcl.Pretty       as D hiding ((<$>))
import qualified Language.Sparcl.Pretty       as D

import           Control.Arrow                (second)
import           Control.Monad.IO.Class       (MonadIO (..))
import           Data.IORef
import           Data.Maybe                   (fromMaybe, isJust)
import           Data.Semigroup               (Endo (..))
import qualified Data.Set                     as S
import           System.IO.Unsafe

{- |

Used for generalization. Increases when it encounters a part for which
a polytype is required. Type variables retain the level when they are
introduced, and unification replaces the the level with the mininum.
For example, unification

@
   a[3] |-> b[2] -> c[1]
@

changes the level of a to 1.

In generalization, a type checker only generalize variables that are
more than the current level.

-}
newtype TcLevel = TcLevel Int
  deriving (Eq, Ord, Enum, Num, Bounded)
  deriving newtype (Show, Pretty)


{- |

Used for implication checking. Increases when implication happens.  If
a type checker runs in level n, unification of smaller-leveled
variables is prohibited.

-}
newtype IcLevel = IcLevel Int
  deriving (Eq, Ord, Enum, Num, Bounded)
  deriving newtype (Show, Pretty)


data Ty = TyCon   !Name ![Ty]       -- ^ Type constructor
        | TyVar   !TyVar           -- ^ Type variable
        | TyMetaV !MetaTyVar       -- ^ Metavariables (to be substituted in type inf.)
        | TyForAll ![TyVar] !QualTy -- ^ polymorphic types
        | TySyn   !Ty !Ty           -- ^ type synonym (@TySym o u@ means @u@ but @o@ will be used for error messages)
        | TyMult  !Multiplicity    -- ^ 1 or ω
         deriving (Eq, Ord, Show)

isMonoTy :: Ty -> Bool
isMonoTy = isJust . testMonoTy

testMonoTy :: Ty -> Maybe MonoTy
testMonoTy (TyForAll xs (TyQual q t)) | null xs && null q = testMonoTy t
                                      | otherwise         = Nothing
testMonoTy (TySyn _ t) = testMonoTy t
testMonoTy t = Just t


{- |

We have a specfical treatment for constructor types, as this the only point
we introduce existential variables.

In it's use there is not difference between universal and existential variables---they are treated as
ordinary types.

In pattern matching, their behaviors are different. Universal variables are replaced with
unification variables, but existential varibles are replaced with skolemized variables.

Skolemized variables cannot escape in the resulting type, and use map.

-}
data ConTy = ConTy ![TyVar]        -- universal variables
                   ![TyVar]        -- existential variables
                   ![TyConstraint] -- constraints
                   ![(Ty, Ty)]     -- constructor's argument types (a pair of a type and a multiplicity)
                   !Ty             -- constructor's return types

instance Pretty ConTy where
  ppr (ConTy xs ys q args ty) =
    let hd d = if null (xs ++ ys) then d
               else hsep [ text "forall", hsep (map ppr xs ++ map ppr ys) <> text "." ] <> align d
        ql d = if null q then d
               else sep [ parens (hsep $ punctuate comma $ map ppr q) <+> text "=>", d ]
    in hd $ ql $ foldr (\(a,m) r -> pprPrec 1 a <+> text "#" <+> ppr m <+> text "->" <+> r) (ppr ty) args

conTy2Ty :: ConTy -> Ty
conTy2Ty (ConTy xs ys q argTy retTy) =
  let t = foldr (\(s,m) r -> TyCon nameTyArr [m, s, r]) retTy argTy
  in TyForAll (xs ++ ys) (TyQual q t)

instance MultiplicityLike Ty where
  one   = TyMult One
  omega = TyMult Omega
  fromMultiplicity = TyMult

data QualTy = TyQual ![TyConstraint] !BodyTy
  deriving (Eq, Ord, Show)

data TyConstraint = MSub !Ty ![Ty]
                  | TyEq !Ty !Ty
  deriving (Eq, Ord, Show)

data TyVar = BoundTv  !Name
           | SkolemTv !TyVar !Int !IcLevel
             -- used for checking of which type is more general.
  deriving Show

instance Eq TyVar where
  BoundTv  n   == BoundTv  m       = n == m
  SkolemTv _ i _ == SkolemTv _ j _ = i == j
  _ == _                           = False

instance Ord TyVar where
  BoundTv n <= BoundTv m           = n <= m
  BoundTv _ <= _                   = True
  SkolemTv _ _ _ <= BoundTv _      = False
  SkolemTv _ i _ <= SkolemTv _ j _ = i <= j


instance Pretty TyVar where
  ppr (BoundTv n)       = ppr n
  ppr (SkolemTv n i lv) = ppr n D.<> D.text "@" D.<> D.int i D.<> ppr lv


instance FreeTyVars Ty TyVar where
  -- Assumption: the input is already zonked.
  foldMapVars f b (TyCon _ ts)    = foldMapVars f b ts
  foldMapVars f _ (TyVar x)       = f x
  foldMapVars _ _ (TyMetaV _)     = mempty
  foldMapVars f b (TyForAll xs t) =
    flip (foldr b) xs $ foldMapVars f b t
  foldMapVars _ _ (TyMult _) = mempty
  foldMapVars f b (TySyn _ t) = foldMapVars f b t

instance FreeTyVars QualTy TyVar where
  -- Assumption: the input is already zonked.
  foldMapVars f b (TyQual q t) = foldMapVars f b (q, t)

instance FreeTyVars TyConstraint TyVar where
  -- Assumption: the input is already zonked.
  foldMapVars f b (MSub t1 ts2) = foldMapVars f b t1 <> foldMapVars f b ts2
  foldMapVars f b (TyEq t1 t2)  = foldMapVars f b t1 <> foldMapVars f b t2

readTcLevelMv :: MonadIO m => MetaTyVar -> m TcLevel
readTcLevelMv mv = liftIO $ readIORef (metaTcLevelRef mv)

setTcLevelMv :: MonadIO m => MetaTyVar -> TcLevel -> m ()
setTcLevelMv mv lvl = liftIO $ writeIORef (metaTcLevelRef mv) lvl

capLevel :: MonadIO m => TcLevel -> Ty -> m Ty
capLevel n = go
  where
    cap = min n

    goQ (TyQual cs t) = TyQual <$> traverse goC cs <*> go t

    goC (MSub t ts)  = MSub <$> go t <*> traverse go ts
    goC (TyEq t1 t2) = TyEq <$> go t1 <*> go t2

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
      pprMs []     = ppr One
      pprMs (x:xs) = pprMs' x xs

      pprMs' x []     = ppr x
      pprMs' x (y:ys) = ppr x <+> text "*" <+> pprMs' y ys
  ppr (TyEq t1 t2) = ppr t1 <+> text "~" <+> ppr t2

-- | Unification variables
data MetaTyVar = MetaTyVar { metaID         :: !Int,
                             metaRef        :: !TyRef,
                             metaTcLevelRef :: !(IORef TcLevel),
                             metaIcLevel    :: !IcLevel}

type TyRef = IORef (Maybe MonoTy)

instance Pretty MetaTyVar where
  ppr (MetaTyVar i _ r ic) =
    let l = unsafePerformIO (readIORef r)
    in D.text $ "_" ++ show i ++ "[" ++ show l ++ "|" ++ show ic ++ "]"

instance Show MetaTyVar where
  show = prettyShow

instance Eq MetaTyVar where
  mv1 == mv2 = metaRef mv1 == metaRef mv2

instance Ord MetaTyVar where
  mv1 <= mv2 = metaID mv1 <= metaID mv2

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
substTyC tbl' (MSub t1 ts2) = MSub (substTy tbl' t1) (map (substTy tbl') ts2)
substTyC tbl' (TyEq t1 t2)  = TyEq (substTy tbl' t1) (substTy tbl' t2)

consec2simul  :: [ (TyVar, Ty) ] -> [ (TyVar, Ty) ]
consec2simul [] = []
consec2simul ((x,t):xts) =
  let r = consec2simul xts
  in (x,t): map (\(y,s) -> (y, substTy [(x,t)] s)) r

consec2simulMeta :: [ (MetaTyVar, Ty) ] -> [ (MetaTyVar, Ty) ]
consec2simulMeta [] = []
consec2simulMeta ((x,t):xts) =
  (x,t) : map (second $ substTyMeta [(x,t)]) (consec2simulMeta xts)

substTyMeta :: [ (MetaTyVar, Ty) ] -> Ty -> Ty
substTyMeta tbl ty = case ty of
  TyVar n       -> TyVar n
  TyCon c ts    -> TyCon c (map (substTyMeta tbl) ts)
  TyMetaV m     -> fromMaybe ty (Prelude.lookup m tbl)
  TyForAll ns t -> TyForAll ns (substTyMetaQ tbl t)
  TySyn _ uTy   -> substTyMeta tbl uTy
  TyMult m      -> TyMult m

substTyMetaQ :: [ (MetaTyVar, Ty) ] -> QualTy -> QualTy
substTyMetaQ tbl (TyQual cs t) =
  TyQual (map (substTyMetaC tbl) cs) (substTyMeta tbl t)

substTyMetaC :: [ (MetaTyVar, Ty) ] -> TyConstraint -> TyConstraint
substTyMetaC tbl (MSub t ts)  = MSub (substTyMeta tbl t) (map (substTyMeta tbl) ts)
substTyMetaC tbl (TyEq t1 t2) = TyEq (substTyMeta tbl t1) (substTyMeta tbl t2)



class MetaTyVars t where
  metaTyVarsGen :: Monoid n => (MetaTyVar -> n) -> t -> n

instance MetaTyVars t => MetaTyVars [t] where
  metaTyVarsGen f ts = mconcat $ map (metaTyVarsGen f) ts

instance (MetaTyVars s, MetaTyVars t) => MetaTyVars (s, t) where
  {-# INLINE metaTyVarsGen #-}
  metaTyVarsGen f (s, t) = metaTyVarsGen f s <> metaTyVarsGen f t

instance MetaTyVars Ty where
  metaTyVarsGen f (TyCon _ ts)   = metaTyVarsGen f ts
  metaTyVarsGen f (TySyn _ t)    = metaTyVarsGen f t
  metaTyVarsGen f (TyForAll _ t) = metaTyVarsGen f t
  metaTyVarsGen f (TyMetaV mv)   = f mv
  metaTyVarsGen _ _              = mempty

instance MetaTyVars QualTy where
  metaTyVarsGen f (TyQual q t) = metaTyVarsGen f (q, t)

instance MetaTyVars TyConstraint where
  metaTyVarsGen f (MSub ms1 ms2) = metaTyVarsGen f (ms1, ms2)
  metaTyVarsGen f (TyEq t1 t2)   = metaTyVarsGen f (t1, t2)

metaTyVars :: MetaTyVars t => t -> [MetaTyVar]
metaTyVars t = S.toList $ appEndo (metaTyVarsGen (\x -> Endo (S.insert x)) t) S.empty

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


type TypeTable  = M.Map Name Ty
type CTypeTable = M.Map Name ConTy
type SynTable   = M.Map Name ([TyVar], Ty)
