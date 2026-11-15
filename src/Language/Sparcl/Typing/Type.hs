{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE ViewPatterns #-}

module Language.Sparcl.Typing.Type where

import qualified Data.Map as M

import Language.Sparcl.FreeTyVars
import Language.Sparcl.Multiplicity
import Language.Sparcl.Name
import Language.Sparcl.Pretty as D hiding ((<$>))
import qualified Language.Sparcl.Pretty as D

import Control.Arrow (second)
import Control.Monad.IO.Class (MonadIO (..))
import Data.IORef
import Data.Maybe (fromMaybe, isJust)
import Data.Semigroup (Endo (..))
import qualified Data.Set as S
import System.IO.Unsafe

-- |
--
-- Used for generalization. Increases when it encounters a part for which
-- a polytype is required. Type variables retain the level when they are
-- introduced, and unification replaces the the level with the mininum.
-- For example, unification
--
-- @
--    a[3] |-> b[2] -> c[1]
-- @
--
-- changes the level of a to 1.
--
-- In generalization, a type checker only generalize variables that are
-- more than the current level.
newtype TcLevel = TcLevel Int
  deriving (Eq, Ord, Enum, Num, Bounded)
  deriving newtype (Show, Pretty)

-- |
--
-- Used for implication checking. Increases when implication happens.  If
-- a type checker runs in level n, unification of smaller-leveled
-- variables is prohibited.
newtype IcLevel = IcLevel Int
  deriving (Eq, Ord, Enum, Num, Bounded)
  deriving newtype (Show, Pretty)

-- | Type-level expressions. Applications are binary ('TyApp') with no
--   flattening, so each type has exactly one representation and the
--   derived 'Eq' / 'Ord' are semantic. The two kinds of function types
--   are constructs of their own, not applications of type constructors,
--   and are never decomposed by unification.
data Ty
  = -- | Type constructor (unapplied)
    TyConst !Name
  | -- | Type variable
    TyVar !TyVar
  | -- | Metavariables (to be substituted in type inf.)
    TyMetaV !MetaTyVar
  | -- | Application of a type-level expression to another
    TyApp !Ty !Ty
  | -- | Function type @a # m -> b@ (@TyFun m a b@)
    TyFun !MultTy !Ty !Ty
  | -- | Instance-argument function type @{{c}} -> t@ (always unrestricted)
    TyInstFun !Ty !Ty
  | -- | polymorphic types
    TyForAll ![TyVar] !QualTy
  | -- | type synonym (@TySym o u@ means @u@ but @o@ will be used for error messages)
    TySyn !Ty !Ty
  | -- | 1 or ω
    TyMult !Multiplicity
  deriving (Eq, Ord, Show)

-- | A type constructor applied to arguments (possibly none or partially):
--   @TyCon c [t1, ..., tn]@ is @TyApp (... (TyApp (TyConst c) t1) ...) tn@.
--   As a pattern it matches only applications headed by a constant; it is
--   in no @COMPLETE@ set, so a function that matches it but not 'TyApp'
--   is reported as incomplete.
pattern TyCon :: Name -> [Ty] -> Ty
pattern TyCon c ts <- (splitTyCon -> Just (c, ts))
  where
    TyCon c ts = foldl TyApp (TyConst c) ts

-- | Splits an application headed by a type constructor into the
--   constructor and its arguments.
splitTyCon :: Ty -> Maybe (Name, [Ty])
splitTyCon t = case splitTyApp t of
  (TyConst c, ts) -> Just (c, ts)
  _ -> Nothing

-- | Splits a type-level expression into its head (any type-level
--   expression that is not an application) and its arguments:
--   @splitTyApp (h t1 ... tn) = (h, [t1, ..., tn])@.
--
--   Traversals that inspect the head of an application handle the whole
--   spine at its outermost 'TyApp' (recursing into the partial
--   applications inside would inspect the same head again with fewer
--   arguments); the pattern 'TyCon' is for inspecting or building one
--   application of a type constructor, not for traversals.
splitTyApp :: Ty -> (Ty, [Ty])
splitTyApp = go []
  where
    go acc (TyApp t1 t2) = go (t2 : acc) t1
    go acc t = (t, acc)

isMonoTy :: Ty -> Bool
isMonoTy = isJust . testMonoTy

testMonoTy :: Ty -> Maybe MonoTy
testMonoTy (TyForAll xs (TyQual q t))
  | null xs && null q = testMonoTy t
  | otherwise = Nothing
testMonoTy (TySyn _ t) = testMonoTy t
testMonoTy t = Just t

-- |
--
-- We have a special treatment for constructor types in patterns, as they are the only constructs that
-- introduce existential variables in pattern matching. Notice that we do not need
-- such special treatment for their uses in expressions, where we need not distinguish
-- existential variables from universal ones.
--
-- In pattern matching, their behaviors are different. Universal variables are replaced with
-- unification variables, but existential variables are replaced with skolemized variables.
--
-- Skolemized variables cannot escape in the resulting type, and use map.
data ConTy
  = ConTy
      ![TyVar] -- universal variables
      ![TyVar] -- existential variables
      ![TyConstraint] -- constraints
      ![(Ty, Ty)] -- constructor's argument types (a pair of a type and a multiplicity)
      !Ty -- constructor's return types

instance Pretty ConTy where
  ppr (ConTy xs ys q args ty) =
    let hd d =
          if null (xs ++ ys)
            then d
            else hsep [text "forall", hsep (map ppr xs ++ map ppr ys) <> text "."] <> align d
        ql d =
          if null q
            then d
            else sep [parens (hsep $ punctuate comma $ map ppr q) <+> text "=>", d]
    in  hd $ ql $ foldr (\(a, m) r -> pprPrec 1 a <+> text "#" <+> ppr m <+> text "->" <+> r) (ppr ty) args

conTy2Ty :: ConTy -> Ty
conTy2Ty (ConTy xs ys q argTy retTy) =
  let t = foldr (\(s, m) r -> TyFun m s r) retTy argTy
  in  TyForAll (xs ++ ys) (TyQual q t)

instance MultiplicityLike Ty where
  one = TyMult One
  omega = TyMult Omega
  fromMultiplicity = TyMult

data QualTy = TyQual ![TyConstraint] !BodyTy
  deriving (Eq, Ord, Show)

data TyConstraint
  = MSub !Ty ![Ty]
  | TyEq !Ty !Ty
  deriving (Eq, Ord, Show)

-- | Kinds are type-level expressions: 'typeKi', 'multKi', @'arrKi' k1 k2@
--   and kind metas (D1 in the notes).
type Kind = Ty

-- | Type variables carry their kinds (D2-a in the notes); equality and
--   order look only at names / numbers.
data TyVar
  = BoundTv !Name !Kind
  | SkolemTv !TyVar !Int !IcLevel
  -- used for checking of which type is more general.
  deriving Show

instance Eq TyVar where
  BoundTv n _ == BoundTv m _ = n == m
  SkolemTv _ i _ == SkolemTv _ j _ = i == j
  _ == _ = False

instance Ord TyVar where
  BoundTv n _ <= BoundTv m _ = n <= m
  BoundTv _ _ <= _ = True
  SkolemTv _ _ _ <= BoundTv _ _ = False
  SkolemTv _ i _ <= SkolemTv _ j _ = i <= j

tyVarKind :: TyVar -> Kind
tyVarKind (BoundTv _ k) = k
tyVarKind (SkolemTv v _ _) = tyVarKind v

instance Pretty TyVar where
  ppr (BoundTv n _) = ppr n
  ppr (SkolemTv n i lv) = ppr n D.<> D.text "_" D.<> ppr i D.<> D.text "@" D.<> ppr lv

instance FreeTyVars Ty TyVar where
  -- Assumption: the input is already zonked.
  foldMapVars _ _ (TyConst _) = mempty
  foldMapVars f b (TyApp t1 t2) = foldMapVars f b t1 <> foldMapVars f b t2
  foldMapVars f b (TyFun m t1 t2) = foldMapVars f b m <> foldMapVars f b t1 <> foldMapVars f b t2
  foldMapVars f b (TyInstFun c t) = foldMapVars f b c <> foldMapVars f b t
  foldMapVars f _ (TyVar x) = f x
  foldMapVars _ _ (TyMetaV _) = mempty
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
  foldMapVars f b (TyEq t1 t2) = foldMapVars f b t1 <> foldMapVars f b t2

readTcLevelMv :: (MonadIO m) => MetaTyVar -> m TcLevel
readTcLevelMv mv = liftIO $ readIORef (metaTcLevelRef mv)

setTcLevelMv :: (MonadIO m) => MetaTyVar -> TcLevel -> m ()
setTcLevelMv mv lvl = liftIO $ writeIORef (metaTcLevelRef mv) lvl

capLevel :: (MonadIO m) => TcLevel -> Ty -> m Ty
capLevel n = go
  where
    cap = min n

    goQ (TyQual cs t) = TyQual <$> traverse goC cs <*> go t

    goC (MSub t ts) = MSub <$> go t <*> traverse go ts
    goC (TyEq t1 t2) = TyEq <$> go t1 <*> go t2

    go (TyConst c) = return $ TyConst c
    go (TyApp t1 t2) = TyApp <$> go t1 <*> go t2
    go (TyFun m t1 t2) = TyFun <$> go m <*> go t1 <*> go t2
    go (TyInstFun c t) = TyInstFun <$> go c <*> go t
    go (TyVar x) = return $ TyVar x
    go (TyMetaV mv) = do
      lv <- readTcLevelMv mv
      setTcLevelMv mv (cap lv)
      return $ TyMetaV mv
    go (TyForAll qs ts) = TyForAll qs <$> goQ ts
    go (TySyn o u) = TySyn o <$> go u
    go (TyMult p) = return $ TyMult p

instance Pretty Ty where
  pprPrec _ (TyCon c ts)
    | c == nameTyTuple (length ts) =
        D.parens $ D.hsep $ D.punctuate D.comma $ map (pprPrec 0) ts
    | c == nameTyWTuple (length ts) =
        D.text "&" <> D.parens (D.hsep $ D.punctuate D.comma $ map (pprPrec 0) ts)
  pprPrec k (TyCon c [t])
    | c == nameTyBang =
        parensIf (k > 1) $ D.text "!" D.<> pprPrec 1 t
    | c == nameTyRev =
        parensIf (k > 1) $ D.text "rev" D.<+> pprPrec 2 t
  -- kinds k1 -> k2 (right associative)
  pprPrec k (TyCon c [k1, k2])
    | c == nameKiArr =
        parensIf (k > 0) $ pprPrec 1 k1 D.<+> D.text "->" D.<+> pprPrec 0 k2
  pprPrec _ (TyConst c) = ppr c
  pprPrec k (TyCon c ts) =
    parensIf (k > 1) $
      ppr c D.<+> D.align (D.hsep (map (pprPrec 2) ts))
  -- an application whose head is not a type constructor, e.g. @f a b@
  pprPrec k (TyApp t1 t2) =
    parensIf (k > 1) $ pprPrec 1 t1 D.<+> pprPrec 2 t2
  pprPrec k (TyFun m a b) = parensIf (k > 0) $
    case m of
      TyMult One -> D.group (D.align (pprPrec 1 a) D.<$> D.text "-o" D.<+> pprPrec 0 b)
      TyMult Omega -> D.group (D.align (pprPrec 1 a) D.<$> D.text "->" D.<+> pprPrec 0 b)
      _ -> D.group (D.align (pprPrec 1 a) <+> D.text "#" <+> pprPrec 0 m D.<$> text "->" <+> pprPrec 0 b)
  pprPrec k (TyInstFun cl b) = parensIf (k > 0) $
    D.group (D.text "{{" <> pprPrec 0 cl <> D.text "}}" D.<$> D.text "->" D.<+> pprPrec 0 b)
  pprPrec _ (TyVar x) = ppr x
  pprPrec _ (TyMetaV m) = ppr m
  pprPrec k (TyForAll [] t) = pprPrec k t
  pprPrec k (TyForAll ns t) =
    D.group $
      D.align $
        parensIf (k > 0) $
          D.text "forall"
            D.<+> D.hsep (map ppr ns)
            D.<> D.text "."
            D.<> nest 2 (line <> D.align (pprPrec 0 t))
  pprPrec k (TySyn t _) = pprPrec k t
  pprPrec _ (TyMult p) = ppr p

instance Pretty QualTy where
  pprPrec k (TyQual [] t) = pprPrec k t
  pprPrec k (TyQual cs t) =
    parensIf (k > 0) $
      align $
        sep [d, text "=>" <+> pprPrec 0 t]
    where
      d = parens $ hsep $ punctuate comma (map ppr cs)

instance Pretty TyConstraint where
  ppr (MSub ty1 tys2) = ppr ty1 <+> text "<=" <+> pprMs tys2
    where
      pprMs [] = ppr One
      pprMs (x : xs) = pprMs' x xs

      pprMs' x [] = ppr x
      pprMs' x (y : ys) = ppr x <+> text "*" <+> pprMs' y ys
  ppr (TyEq t1 t2) = ppr t1 <+> text "~" <+> ppr t2

-- | Unification variables
data MetaTyVar = MetaTyVar
  { metaID :: !Int
  , metaRef :: !TyRef
  , metaTcLevelRef :: !(IORef TcLevel)
  , metaIcLevel :: !IcLevel
  , metaKind :: !Kind
  -- ^ the kind of the meta; for a kind meta, the marker
  --   @TyConst nameSort@ (never inspected)
  }

type TyRef = IORef (Maybe MonoTy)

instance Pretty MetaTyVar where
  ppr (MetaTyVar i _ r ic _) =
    let l = unsafePerformIO (readIORef r)
    in  D.text $ "_" ++ show i ++ "[" ++ show l ++ "]@" ++ show ic

instance Show MetaTyVar where
  show = prettyShow

instance Eq MetaTyVar where
  mv1 == mv2 = metaRef mv1 == metaRef mv2

instance Ord MetaTyVar where
  mv1 <= mv2 = metaID mv1 <= metaID mv2

type BodyTy = MonoTy -- forall body. only consider rank 1
type PolyTy = Ty -- polymorphic types
type MonoTy = Ty -- monomorphic types

type MultTy = Ty

substTy :: [(TyVar, Ty)] -> Ty -> Ty
substTy tbl ty = case ty of
  TyVar n -> fromMaybe ty (Prelude.lookup n tbl)
  TyConst c -> TyConst c
  TyApp t1 t2 -> TyApp (substTy tbl t1) (substTy tbl t2)
  TyFun m t1 t2 -> TyFun (substTy tbl m) (substTy tbl t1) (substTy tbl t2)
  TyInstFun c t -> TyInstFun (substTy tbl c) (substTy tbl t)
  TyMetaV m -> TyMetaV m
  TyForAll ns t ->
    let tbl' = filter (not . (`elem` ns) . fst) tbl
    in  TyForAll ns $ substTyQ tbl' t
  TySyn origTy uTy -> TySyn (substTy tbl origTy) (substTy tbl uTy)
  TyMult m -> TyMult m

substTyQ :: [(TyVar, Ty)] -> QualTy -> QualTy
substTyQ tbl' (TyQual cs t) = TyQual (map (substTyC tbl') cs) (substTy tbl' t)

substTyC :: [(TyVar, Ty)] -> TyConstraint -> TyConstraint
substTyC tbl' (MSub t1 ts2) = MSub (substTy tbl' t1) (map (substTy tbl') ts2)
substTyC tbl' (TyEq t1 t2) = TyEq (substTy tbl' t1) (substTy tbl' t2)

consec2simul :: [(TyVar, Ty)] -> [(TyVar, Ty)]
consec2simul [] = []
consec2simul ((x, t) : xts) =
  let r = consec2simul xts
  in  (x, t) : map (\(y, s) -> (y, substTy [(x, t)] s)) r

consec2simulMeta :: [(MetaTyVar, Ty)] -> [(MetaTyVar, Ty)]
consec2simulMeta [] = []
consec2simulMeta ((x, t) : xts) =
  (x, t) : map (second $ substTyMeta [(x, t)]) (consec2simulMeta xts)

substTyMeta :: [(MetaTyVar, Ty)] -> Ty -> Ty
substTyMeta tbl ty = case ty of
  TyVar n -> TyVar n
  TyConst c -> TyConst c
  TyApp t1 t2 -> TyApp (substTyMeta tbl t1) (substTyMeta tbl t2)
  TyFun m t1 t2 -> TyFun (substTyMeta tbl m) (substTyMeta tbl t1) (substTyMeta tbl t2)
  TyInstFun c t -> TyInstFun (substTyMeta tbl c) (substTyMeta tbl t)
  TyMetaV m -> fromMaybe ty (Prelude.lookup m tbl)
  TyForAll ns t -> TyForAll ns (substTyMetaQ tbl t)
  TySyn _ uTy -> substTyMeta tbl uTy
  TyMult m -> TyMult m

substTyMetaQ :: [(MetaTyVar, Ty)] -> QualTy -> QualTy
substTyMetaQ tbl (TyQual cs t) =
  TyQual (map (substTyMetaC tbl) cs) (substTyMeta tbl t)

substTyMetaC :: [(MetaTyVar, Ty)] -> TyConstraint -> TyConstraint
substTyMetaC tbl (MSub t ts) = MSub (substTyMeta tbl t) (map (substTyMeta tbl) ts)
substTyMetaC tbl (TyEq t1 t2) = TyEq (substTyMeta tbl t1) (substTyMeta tbl t2)

class MetaTyVars t where
  metaTyVarsGen :: (Monoid n) => (MetaTyVar -> n) -> t -> n

instance (MetaTyVars t) => MetaTyVars [t] where
  metaTyVarsGen f ts = mconcat $ map (metaTyVarsGen f) ts

instance (MetaTyVars s, MetaTyVars t) => MetaTyVars (s, t) where
  {-# INLINE metaTyVarsGen #-}
  metaTyVarsGen f (s, t) = metaTyVarsGen f s <> metaTyVarsGen f t

instance (MetaTyVars s, MetaTyVars t, MetaTyVars u) => MetaTyVars (s, t, u) where
  {-# INLINE metaTyVarsGen #-}
  metaTyVarsGen f (s, t, u) = metaTyVarsGen f s <> metaTyVarsGen f t <> metaTyVarsGen f u

instance MetaTyVars MetaTyVar where
  {-# INLINE metaTyVarsGen #-}
  metaTyVarsGen f = f

instance MetaTyVars Ty where
  metaTyVarsGen f (TyApp t1 t2) = metaTyVarsGen f (t1, t2)
  metaTyVarsGen f (TyFun m t1 t2) = metaTyVarsGen f (m, t1, t2)
  metaTyVarsGen f (TyInstFun c t) = metaTyVarsGen f (c, t)
  metaTyVarsGen f (TySyn _ t) = metaTyVarsGen f t
  metaTyVarsGen f (TyForAll _ t) = metaTyVarsGen f t
  metaTyVarsGen f (TyMetaV mv) = f mv
  metaTyVarsGen _ (TyConst _) = mempty
  metaTyVarsGen _ (TyVar _) = mempty
  metaTyVarsGen _ (TyMult _) = mempty

instance MetaTyVars QualTy where
  metaTyVarsGen f (TyQual q t) = metaTyVarsGen f (q, t)

instance MetaTyVars TyConstraint where
  metaTyVarsGen f (MSub ms1 ms2) = metaTyVarsGen f (ms1, ms2)
  metaTyVarsGen f (TyEq t1 t2) = metaTyVarsGen f (t1, t2)

metaTyVars :: (MetaTyVars t) => t -> [MetaTyVar]
metaTyVars t = S.toList $ appEndo (metaTyVarsGen (\x -> Endo (S.insert x)) t) S.empty

bangTy :: Ty -> Ty
bangTy ty = TyCon nameTyBang [ty]

revTy :: Ty -> Ty
revTy ty = TyCon nameTyRev [ty]

(-@) :: Ty -> Ty -> Ty
t1 -@ t2 = TyFun (TyMult One) t1 t2

pattern (:-@) :: Ty -> Ty -> Ty
pattern t1 :-@ t2 = TyFun (TyMult One) t1 t2

boolTy :: Ty
boolTy = TyCon nameTyBool []

charTy :: Ty
charTy = TyCon nameTyChar []

tupleTy :: [Ty] -> Ty
tupleTy ts = TyCon (nameTyTuple $ length ts) ts

typeKi :: Kind
typeKi = TyConst nameKindType

multKi :: Kind
multKi = TyConst nameKindMultiplicity

arrKi :: Kind -> Kind -> Kind
arrKi k1 k2 = TyCon nameKiArr [k1, k2]

-- | The marker kept as the 'metaKind' of kind metas.
sortKi :: Ty
sortKi = TyConst nameSort

-- | The kind of a type-level name, from the table (entries of type-level
--   names in the 'TypeTable', D4-a in the notes); the kinds of tuple
--   constructors of all arities are computed from their names.
kindOfName :: TypeTable -> Name -> Maybe Kind
kindOfName tbl c = case c of
  Original _ (System (NTuple n)) _ -> Just (tupleKi n)
  Original _ (System (NWTuple n)) _ -> Just (tupleKi n)
  _ -> M.lookup c tbl
  where
    tupleKi n = foldr arrKi typeKi (replicate n typeKi)

-- | The type constructor names occurring in a type-level expression (used
--   to keep the kinds of reachable names across modules, D4-c in the
--   notes).
tyConNames :: Ty -> S.Set Name
tyConNames = go
  where
    go (TyConst c) = S.singleton c
    go (TyVar _) = S.empty
    go (TyMetaV _) = S.empty
    go (TyApp t1 t2) = go t1 <> go t2
    go (TyFun m t1 t2) = go m <> go t1 <> go t2
    go (TyInstFun c t) = go c <> go t
    go (TyForAll _ (TyQual cs t)) = foldMap goC cs <> go t
    go (TySyn o u) = go o <> go u
    go (TyMult _) = S.empty
    goC (MSub t ts) = foldMap go (t : ts)
    goC (TyEq t1 t2) = go t1 <> go t2

-- | Replaces the kind metas left in a zonked kind by @Type@ (no kind
--   polymorphism, D1-b in the notes).
defaultKind :: Kind -> Kind
defaultKind (TyMetaV _) = typeKi
defaultKind (TyApp k1 k2) = TyApp (defaultKind k1) (defaultKind k2)
defaultKind k = k

-- | The kind of a well-kinded type-level expression (D3-b in the notes):
--   constants by the table, variables and metas by their own kinds.
--   Ill-kinded applications are never built once kinds are checked, so
--   they are internal errors here.
kindOf :: TypeTable -> Ty -> Kind
kindOf tbl = go
  where
    go (TyConst c) =
      fromMaybe (error $ "kindOf: no kind for " ++ show c) (kindOfName tbl c)
    go (TyVar x) = tyVarKind x
    go (TyMetaV m) = metaKind m
    go (TyApp t1 _) = case go t1 of
      TyCon a [_, k2] | a == nameKiArr -> k2
      _ -> error "kindOf: applying a type-level expression of a non-arrow kind"
    go (TyFun {}) = typeKi
    go (TyInstFun {}) = typeKi
    go (TyForAll {}) = typeKi
    go (TySyn _ t) = go t
    go (TyMult _) = multKi

infixr 4 -@
infixr 4 :-@

(*->) :: Ty -> Ty -> Ty
a *-> b = TyFun (TyMult Omega) a b
infixr 4 *->

(*-@) :: Ty -> Ty -> Ty
a *-@ b = a -@ b
infixr 4 *-@

tyarr :: MultTy -> Ty -> Ty -> Ty
tyarr m a b = TyFun m a b

type TypeTable = M.Map Name Ty
type CTypeTable = M.Map Name ConTy
type SynTable = M.Map Name ([TyVar], Ty)
