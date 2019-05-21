{-# LANGUAGE ViewPatterns #-}
module Language.Sparcl.Typing.Type where

import qualified Data.Map as M

import Language.Sparcl.Pretty as D
import Language.Sparcl.Name
import Language.Sparcl.Multiplicity

import Data.IORef
import Data.Maybe (fromMaybe) 

data Ty = TyCon   Name [Ty]     -- ^ Type constructor 
        | TyVar   TyVar          -- ^ Type variable         
        | TyMetaV MetaTyVar      -- ^ Metavariables (to be substituted in type inf.) 
        | TyForAll [TyVar] QualTy -- ^ polymorphic types 
        | TySyn   Ty Ty          -- ^ type synonym (@TySym o u@ means @u@ but @o@ will be used for error messages)
        | TyMult  Multiplicity   -- ^ 1 or ω
         deriving (Eq, Ord, Show)

data QualTy = TyQual [TyConstraint] BodyTy
  deriving (Eq, Ord, Show)

data TyConstraint = MEqMax Ty Ty Ty 
  deriving (Eq, Ord, Show)

data TyVar = BoundTv Name
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
  ppr (BoundTv n) = ppr n
  ppr (SkolemTv n i) = ppr n D.<> D.text "@" D.<> D.int i 


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
      TyMult One   -> D.group (pprPrec 1 a D.<$> D.text "-o" D.<+> pprPrec 0 b)
      TyMult Omega -> D.group (pprPrec 1 a D.<$> D.text "->" D.<+> pprPrec 0 b)
      _            -> D.group (pprPrec 1 a <+> D.text "#" <+> pprPrec 0 m D.<$> text "->" <+> pprPrec 0 b)

  pprPrec k (TyCon c ts) = parensIf (k > 1) $
    ppr c D.<+> D.align (D.hsep (map (pprPrec 2) ts))

  pprPrec _ (TyVar x) = ppr x 

  pprPrec _ (TyMetaV m) = ppr m

  pprPrec k (TyForAll [] t) = pprPrec k t 
  pprPrec k (TyForAll ns t) = parensIf (k > 0) $ 
    D.text "forall" D.<+>
      D.hsep (map ppr ns) D.<> D.text "."
      D.<+> D.align (pprPrec 0 t)

  pprPrec k (TySyn t _) = pprPrec k t 

  pprPrec _ (TyMult p) = ppr p 

instance Pretty QualTy where
  pprPrec k (TyQual [] t) = pprPrec k t 
  pprPrec k (TyQual cs t) = parensIf (k > 0) $
    sep [d, text "=>" <+> pprPrec 0 t]
    where
      d = parens $ hsep $ punctuate comma (map ppr cs)

instance Pretty TyConstraint where
  ppr (MEqMax ty1 ty2 ty3)
    | ty1 == ty2 =
      hsep [ ppr ty3 <+> text "<=" <+> ppr ty1 ]
    | ty1 == ty3 =
      hsep [ ppr ty2 <+> text "<=" <+> ppr ty1 ]       
    | otherwise = 
      ppr ty1 <+> text "~" <+> ppr ty2 <+> text "*" <+> ppr ty3

data MetaTyVar = MetaTyVar !Int !TyRef 
 
type TyRef = IORef (Maybe MonoTy)

instance Pretty MetaTyVar where
  ppr (MetaTyVar i _) = D.text $ "_" ++ show i 

instance Show MetaTyVar where
  show = prettyShow 

instance Eq MetaTyVar where
  -- MetaTyVar i _ == MetaTyVar j _ = i == j
  MetaTyVar _ i == MetaTyVar _ j = i == j 

instance Ord MetaTyVar where
  MetaTyVar i _ <= MetaTyVar j _ = i <= j 

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
substTyC tbl' (MEqMax t1 t2 t3)  = MEqMax (substTy tbl' t1) (substTy tbl' t2) (substTy tbl' t3)


metaTyVars :: [Ty] -> [MetaTyVar]
metaTyVarsQ :: [QualTy] -> [MetaTyVar]

(metaTyVars, metaTyVarsQ) = (flip (apps goTy) [], flip (apps goQ) [])
  where
    apps _f [] = id
    apps f  (t:ts) = f t . apps f ts 
    
    goTy (TyCon _ ts) = apps goTy ts
    goTy (TyForAll _ t) = goQ t
    goTy (TySyn _ t)    = goTy t
    goTy (TyMetaV m)    = \r -> if m `elem` r then r else m:r
    goTy _              = id 

    goQ (TyQual cs t) = foldr (\c r -> goC c . r) (goTy t) cs

    goC :: TyConstraint -> [MetaTyVar] -> [MetaTyVar]
    goC (MEqMax t1 t2 t3)  = goTy t1 . goTy t2 . goTy t3 

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
