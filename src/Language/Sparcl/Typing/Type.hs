{-# LANGUAGE ViewPatterns #-}
module Language.Sparcl.Typing.Type where

import qualified Data.Map as M

import Language.Sparcl.Pretty as D
import Language.Sparcl.Name

import Data.IORef 

data Ty = TyCon   Name [Ty]     -- ^ Type constructor 
        | TyVar   TyVar          -- ^ Type variable         
        | TyMetaV MetaTyVar      -- ^ Metavariables (to be substituted in type inf.) 
        | TyForAll [TyVar] BodyTy -- ^ polymorphic types 
        | TySyn   Ty Ty          -- ^ type synonym (@TySym o u@ means @u@ but @o@ will be used for error messages) 
         deriving (Eq, Show)

data TyVar = BoundTv Name
           | SkolemTv TyVar Int -- used only for checking of which type is more general. 
  deriving Show 

instance Eq TyVar where
  BoundTv n == BoundTv m = n == m
  SkolemTv _ i == SkolemTv _ j = i == j
  _ == _ = False

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
  pprPrec k (TyCon c [a,b]) | c == nameTyLArr = parensIf (k > 0) $ 
    D.group $ (pprPrec 1 a D.<$> D.text "-o" D.<+> pprPrec 0 b)

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

data MetaTyVar = MetaTyVar !Int !TyRef 
 
type TyRef = IORef (Maybe MonoTy)

instance Pretty MetaTyVar where
  ppr (MetaTyVar i _) = D.text $ "_" ++ show i 

instance Show MetaTyVar where
  show = prettyShow 

instance Eq MetaTyVar where
  -- MetaTyVar i _ == MetaTyVar j _ = i == j
  MetaTyVar _ i == MetaTyVar _ j = i == j 

type BodyTy = MonoTy  -- forall body. only consider rank 1
type PolyTy = Ty      -- polymorphic types
type MonoTy = Ty      -- monomorphic types


bangTy :: Ty -> Ty
bangTy ty = TyCon nameTyBang [ty]

revTy :: Ty -> Ty
revTy ty = TyCon nameTyRev [ty]

(-@) :: Ty -> Ty -> Ty
t1 -@ t2 = TyCon nameTyLArr [t1, t2]

pattern (:-@) :: Ty -> Ty -> Ty 
pattern t1 :-@ t2 <- TyCon ((== nameTyLArr) -> True) [t1, t2] 
  where
    t1 :-@ t2 = TyCon nameTyLArr [t1, t2]

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

type TypeTable = M.Map Name Ty
type SynTable  = M.Map Name ([TyVar], Ty)
