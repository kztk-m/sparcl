module Language.Sparcl.Untyped.Desugar.Syntax (
  Ty(..), MetaTyVar(..), BodyTy, PolyTy, MonoTy,
  bangTy, revTy, boolTy, (-@), tupleTy,
  
  Exp(..), OLExp, Orig(..), noOrig, 
  Pat(..), LPat,
  Decl(..), LDecl,
  TypeTable, SynTable, 
  freeVarsP, freeVars, freeBVars, TyVar(..), 
  S.Prec(..), S.Assoc(..), OpTable ,
  module Language.Sparcl.Name,
  module Language.Sparcl.Literal,
  module Language.Sparcl.SrcLoc,
  S.Module(..), S.Import(..)
  ) where

import Language.Sparcl.Name
import Language.Sparcl.Literal
import Language.Sparcl.SrcLoc 

import qualified Data.Map as M
import qualified Data.Set as S 

import qualified Language.Sparcl.Untyped.Syntax as S


import Language.Sparcl.Pretty 
import qualified Text.PrettyPrint.ANSI.Leijen as D


data Ty = TyCon   QName [Ty]     -- ^ Type constructor 
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

data MetaTyVar = MetaTyVar Int SrcSpan
  deriving Show

instance Pretty MetaTyVar where
  ppr (MetaTyVar i _) = D.text $ "_" ++ show i 

instance Eq MetaTyVar where
  MetaTyVar i _ == MetaTyVar j _ = i == j 

type BodyTy = MonoTy  -- forall body. only consider rank 1
type PolyTy = Ty      -- polymorphic types
type MonoTy = Ty      -- monomorphic types


bangTy :: Ty -> Ty
bangTy ty = TyCon nameTyBang [ty]

revTy :: Ty -> Ty
revTy ty = TyCon nameTyRev [ty]

(-@) :: Ty -> Ty -> Ty
t1 -@ t2 = TyCon nameTyLArr [t1, t2]

boolTy :: Ty
boolTy = TyCon nameTyBool []

tupleTy :: [Ty] -> Ty
tupleTy ts = TyCon (nameTyTuple $ length ts) ts 

infixr 4 -@ 

data Orig a b = Orig { original :: Maybe a, desugared :: b }
  deriving Show
type OLExp = Orig S.LExp (Loc Exp)

noOrig :: d -> Orig o d
noOrig = Orig Nothing 

-- type LExp = Loc Exp 
data Exp 
  = Lit Literal
  | Var QName
  | App OLExp OLExp
  | Abs Name OLExp
  | Con QName [OLExp]
  | Bang OLExp
  | Case OLExp [ (LPat, OLExp ) ]
  | Lift OLExp OLExp
  | Sig  OLExp Ty
  | Let  [LDecl] OLExp
  | Unlift OLExp 

  | RCon QName [OLExp]
  | RCase OLExp [ (LPat, OLExp, OLExp ) ]
  | RPin  OLExp OLExp
  deriving Show 

freeBVars :: OLExp -> [ Name ]
freeBVars e = [ n | BName n <- freeVars e ] 

freeVars :: OLExp -> [ QName ]
freeVars e = S.toList $ go (S.fromList []) e (S.fromList [])
  where
    go bound e = go' bound (unLoc $ desugared e)

    go' _bound (Lit _) r = r
    go' bound (Var q) r
      | S.member q bound = r
      | otherwise        = S.insert q r
    go' bound (App e1 e2) r =
      go bound e1 (go bound e2 r)

    go' bound (Abs x e) r =
      go (S.insert (BName x) bound) e r
    go' bound (Con _ es) r =
      foldl (flip $ go bound) r es
    go' bound (Bang e) r = go bound e r
    go' bound (Case e alts) r =
      go bound e (goAlts bound alts r)
    go' bound (Lift e1 e2) r =
      go bound e1 (go bound e2 r)
    go' bound (Sig e _) r = go bound e r
    go' bound (Let decls e) r = 
      let ns = [ n | Loc _ (DDef n _ _) <- decls ]
          es = [ e | Loc _ (DDef _ _ e) <- decls ]
          bound' = foldl (flip S.insert) bound ns 
      in go bound' e $ foldl (flip $ go bound') r es 

    go' bound (Unlift e) r = go bound e r
    go' bound (RCon _ es) r =
      foldl (flip $ go bound) r es 
    go' bound (RCase e ralts) r =
      go bound e (goRAlts bound ralts r)
    go' bound (RPin e1 e2) r =
      go bound e1 (go bound e2 r)

    goAlts _bound [] r = r
    goAlts bound ((p,e):alts) r =
      let ns = freeVarsP (unLoc p)
          bound' = foldl (flip S.insert) bound $ map BName ns
      in go bound' e (goAlts bound alts r)

    goRAlts _bound [] r = r
    goRAlts bound ((p,e,e'):alts) r =
      let ns = freeVarsP (unLoc p)
          bound' = foldl (flip S.insert) bound $ map BName ns
      in go bound' e $ go bound e' $ goRAlts bound alts r 
      

instance Pretty d => Pretty (Orig o d) where
  pprPrec k (Orig _ d) = pprPrec k d 

instance Pretty (Loc Exp) where
  pprPrec k = pprPrec k . unLoc

instance Pretty Exp where
  pprPrec _ (Lit l) = ppr l
  pprPrec _ (Var q) = ppr q
  pprPrec k (App e1 e2) = parensIf (k > 9) $
    pprPrec 9 e1 D.<+> pprPrec 10 e2
  pprPrec k (Abs x e) = parensIf (k > 0) $ D.group $ D.align $ 
    D.text "\\" D.<> ppr x D.<+> D.nest 2 (D.text "->" D.<$> D.align (pprPrec 0 e))

  pprPrec _ (Con c es)
    | c == nameTuple (length es) =
        D.parens (D.hsep $ D.punctuate D.comma $ map (pprPrec 0) es)

  pprPrec _ (Con c []) =
    ppr c 

  pprPrec k (Con c es) = parensIf (k > 9) $
    ppr c D.<+> D.hsep (map (pprPrec 10) es)

  pprPrec _ (Bang e) =
    D.text "!" D.<> pprPrec 10 e

  pprPrec k (Case e ps) = parensIf (k > 0) $ D.group $ D.align $ 
    D.text "case" D.<+> pprPrec 0 e D.<+> D.text "of" D.<$>
    D.vcat (map pprPs ps) D.<$>
    D.text "end"
    where
      pprPs (p, c) =
        D.group $ D.text "|" D.<+> D.align (pprPrec 1 p D.<+> D.text "->" D.<> (D.nest 2 $ D.line D.<> ppr c))

  pprPrec k (Lift e1 e2) = parensIf (k > 9) $
    D.text "lift" D.<+> D.align (pprPrec 10 e1 D.</> pprPrec 10 e2)

  pprPrec k (Sig e t) = parensIf (k > 0) $
    pprPrec 0 e D.<+> D.colon D.<+> ppr t

  pprPrec k (Let ds e) = parensIf (k > 0) $
    D.align $
     D.text "let" D.<+> D.align (D.semiBraces $ map ppr ds) D.</>
     D.text "in" D.<+> pprPrec 0 e

  pprPrec k (Unlift e) = parensIf (k > 9) $
    D.text "unlift" D.<+> D.align (pprPrec 10 e) 

  pprPrec k (RCon c es) = parensIf (k > 9) $
    D.text "rev" D.<+> ppr c D.<+>
     D.hsep (map (pprPrec 10) es)

  pprPrec k (RCase e ps) = parensIf (k > 0) $ D.group $ D.align $ 
    D.text "case" D.<+> pprPrec 0 e D.<+> D.text "of" D.<$>
    D.vcat (map pprPs ps) D.<$> 
    D.text "end"
    where
      pprPs (p, c, e) =
        D.text "|" D.<+> D.align (D.text "rev" D.<+> pprPrec 1 p D.<+> D.text "->" D.<+> (D.nest 2 $ ppr c D.</> D.text "with" D.<+> D.align (ppr e)))

  pprPrec k (RPin e1 e2) = parensIf (k > 9) $
    D.text "pin" D.<+> pprPrec 10 e1 D.<+> pprPrec 10 e2 
        


type LPat = Loc Pat
data Pat = PVar Name
         | PCon QName [LPat]
         | PBang LPat
  deriving Show 

instance Pretty (Loc Pat) where
  pprPrec k = pprPrec k . unLoc 

instance Pretty Pat where
  pprPrec _ (PVar n) = ppr n

  pprPrec _ (PCon c ps)
    | c == nameTuple (length ps) =
        D.parens $ D.hsep $ D.punctuate D.comma $ map (pprPrec 0) ps 

  pprPrec _ (PCon c []) = ppr c 
  pprPrec k (PCon c ps) = parensIf (k > 0) $
    ppr c D.<+> D.hsep (map (pprPrec 1) ps)
  pprPrec _ (PBang p)   =
    D.text "!" D.<> pprPrec 1 p

freeVarsP :: Pat -> [Name]
freeVarsP (PVar n) = [n]
freeVarsP (PCon _ ps) = concatMap (freeVarsP . unLoc) ps
freeVarsP (PBang p)   = freeVarsP $ unLoc p 


type LDecl = Loc Decl 
data Decl
  = DDef QName (Maybe Ty) OLExp
  deriving Show

instance Pretty Decl where
  ppr (DDef n m e) =
    D.text "def" D.<+> ppr n 
    D.<> (case m of
            Nothing -> D.empty
            Just  t -> D.space D.<> D.colon D.<+> D.group (D.align (ppr t)))
    D.<+> D.nest 2 (D.text "=" D.<$> D.group (ppr e))
    
  pprList _ = D.vsep . map ppr 

instance Pretty LDecl where
  ppr (Loc l d) =
    D.text "{- " D.<+> ppr l D.<+> D.text "-}"
    D.<$> ppr d

  pprList _ = D.vsep . map ppr 
  
type OpTable = M.Map QName (S.Prec, S.Assoc) 

type TypeTable = M.Map QName Ty
type SynTable  = M.Map QName ([TyVar], Ty)

