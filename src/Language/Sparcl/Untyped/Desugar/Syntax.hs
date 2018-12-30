module Language.Sparcl.Untyped.Desugar.Syntax where

import Language.Sparcl.Name
import Language.Sparcl.Literal
import Language.Sparcl.SrcLoc 

import qualified Language.Sparcl.Untyped.Syntax as S


import Language.Sparcl.Pretty 
import qualified Text.PrettyPrint.ANSI.Leijen as D


data Ty = TyCon   QName [Ty]     -- ^ Type constructor 
        | TyVar   Name           -- ^ Type variable         
        | TyMetaV MetaTyVar      -- ^ Metavariables (to be substituted in type inf.) 
        | TyForAll [Name] BodyTy -- ^ polymorphic types 
        | TySyn   Ty Ty          -- ^ type synonym (@TySym o u@ means @u@ but @o@ will be used for error messages) 
         deriving (Eq, Show)

instance Pretty Ty where
  pprPrec _ (TyCon c []) = ppr c
  pprPrec k (TyCon c [a,b]) | c == nameTyArr = parensIf (k > 0) $ 
    D.group $ (pprPrec 1 a D.<$> D.text "->" D.<+> pprPrec 0 b)
  pprPrec k (TyCon c ts) = parensIf (k > 1) $
    ppr c D.<+> D.align (D.hsep (map (pprPrec 2) ts))

  pprPrec _ (TyVar x) = ppr x 

  pprPrec _ (TyMetaV m) = ppr m
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


type LExp = Loc Exp 
data Exp 
  = Lit Literal
  | Var QName
  | App LExp LExp
  | Abs Name LExp
  | Con QName [LExp]
  | Bang LExp
  | Case LExp [ (LPat, LExp ) ]
  | Lift LExp LExp
  | Sig  LExp Ty
  | Let  [LDecl] LExp
  | Unlift LExp 

  | RCon QName [LExp]
  | RCase LExp [ (LPat, LExp, LExp ) ]
  | RPin  LExp LExp
  deriving Show 

instance Pretty (Loc Exp) where
  pprPrec k = pprPrec k . unLoc

instance Pretty Exp where
  pprPrec _ (Lit l) = ppr l
  pprPrec _ (Var q) = ppr q
  pprPrec k (App e1 e2) = parensIf (k > 9) $
    pprPrec 9 e1 D.<+> pprPrec 10 e2
  pprPrec k (Abs x e) = parensIf (k > 0) $ D.group $ D.align $ 
    D.text "\\" D.<> ppr x D.<+> D.nest 2 (D.text "->" D.<$> D.align (pprPrec 0 e))

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

  pprPrec _ (PCon c []) = ppr c 
  pprPrec k (PCon c ps) = parensIf (k > 0) $
    ppr c D.<+> D.hsep (map (pprPrec 1) ps)
  pprPrec _ (PBang p)   =
    D.text "!" D.<+> pprPrec 1 p

freeVarsP :: Pat -> [Name]
freeVarsP (PVar n) = [n]
freeVarsP (PCon _ ps) = concatMap (freeVarsP . unLoc) ps
freeVarsP (PBang p)   = freeVarsP $ unLoc p 


type LDecl = Loc Decl 
data Decl
  = DDef Name (Maybe Ty) LExp
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
    D.text "-- " D.<+> ppr l D.<$> ppr d

  pprList _ = D.vsep . map ppr 
  

data TopDecl
  = NormalDecl Decl
  | Fixity     QName S.Prec S.Assoc
