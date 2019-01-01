module Language.Sparcl.Untyped.Syntax where

import Language.Sparcl.SrcLoc

import Language.Sparcl.Pretty 
import qualified Text.PrettyPrint.ANSI.Leijen as D

-- Surface Syntax

import Language.Sparcl.Name
import Language.Sparcl.Literal

makeTupleExp :: [LExp] -> LExp
makeTupleExp [e] = e
makeTupleExp es  = noLoc $ Con (nameTuple $ length es) es

makeTuplePat :: [LPat] -> LPat
makeTuplePat [p] = p
makeTuplePat ps = noLoc $ PCon (nameTuple $ length ps) ps 

type LTy = Loc Ty -- located types (not linear) 

data Ty
  = TVar    Name
  | TCon    QName [LTy]
  | TForall Name LTy
  deriving Show

instance Pretty Ty where
  pprPrec _ (TVar n) = ppr n
  pprPrec k (TCon c ts) = parensIf (k > 0) $
    ppr c D.<+> (D.hsep $ map (pprPrec 1) ts)
  pprPrec k (TForall n t) = parensIf (k > 0) $
    D.text "forall" D.<+> ppr n D.<+> pprPrec 0 t

instance Pretty (Loc Ty) where
  pprPrec k = pprPrec k . unLoc 

type LExp = Loc Exp 

-- TODO: add "if" expression 
data Exp
  = Lit Literal
  | Var QName
  | App LExp   LExp
  | Abs [LPat] LExp
  | Con QName [LExp]
  | Bang LExp 
  | Case LExp [ (LPat, Clause) ]
  | Lift LExp LExp
  | Sig  LExp LTy
  | Let  [LDecl] LExp

  | Parens LExp -- for operators
  | Op  QName LExp LExp 

  | Unlift LExp
  | Fwd    LExp
  | Bwd    LExp 

  | RCon QName [LExp]
--  | RCase LExp [ (LPat, Clause) ]
  | RPin  LExp LExp
  deriving Show -- for debugging

instance Pretty LExp where
  pprPrec k = pprPrec k . unLoc 

instance Pretty Exp where
  pprPrec _ (Lit l) = ppr l
  pprPrec _ (Var q) = ppr q
  pprPrec k (App e1 e2) = parensIf (k > 9) $
    pprPrec 9 e1 D.<+> pprPrec 10 e2
  pprPrec k (Abs x e) = parensIf (k > 0) $
    D.text "\\" D.<> D.hsep (map ppr x) D.<+> D.text "->" D.<+> D.align (D.nest 2 (pprPrec 0 e))

  pprPrec _ (Con c []) =
    ppr c 

  pprPrec k (Con c es) = parensIf (k > 9) $
    ppr c D.<+> D.hsep (map (pprPrec 10) es)

  pprPrec _ (Bang e) =
    D.text "!" D.<> pprPrec 10 e

  pprPrec k (Case e ps) = parensIf (k > 0) $ 
    D.text "case" D.<+> pprPrec 0 e D.<+> D.text "of" D.</>
    D.vcat (map pprPs ps) D.</>
    D.text "end" 
    where
      pprPs (p, c) = D.text "|" D.<+>
                     D.align (pprPrec 1 p D.<+> D.text "->" D.<+> (D.nest 2 $ ppr c))

  pprPrec k (Lift e1 e2) = parensIf (k > 9) $
    D.text "lift" D.<+> D.align (pprPrec 10 e1 D.</> pprPrec 10 e2)

  pprPrec k (Unlift e) = parensIf (k > 9) $
    D.text "unlift" D.<+> D.align (pprPrec 10 e) 

  pprPrec k (Fwd e) = parensIf (k > 9) $
    D.text "forward" D.<+> D.align (pprPrec 10 e)

  pprPrec k (Bwd e) = parensIf (k > 9) $
    D.text "backward" D.<+> D.align (pprPrec 10 e) 

  pprPrec _ (Parens e) = D.parens (pprPrec 0 e)
  pprPrec k (Op q e1 e2) = parensIf (k > 8) $
    pprPrec 8 e1 D.<+> ppr q D.<+> pprPrec 9 e2 

  pprPrec k (Sig e t) = parensIf (k > 0) $
    pprPrec 0 e D.<+> D.colon D.<+> ppr t

  pprPrec k (Let ds e) = parensIf (k > 0) $
    D.align $
     D.text "let" D.<+> D.align (D.semiBraces $ map ppr ds) D.</>
     D.text "in" D.<+> pprPrec 0 e

  pprPrec k (RCon c es) = parensIf (k > 9) $
    D.text "rev" D.<+> ppr c D.<+>
     D.hsep (map (pprPrec 10) es)

  pprPrec k (RPin e1 e2) = parensIf (k > 9) $
    D.text "pin" D.<+> pprPrec 10 e1 D.<+> pprPrec 10 e2 
        
    

type LPat = Loc Pat
data Pat = PVar Name
         | PCon QName [LPat]
         | PBang LPat
         | PREV  LPat
         | PWild 
         -- TODO: Add literal pattern
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
  pprPrec k (PREV p) = parensIf (k > 0) $
    D.text "rev" D.<+> pprPrec 1 p 
  
  pprPrec _ PWild = D.text "_" 

data Clause = Clause { body :: LExp, whereClause :: [LDecl], withExp :: Maybe LExp } 
  deriving Show 

instance Pretty Clause where
  ppr (Clause e ds w) =
    ppr e D.<+> (case w of
                   Nothing -> D.empty
                   Just e' -> D.text "with" D.<+> D.align (ppr e'))
    D.<> pprWhere ds
    where
      pprWhere [] = D.empty 
      pprWhere ds = 
        D.nest 2 (D.line D.<> D.nest 2 (D.text "where" D.</>
                                         D.align (D.vcat $ map ppr ds)) D.</> D.text "end")
       

newtype Prec  = Prec Int
  deriving (Eq, Ord, Show) 

instance Pretty Prec where
  ppr (Prec k) = D.int k 

instance Bounded Prec where
  minBound = Prec 0
  maxBound = Prec maxBound 

instance Enum Prec where
  toEnum = Prec
  fromEnum (Prec n) = n 

data Assoc = L | R | N 
  deriving (Eq, Ord, Show)

instance Pretty Assoc where
  ppr L = D.text "left"
  ppr R = D.text "right"
  ppr N = D.empty 

type LDecl = Loc Decl 

data CDecl
  = CDecl Name  -- constructor name
          [LTy] -- constructor argument
  deriving Show

instance Pretty (Loc CDecl) where
  ppr (Loc l d) =
    D.text "{-" D.<+> ppr l D.<+> D.text "-}"
    D.<$> ppr d 
    
instance Pretty CDecl where
  ppr (CDecl c []) = ppr c
  ppr (CDecl c args) = 
    ppr c D.<+> D.hsep [ pprPrec 1 a | a <- args ] 

data TopDecl
  = DDecl Decl 
  | DData Name [Name] [Loc CDecl]
  | DType Name [Name] LTy

data Decl
  = DDef Name [ ([LPat],  Clause) ] 
  | DSig Name LTy
  | DFixity Name Prec Assoc -- TODO: will be replaced with "DDefOp" 
  -- | DMutual [LDecl] 
   deriving Show

instance Pretty (Loc TopDecl) where
  ppr (Loc l d) =
    D.text "{- " D.<+> ppr l D.<+> D.text "-}"
    D.<$> ppr d  

  pprList _ ds =
    D.vsep (map ppr ds) 
  

instance Pretty TopDecl where
  ppr (DData t targs cs) =
    D.hsep [D.text "data", ppr t, D.align $ D.hsep (map ppr targs)] D.<>
    D.nest 2 (D.line D.<> D.text "=" D.<+> D.group (pprCs cs))
    where
      pprCs []     = D.empty
      pprCs [c]    = ppr c
      pprCs (c:cs) = ppr c D.<$> D.text "|" D.<+> pprCs cs 

  ppr (DType t targs ty) =
    D.hsep [D.text "type", ppr t, D.align $ D.hsep (map ppr targs),
            D.align (ppr ty)] 

  ppr (DDecl d) = ppr d 

instance Pretty Decl where
  ppr (DDef n pcs) =
    D.text "def" D.<+> ppr n D.<+>
    D.align (D.nest (-2) $
            D.hcat $ D.punctuate (D.line D.<> D.text "|" D.<> D.space)
                                 (map pprPC pcs))
    where
      pprPC (ps, c) =
        D.align $
          D.hsep (map (pprPrec 1) ps) D.<+> D.text "=" D.<+> ppr c

  ppr (DSig n t) =
    D.text "sig" D.<+> ppr n D.<+> D.colon D.<+> ppr t

  ppr (DFixity n k a) =
    D.text "fixity" D.<+> ppr n D.<+> ppr k D.<+> ppr a

            

  -- ppr (DMutual ds) =
  --   D.text "mutual" D.<+> D.semiBraces (map ppr ds) 
            
  pprList _ ds =
    D.vsep (map ppr ds) 
                                           
instance Pretty (Loc Decl) where
  ppr (Loc l d) =
    D.text "{- " D.<+> ppr l D.<+> D.text "-}"
    D.<$> ppr d  

  pprList _ ds =
    D.vsep (map ppr ds) 
    

data Module
  = Module ModuleName (Maybe [Export]) [Import] [Loc TopDecl]

type Export = QName
data Import = Import { importModuleName :: ModuleName, importingNames :: Maybe [QName] }
