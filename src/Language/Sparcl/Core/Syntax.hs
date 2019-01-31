module Language.Sparcl.Core.Syntax (
  Exp(..), Bind, 
  Pat(..), 
  freeVarsP, 
  module Language.Sparcl.Name,
  module Language.Sparcl.Literal,
  module Language.Sparcl.SrcLoc,
  S.Module(..), S.Import(..),
  DDecl(..), TDecl(..)
  ) where

import Language.Sparcl.Name
import Language.Sparcl.Literal
import Language.Sparcl.SrcLoc 

import Language.Sparcl.Typing.Type

import qualified Language.Sparcl.Surface.Syntax as S


import Language.Sparcl.Pretty 
import qualified Text.PrettyPrint.ANSI.Leijen as D


data Exp n
  = Lit Literal
  | Var n
  | App (Exp n) (Exp n)
  | Abs n (Exp n)
  | Con n [Exp n]
  | Bang (Exp n)
  | Case (Exp n) [ (Pat n, Exp n) ]
  | Let  (Bind n) (Exp n)
  | Lift (Exp n) (Exp n)
  | Unlift (Exp n)

  | RCon n [Exp n]
  | RCase (Exp n) [ (Pat n, Exp n, Exp n ) ]
  | RPin  (Exp n) (Exp n)

     

instance Pretty n => Pretty (Exp n) where
  pprPrec _ (Lit l) = ppr l
  pprPrec _ (Var q) = ppr q
  pprPrec k (App e1 e2) = parensIf (k > 9) $
    pprPrec 9 e1 D.<+> pprPrec 10 e2
  pprPrec k (Abs x e) = parensIf (k > 0) $ D.group $ D.align $ 
    D.text "\\" D.<> ppr x D.<+> D.nest 2 (D.text "->" D.<$> D.align (pprPrec 0 e))

  -- pprPrec _ (Con c es)
  --   | c == nameTuple (length es) =
  --       D.parens (D.hsep $ D.punctuate D.comma $ map (pprPrec 0) es)

  pprPrec _ (Con c []) =
    ppr c 

  pprPrec _ (Con c es) =
    ppr c <> align (parens $ hsep $ punctuate comma $ (map (pprPrec 0) es))
    -- parensIf (k > 9) $
    -- ppr c D.<+> D.hsep (map (pprPrec 10) es)

  pprPrec _ (Bang e) =
    D.text "!" D.<> pprPrec 10 e

  pprPrec k (Case e ps) = parensIf (k > 0) $ D.group $ D.align $ 
    D.text "case" D.<+> pprPrec 0 e D.<+> D.text "of" D.<$>
    D.vsep (map pprPs ps) D.<$>
    D.text "end"
    where
      pprPs (p, c) =
        D.group $ D.text "|" D.<+> D.align (pprPrec 1 p D.<+> D.text "->" D.<> (D.nest 2 $ D.line D.<> ppr c))

  pprPrec k (Lift e1 e2) = parensIf (k > 9) $
    D.text "lift" D.<+> D.align (pprPrec 10 e1 D.</> pprPrec 10 e2)

  pprPrec k (Let ds e) = parensIf (k > 0) $
    D.align $
     D.text "let" D.<+> D.align (D.semiBraces $ map ppr ds) D.</>
     D.text "in" D.<+> pprPrec 0 e

  pprPrec k (Unlift e) = parensIf (k > 9) $
    D.text "unlift" D.<+> D.align (pprPrec 10 e) 

  pprPrec k (RCon c es) = parensIf (k > 9) $
    D.text "rev" D.<+> ppr c D.<+>
     D.hsep (map (pprPrec 10) es)

  pprPrec k (RCase e0 ps) = parensIf (k > 0) $ D.group $ D.align $ 
    D.text "case" D.<+> pprPrec 0 e0 D.<+> D.text "of" D.<$>
    D.vsep (map pprPs ps) D.<$> 
    D.text "end"
    where
      pprPs (p, c, e) =
        D.text "|" D.<+> D.align (D.text "rev" D.<+> pprPrec 1 p D.<+> D.text "->" D.<+> (D.nest 2 $ ppr c D.</> D.text "with" D.<+> D.align (ppr e)))

  pprPrec k (RPin e1 e2) = parensIf (k > 9) $
    D.text "pin" D.<+> pprPrec 10 e1 D.<+> pprPrec 10 e2 
        

data Pat n = PVar n
           | PCon n [Pat n]
           | PBang (Pat n)
  deriving Show 

instance Pretty n => Pretty (Pat n) where
  pprPrec _ (PVar n) = ppr n

  pprPrec _ (PCon c []) = ppr c 
  pprPrec k (PCon c ps) = parensIf (k > 0) $
    ppr c D.<> align (parens $ D.hsep $ punctuate comma $ map (pprPrec 1) ps)
  pprPrec _ (PBang p)   =
    D.text "!" D.<> pprPrec 1 p

freeVarsP :: Pat n -> [n]
freeVarsP (PVar n) = [n]
freeVarsP (PCon _ ps) = concatMap freeVarsP ps
freeVarsP (PBang p)   = freeVarsP p 


type Bind n = [ (n, Exp n) ] 


-- | Datatype declarations 
data DDecl n = DDecl n [TyVar] [(n, [Ty])]

-- | Type synonym declarations 
data TDecl n = TDecl n [TyVar] Ty
