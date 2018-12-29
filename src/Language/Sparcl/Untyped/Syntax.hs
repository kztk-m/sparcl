module Language.Sparcl.Untyped.Syntax where

import Language.Sparcl.SrcLoc

-- Surface Syntax

import Language.Sparcl.Name

makeTupleExp :: [LExp] -> LExp
makeTupleExp [e] = e
makeTupleExp es  = noLoc $ Con (tupleName $ length es) es

makeTuplePat :: [LPat] -> LPat
makeTuplePat [p] = p
makeTuplePat ps = noLoc $ PCon (tupleName $ length ps) ps 

data Literal
  = LitInt    Int
  | LitDouble Double
  | LitChar   Char 
  deriving Show

type LTyp = Loc Typ -- located types (not linear) 

data Typ
  = TVar    QName
  | TBang   LTyp
  | TCon    QName [Typ]
  | TRev    LTyp
  | TArr    Typ  LTyp
  | TForall Name LTyp
  deriving Show

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
  | Sig  LExp Typ
  | Let  [LDecl] LExp 

  | RCon QName [LExp]
--  | RCase LExp [ (LPat, Clause) ]
  | RPin  LExp LExp
  deriving Show -- for debugging

type LPat = Loc Pat
data Pat = PVar Name
         | PCon QName [LPat]
         | PBang LPat
         | PREV  LPat
  deriving Show 

data Clause = Clause { body :: LExp, whereClause :: [LDecl], withExp :: Maybe LExp } 
  deriving Show 

newtype Prec  = Prec Int
  deriving (Eq, Ord, Show) 

instance Bounded Prec where
  minBound = Prec 0
  maxBound = Prec maxBound 

instance Enum Prec where
  toEnum = Prec
  fromEnum (Prec n) = n 

data Assoc = L | R | N 
  deriving (Eq, Ord, Show)

type LDecl = Loc Decl 

data Decl
  = DDef Name [ ([LPat],  Clause) ] 
  | DSig Name Typ
  | DFixity QName Prec Assoc
  | DMutual [LDecl] 
   deriving Show 

-- data Module
--   = Module ModuleName [Export] [Import]  [Decl]

type Export = QName
data Import = Import { importModuleName :: ModuleName, importingNames ::  [QName] }
