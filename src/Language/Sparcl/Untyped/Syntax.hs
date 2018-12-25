module Language.Sparcl.Untyped.Syntax where

import Language.Sparcl.SrcLoc

-- Surface Syntax

data Name = NormalName String
          | MixFix [String] Bool Bool
          | Generated  Int
  deriving (Ord, Eq, Show) 

-- "if_then_else_" is represented by MixFix ["if", "then", "else"] False True 



type ModuleName = [String]

data QName = QName ModuleName Name -- qualified name (for global names)
           | BName Name            -- bare name

data Literal
  = LitInt    Int
  | LitDouble Double
  | LitChar   Char 

type LTyp = Loc Typ -- located types (not linear) 

data Typ
  = TVar    QName
  | TBang   LTyp
  | TCon    QName [Typ]
  | TRev    LTyp
  | TArr    Typ  LTyp
  | TForall Name LTyp

type LExp = Loc Exp 

data Exp
  = Lit Literal
  | Var QName
  | App LExp   LExp
  | Abs [Pat] LExp
  | Con QName [LExp]
  | Bang LExp 
  | Case LExp [ (Pat, Clause) ]
  | Lift LExp LExp
  | Sig  LExp Typ
  | Let  [LDecl] LExp 

  | RCon QName [LExp]
  | RCase LExp [ (Pat, Clause) ]
  | RPin  LExp LExp

type LPat = Loc Pat
data Pat = PVar Name
         | PCon QName [LPat]
         | PBang LPat
         | PREV  LPat

data Clause = Clause { body :: LExp, whereClause :: [LDecl], withExp :: Maybe LExp } 

newtype Prec  = Prec Int
  deriving (Eq, Ord) 

instance Bounded Prec where
  minBound = Prec 0
  maxBound = Prec maxBound 

instance Enum Prec where
  toEnum = Prec
  fromEnum (Prec n) = n 

data Assoc = L | R | N 

type LDecl = Loc Decl 

data Decl
  = DDef QName [ ([LPat],  Clause) ] 
  | DSig QName Typ
  | DFixity QName Prec Assoc
  | DMutual [LDecl] 
  -- | Modules are not supported yet.
  | DModule QName [LDecl]
  | DImport QName 
  | DOpen   QName 
