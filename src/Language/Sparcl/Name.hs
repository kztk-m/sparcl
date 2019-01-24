module Language.Sparcl.Name where

import Language.Sparcl.Pretty as D
import Control.DeepSeq 


data NameBase = User   String
              | System !SystemName
              deriving (Eq, Ord, Show) 

instance NFData NameBase where
  rnf (User n) = rnf n
  rnf (System _) = ()

instance Pretty NameBase where 
  ppr (User n)   = text n
  ppr (System s) = ppr s  

data SystemName = NTuple Int | NLinearArrow | NBang | NRev 
  deriving (Eq, Ord, Show)

instance Pretty SystemName where
  ppr (NTuple n)   = text "<Tup" <+> int n <> text ">"
  ppr NLinearArrow = text "-o"
  ppr NBang        = text "!"
  ppr NRev         = text "rev"


data SurfaceName
  = Qual ModuleName NameBase
  | Bare              NameBase
  | BuiltIn           Name     -- for built-in things
  deriving (Eq, Ord, Show) 

data Name
  = Local     NameBase
  | Original  ModuleName NameBase SurfaceName     
  | Alpha     !Int NameBase
  | Generated !Int Phase
  deriving Show

data Phase = Desugaring | CodeGen deriving (Eq, Show, Ord)

instance NFData Phase where
  rnf x = seq x ()

instance Eq Name where
  Local n1 == Local n2 = n1 == n2
  Original m1 n1 _ == Original m2 n2 _ = m1 == m2 && n1 == n2
  Alpha i1 _ == Alpha i2 _ = i1 == i2
  Generated i1 p1 == Generated i2 p2 = i1 == i2 && (p1 == p2)
  _ == _ = False 

instance Ord Name where
  compare (Local n1) (Local n2) = compare n1 n2 
  compare (Local _)   _         = LT

  compare (Original _ _ _) (Local _) = GT
  compare (Original m1 n1 _) (Original m2 n2 _) = compare (m1, n1) (m2, n2)
  compare (Original _ _ _)   _       = LT 

  compare (Alpha _ _)  (Generated _ _) = LT
  compare (Alpha i1 _) (Alpha i2 _)  = compare i1 i2 
  compare (Alpha _ _)  _             = GT

  compare (Generated i1 p1) (Generated i2 p2) = compare (p1, i1) (p2, i2)
  compare (Generated _ _) _              = GT


instance NFData SurfaceName where
  rnf (Qual m n) = rnf (m, n)
  rnf (Bare   n)   = rnf n
  rnf (BuiltIn n)  = rnf n 

instance NFData Name where
  rnf (Local n)      = rnf n
  rnf (Original m n orig) = rnf (m, n, orig)
  rnf (Alpha _ n)      = rnf n
  rnf (Generated _ p)  = rnf p

newtype ModuleName = ModuleName String
  deriving (Show, Eq, Ord, NFData) 


instance Pretty ModuleName where
  ppr (ModuleName m) = text m

instance Pretty SurfaceName where 
  ppr (Qual m n) = ppr m <> text "." <> ppr n
  ppr (Bare     n) = ppr n
  ppr (BuiltIn  n) = ppr n 

-- Basically, the method pretty-print names as the original without additional
-- information introduced in the system. 
instance Pretty Name where
  ppr (Generated  i p) = text "_" <> text (case p of { Desugaring -> "d" ; CodeGen -> "c"}) <> int i 
  ppr (Alpha _i   n)   = ppr n
  ppr (Local n)        = ppr n
  ppr (Original _ _ o) = ppr o

moduleNameToStr :: ModuleName -> String
moduleNameToStr (ModuleName ms) = ms

-- data QName = QName ModuleName Name -- qualified name (for global names)
--            | BName Name            -- bare name
--            deriving (Show, Eq, Ord) 

-- instance NFData QName where
--   rnf (QName m n) = rnf (m, n)
--   rnf (BName n)   = rnf n 

-- instance Pretty QName where
--   ppr (QName m n) =
--     (case n of
--         Generated _ -> id 
--         NormalName (c:_) | isLower c || isUpper c -> id
--         _                            -> D.parens) $ 
--     D.text (moduleNameToStr m) D.<> D.text "." D.<> ppr n
--   ppr (BName n)   = ppr n 
  

baseModule :: ModuleName
baseModule = ModuleName "Base"

nameInBase :: NameBase -> Name
nameInBase bn = Original baseModule bn (Qual baseModule bn)

conTrue :: Name
conTrue = nameInBase (User "True")

conFalse :: Name
conFalse = nameInBase (User "False")

nameTuple :: Int -> Name
nameTuple n =
  let bn = System (NTuple n)
  in Original baseModule bn (Bare bn) 

checkNameTuple :: Name -> Maybe Int
checkNameTuple (Original _ (System (NTuple m)) _) = Just m
checkNameTuple _                                  = Nothing 

nameUnit :: Name
nameUnit = nameTuple 0 

nameTyTuple :: Int -> Name
nameTyTuple = nameTuple

nameTyBang :: Name
nameTyBang = nameInBase (System NBang) 

nameTyRev :: Name
nameTyRev = nameInBase (System NRev)

nameTyInt :: Name
nameTyInt = nameInBase (User "Int")

nameTyDouble :: Name
nameTyDouble = nameInBase (User "Double")

nameTyChar :: Name
nameTyChar = nameInBase (User "Char")

nameTyBool :: Name
nameTyBool = nameInBase (User "Bool") 

nameTyList :: Name
nameTyList = nameInBase (User "List")

nameTyLArr :: Name
nameTyLArr = nameInBase (System NLinearArrow) 

nameKindType :: Name
nameKindType = nameInBase (User "Type") 
