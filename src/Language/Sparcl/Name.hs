module Language.Sparcl.Name where

data Name = NormalName String
          | Generated  Int
  deriving (Ord, Eq, Show) 


type ModuleName = [String]

moduleNameToStr :: ModuleName -> String
moduleNameToStr ms = foldr1 (\a b -> a ++ "." ++ b) ms 

data QName = QName ModuleName Name -- qualified name (for global names)
           | BName Name            -- bare name
           deriving (Show, Eq, Ord) 

baseModule :: ModuleName
baseModule = ["Base"]

conTrue :: QName
conTrue = QName baseModule (NormalName "True")

conFalse :: QName
conFalse = QName baseModule (NormalName "False")

tupleName :: Int -> QName
tupleName n = QName baseModule (NormalName $ replicate n ',')

unitName :: QName
unitName = tupleName 0 
