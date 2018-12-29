module Language.Sparcl.Name where

import Language.Sparcl.Pretty 
import qualified Text.PrettyPrint.ANSI.Leijen as D

import Data.Char

data Name = NormalName String
          | Generated  Int
  deriving (Ord, Eq, Show) 

instance Pretty Name where
  ppr (NormalName n) = D.text n
  ppr (Generated  i) = D.text "_" D.<> D.int i 

type ModuleName = [String]

moduleNameToStr :: ModuleName -> String
moduleNameToStr ms = foldr1 (\a b -> a ++ "." ++ b) ms 

data QName = QName ModuleName Name -- qualified name (for global names)
           | BName Name            -- bare name
           deriving (Show, Eq, Ord) 

instance Pretty QName where
  ppr (QName m n) =
    (case n of
        Generated _ -> id 
        NormalName (c:_) | isLower c || isUpper c -> id
        _                            -> D.parens) $ 
    D.text (moduleNameToStr m) D.<> D.text "." D.<> ppr n
  ppr (BName n)   = ppr n 
  

baseModule :: ModuleName
baseModule = ["Base"]

conTrue :: QName
conTrue = QName baseModule (NormalName "True")

conFalse :: QName
conFalse = QName baseModule (NormalName "False")

nameTuple :: Int -> QName
nameTuple n = QName baseModule (NormalName $ replicate n ',')

nameUnit :: QName
nameUnit = nameTuple 0 

nameTyTuple :: Int -> QName
nameTyTuple = nameTuple

nameTyBang :: QName
nameTyBang = QName baseModule (NormalName "Bang")

nameTyRev :: QName
nameTyRev = QName baseModule (NormalName "Rev")

nameTyInt :: QName
nameTyInt = QName baseModule (NormalName "Int")

nameTyDouble :: QName
nameTyDouble = QName baseModule (NormalName "Double")

nameTyChar :: QName
nameTyChar = QName baseModule (NormalName "Char")

nameTyList :: QName
nameTyList = QName baseModule (NormalName "List")

nameTyArr :: QName
nameTyArr = QName baseModule (NormalName "->") 
