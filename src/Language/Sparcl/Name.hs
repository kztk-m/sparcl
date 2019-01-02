module Language.Sparcl.Name where

import Language.Sparcl.Pretty 
import qualified Text.PrettyPrint.ANSI.Leijen as D

import Control.DeepSeq 

import Data.Char

data Name = NormalName String
          | NameTuple Int 
          | Generated  Int
          | Alpha      Name Int 
  deriving (Ord, Eq, Show) 

instance NFData Name where
  rnf (NormalName s) = rnf s
  rnf (NameTuple i)  = rnf i
  rnf (Generated i)  = rnf i
  rnf (Alpha n i)    = rnf (n, i) 

instance Pretty Name where
  ppr (NameTuple 0)  = D.text "()"
  ppr (NameTuple n)  = D.text (replicate (n-1) ',') 
  ppr (NormalName n) = D.text n
  ppr (Generated  i) = D.text "_" D.<> D.int i 
  ppr (Alpha n    i) = ppr n D.<> D.text "_" D.<> D.int i 

originalName :: Name -> Name
originalName (Alpha n _) = n
originalName n           = n

originalQName :: QName -> QName
originalQName (BName n) = BName (originalName n)
originalQName (QName cm n) = QName cm (originalName n) 

type ModuleName = [String]

moduleNameToStr :: ModuleName -> String
moduleNameToStr ms = foldr1 (\a b -> a ++ "." ++ b) ms 

data QName = QName ModuleName Name -- qualified name (for global names)
           | BName Name            -- bare name
           deriving (Show, Eq, Ord) 

instance NFData QName where
  rnf (QName m n) = rnf (m, n)
  rnf (BName n)   = rnf n 

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
nameTuple n = QName baseModule (NameTuple n) 

checkNameTuple :: QName -> Maybe Int
checkNameTuple (QName _ (NameTuple m)) = Just m
checkNameTuple (BName   (NameTuple m)) = Just m
checkNameTuple _                       = Nothing 

nameUnit :: QName
nameUnit = nameTuple 0 

nameTyTuple :: Int -> QName
nameTyTuple = nameTuple

nameTyBang :: QName
nameTyBang = QName baseModule (NormalName "bang")

nameTyRev :: QName
nameTyRev = QName baseModule (NormalName "rev")

nameTyInt :: QName
nameTyInt = QName baseModule (NormalName "Int")

nameTyDouble :: QName
nameTyDouble = QName baseModule (NormalName "Double")

nameTyChar :: QName
nameTyChar = QName baseModule (NormalName "Char")

nameTyBool :: QName
nameTyBool = QName baseModule (NormalName "Bool") 

nameTyList :: QName
nameTyList = QName baseModule (NormalName "List")

nameTyLArr :: QName
nameTyLArr = QName baseModule (NormalName "-o") 
