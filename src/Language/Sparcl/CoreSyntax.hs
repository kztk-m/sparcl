{-# OPTIONS_GHC -Wincomplete-patterns #-}

module Language.Sparcl.CoreSyntax where

import Data.Maybe (fromJust) 
import Control.Monad.Reader 
import Control.Monad.State 

import Language.Sparcl.SrcLoc 

data Name = NameUser String -- ^ User specified names
          | NameGen  Int    -- ^ Generated names
  deriving (Eq, Ord) 

type ModuleName = String

data QName = QName [ModuleName] Name -- qualified name 
           | LName Name              -- local name
  deriving (Eq, Ord)


data LType = TArr LType LType
           | TCon QName [LType]
           | TForall Name LType
           | TBang LType

pattern a :-* b = TArr a b

infixr 1 :-*

data Typed a = Typed { typeOf :: LType, untype :: a } 
 
type LocTerm a = Loc (Term a)
type TypedLocTerm a = Typed (Loc (Term a))

type TyEnv = [(QName, LType)]

type TyEnvU = TyEnv -- ^ unrestricted typing environment
type TyEnvL = TyEnv -- ^ linear typing environment
type TyEnvR = TyEnv -- ^ reversible typing environment

data Term a 
  = LVar a QName
  | UVar a QName
  | Abs  a (Typed QName) (TypedLocTerm a)
  | App  a (TypedLocTerm a) (TypedLocTerm a)
  | Bang a (TypedLocTerm a)
  | TAbs a QName (TypedLocTerm a)
  | TApp a (TypedLocTerm a) LType
  | Case a (TypedLocTerm a) [ Branch a ]
  | Con  a QName [LType] [TypedLocTerm a] 

  | RVar a QName
  | RCon a QName [LType] [TypedLocTerm a]
  | RCase a (TypedLocTerm a) [ RBranch a ]

  | Lift   a (TypedLocTerm a) (TypedLocTerm a)
  | UnLift a (TypedLocTerm a)

  | RPin a (TypedLocTerm a) (TypedLocTerm a) 

data Branch  a = Br  Pat (TypedLocTerm a)
data RBranch a = RBr Pat (TypedLocTerm a) (TypedLocTerm a) 

data Pat = PVar   (Typed QName)
         | PCon   QName [LType] [Typed QName]
         | PBang  (Typed QName)
         | PBCon  QName [LType] [Typed QName]
