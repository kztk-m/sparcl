module Language.Sparcl.SrcLoc where

import Data.Semigroup 

data SrcSpan = SrcSpan SrcLoc SrcLoc
             | NoLoc 
             deriving (Eq, Ord, Show) 

noLoc :: a -> Loc a
noLoc = Loc NoLoc

instance Semigroup SrcSpan where
  NoLoc <> e = e
  SrcSpan s1 e1 <> SrcSpan s2 e2 = SrcSpan (min s1 s2) (max e1 e2)
  s@(SrcSpan s1 e1) <> NoLoc = s 

instance Monoid SrcSpan where
  mempty = NoLoc 

data SrcLoc = SrcLoc { filename :: Maybe FilePath, row :: Int, col :: Int } 
  deriving (Eq, Ord, Show) 
  
data Loc a = Loc {location :: SrcSpan, unLoc :: a}
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable) 
