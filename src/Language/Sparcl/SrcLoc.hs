module Language.Sparcl.SrcLoc where

type SrcSpan = Maybe (SrcLoc, SrcLoc)

data SrcLoc = SrcLoc { filename :: Maybe FilePath, row :: Int, col :: Int } 
  deriving (Eq, Ord, Show) 
  
data Loc a = Loc SrcSpan a  
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable) 
