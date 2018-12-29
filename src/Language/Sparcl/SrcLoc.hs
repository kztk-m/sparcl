module Language.Sparcl.SrcLoc where

import Language.Sparcl.Pretty 
import qualified Text.PrettyPrint.ANSI.Leijen as D

data SrcLoc = SrcLoc { filename :: Maybe FilePath, row :: Int, col :: Int } 
  deriving (Eq, Ord, Show) 

instance Pretty SrcLoc where
  ppr (SrcLoc m r c) =
    D.angles $ D.hcat [pprMaybeFilePath m,
                       D.colon,
                       D.parens $ D.hcat [ D.int r,
                                           D.comma,
                                           D.int c ] ]
    
pprMaybeFilePath :: Maybe FilePath -> D.Doc
pprMaybeFilePath Nothing  = D.text "*unknown source*"
pprMaybeFilePath (Just s) = D.text s


data SrcSpan = SrcSpan SrcLoc SrcLoc
             | NoLoc 
             deriving (Eq, Ord, Show) 

instance Pretty SrcSpan where
  ppr NoLoc = D.angles $ D.text "*unknown loc*"
  ppr (SrcSpan s1 s2) =
    D.angles $ D.hcat [pprMaybeFilePath $ filename s1,
                       D.colon,
                       D.parens $ D.hcat [ D.int (row s1),
                                           D.comma,
                                           D.int (col s1) ],
                       D.text "-", 
                       D.parens $ D.hcat [ D.int (row s2),
                                           D.comma,
                                           D.int (col s1) ]]
    


noLoc :: a -> Loc a
noLoc = Loc NoLoc

instance Semigroup SrcSpan where
  NoLoc <> e = e
  SrcSpan s1 e1 <> SrcSpan s2 e2 = SrcSpan (min s1 s2) (max e1 e2)
  s@(SrcSpan _s1 _e1) <> NoLoc = s 

instance Monoid SrcSpan where
  mempty = NoLoc 

  
data Loc a = Loc {location :: SrcSpan, unLoc :: a}
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable) 

