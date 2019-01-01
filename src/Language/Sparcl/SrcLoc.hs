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
                       D.colon, pprPos (row s1) (col s1) (row s2) (col s2) ]
    where
      pprPos l1 c1 l2 c2
        | l1 == l2 && c1 == c2 = D.hcat [ D.int l1, D.colon, D.int c1]
        | l1 == l2 && c1 /= c2 = D.hcat [ D.int l1, D.colon, D.int c1, D.text "-", D.int c2 ]
        | otherwise            = D.hcat [ D.parens (D.hcat [D.int l1, D.colon, D.int c1]),
                                          D.text "-",
                                          D.parens (D.hcat [D.int l2, D.colon, D.int c2])] 



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


instance Applicative Loc where
  pure a = Loc NoLoc a
  Loc l1 a <*> Loc l2 b = Loc (l1 <> l2) (a b) 
