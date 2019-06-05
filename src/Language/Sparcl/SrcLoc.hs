module Language.Sparcl.SrcLoc where

import           Language.Sparcl.Pretty as D

data SrcLoc = SrcLoc { slFilename :: Maybe FilePath, slRow :: Int, slCol :: Int }
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


data SrcSpan = SrcSpan (Maybe FilePath) Int Int Int Int
             | NoLoc
             deriving (Eq, Ord, Show)

instance Pretty SrcSpan where
  ppr NoLoc = D.angles $ D.text "<*unknown place*>"
  ppr (SrcSpan fp r1 c1 r2 c2) =
    D.hcat [pprMaybeFilePath fp,
             D.colon, pprPos ]
    where
      pprPos
        | r1 == r2 && c1 == c2 = D.hcat [ D.int r1, D.colon, D.int c1]
        | r1 == r2 && c1 /= c2 = D.hcat [ D.int r1, D.colon, D.int c1, D.text "-", D.int c2 ]
        | otherwise            = D.hcat [ D.parens (D.hcat [D.int r1, D.colon, D.int c1]),
                                          D.text "-",
                                          D.parens (D.hcat [D.int r2, D.colon, D.int c2])]



noLoc :: a -> Loc a
noLoc = Loc NoLoc

instance Semigroup SrcSpan where
  NoLoc <> e = e
  SrcSpan fp ls1 cs1 le1 ce1  <> SrcSpan _ ls2 cs2 le2 ce2 =
    let (ls, cs) = min (ls1, cs1) (ls2, cs2)
        (le, ce) = max (le1, ce1) (le2, ce2)
    in SrcSpan fp ls cs le ce
  s <> NoLoc = s

instance Monoid SrcSpan where
  mempty = NoLoc

data Loc a = Loc {location :: SrcSpan, unLoc :: a}
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

instance Applicative Loc where
  pure = Loc NoLoc
  Loc l1 a <*> Loc l2 b = Loc (l1 <> l2) (a b)

extend :: Loc a -> Loc b -> Loc b
extend (Loc s1 _) (Loc s2 x) = Loc (s1 <> s2) x
