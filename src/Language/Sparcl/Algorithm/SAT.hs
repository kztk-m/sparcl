{-
A simple DPLL-based SAT solver. 
-}

module Language.Sparcl.Algorithm.SAT (
  Formula, var, neg, (.&&.), (.||.), (.=>.), (.<=>.), elim, 
  true, false, sat, allsat
  ) where

import qualified Data.Map as M 
import qualified Data.Map.Merge.Lazy as M 

import Control.Monad.Writer
import Language.Sparcl.Pretty hiding ((<$>))

import Data.Maybe (mapMaybe, catMaybes)

data Formula v
  = FVar v
  | FAnd (Formula v) (Formula v)
  | FNot (Formula v)
  | FTrue
  | FFalse 

(.&&.) :: Formula v -> Formula v -> Formula v
(.&&.) = FAnd

(.||.) :: Formula v -> Formula v -> Formula v
(.||.) t1 t2  = FNot (FAnd (FNot t1) (FNot t2))

neg :: Formula v -> Formula v
neg = FNot

var :: v -> Formula v 
var = FVar

elim :: Eq v => v -> Bool -> Formula v -> Formula v
elim v b = go
  where
    go (FVar x) 
      | v == x    = if b then FTrue else FFalse
      | otherwise = FVar x
    go (FAnd t1 t2) = FAnd (go t1) (go t2)
    go (FNot t)     = FNot (go t)
    go FTrue        = FTrue
    go FFalse       = FFalse

makeCNF :: Ord v => Formula v -> (CNF v, DNF v)
makeCNF (FVar v) = ([M.singleton v True], [M.singleton v False])
makeCNF (FAnd t1 t2) =
  let r1 = makeCNF t1
      r2 = makeCNF t2
  in (fst r1 ++ fst r2,
      catMaybes [ c1 `appC` c2 | c1 <- snd r1, c2 <- snd r2 ])
makeCNF (FNot t) = swap (makeCNF t)
  where
    swap (a, b) = (b, a) 
makeCNF FTrue  = ([], [M.empty])
makeCNF FFalse = ([M.empty], [])

pCNF :: Ord v => Formula v -> CNF v                   
pCNF = fst . makeCNF


-- data Formula v = Formula { pCNF :: CNF v,
--                            nDNF :: DNF v } 
type DNF v = [Clause v]
type CNF v = [Clause v]

instance (Pretty v, Ord v) => Pretty (Formula v) where
  ppr = withSep (text "&") . map pprC . pCNF
    where
      withSep _ []  = empty
      withSep _ [x] = x
      withSep d (x:xs) = x <+> d <+> withSep d xs 
      pprC = parens . withSep (text "|") . map pprL . M.toList
      pprL (x, True)  = ppr x
      pprL (x, False) = text "-" <> ppr x 

type Clause v = M.Map v Bool 

appC :: Ord v => Clause v -> Clause v -> Maybe (Clause v)
appC =
  M.mergeA (M.traverseMissing $ \_ x -> pure x)
           (M.traverseMissing $ \_ x -> pure x)
           (M.zipWithAMatched $ \_ x y -> if x == y then pure x else Nothing) 

(.=>.) :: Ord v => Formula v -> Formula v -> Formula v
(.=>.) a b = neg a .||. b

(.<=>.) :: Ord v => Formula v -> Formula v -> Formula v
(.<=>.) a b = (neg a .||. b) .&&. (neg b .||. a) 

true :: Formula v
true = FTrue

false :: Formula v
false = FFalse

infixr 2 .||.
infixr 3 .&&.
infixr 1 .=>.
infixr 1 .<=>.
  
-----------

type Key = Int 

-- Paring Heap -- from Chris Okasaki's book
  -- We also referred the following URL
  -- https://www-ps.informatik.uni-kiel.de/~sebf/projects/sat-solver/Control/Monad/Constraint/Boolean.lhs.html
data PQueue a = EmptyQ
              | NodeQ  Key a [PQueue a]

mergeQ :: PQueue a -> PQueue a -> PQueue a
mergeQ EmptyQ h = h
mergeQ h EmptyQ = h
mergeQ h1@(NodeQ k1 n1 ts1) h2@(NodeQ k2 n2 ts2) =
  if k1 <= k2 then NodeQ k1 n1 (h2:ts1)
  else             NodeQ k2 n2 (h1:ts2)

mergeQs :: [PQueue a] -> PQueue a     
mergeQs []  = EmptyQ
mergeQs [h]        = h
mergeQs (h1:h2:hs) = mergeQ (mergeQ h1 h2) (mergeQs hs)

singletonQ :: (a -> Key) -> a -> PQueue a
singletonQ k n = NodeQ (k n) n []

toListQ :: PQueue a -> [a]
toListQ h = go h [] 
  where
    go EmptyQ r         = r
    go (NodeQ _ x hs) r = foldr go (x:r) hs 

fromClauses :: [Clause v] -> PQueue (Clause v)
fromClauses = mergeQs . map (singletonQ M.size) 

instance Foldable PQueue where
  foldMap f = foldMap f . toListQ 
  
type CNFimpl v = PQueue (Clause v) 

toImpl :: Ord v => Formula v -> CNFimpl v
toImpl p = fromClauses $ pCNF p 

type Solver v m = WriterT [(v,Bool)] m 

assign :: (Monad m, Ord v) => v -> Bool -> CNFimpl v -> Solver v m (CNFimpl v) 
assign v b cs = do
  tell [(v, b)]
  return $ fromClauses $ mapMaybe tryAssign $ toListQ cs 
  where
    tryAssign m =
      case M.lookup v m of
        Just b' ->
          if b == b' then -- the assignment make the literal true
            Nothing -- the whole clause becomes true 
          else
            Just $ M.delete v m 
        Nothing ->
          Just m -- the assignment does not affect the clause

-- assignNM :: Ord v => v -> Bool -> CNFimpl v -> CNFimpl v
-- assignNM v b cs = fst $ runWriter (assign v b cs)

assignAll :: (MonadPlus m, Ord v) => [v] -> Bool -> CNFimpl v -> Solver v m (CNFimpl v)
assignAll []     _ m = return m
assignAll (x:xs) b m = do
  m' <- assign x b m
  assignAll xs b m' 
  

unitProp :: (MonadPlus m, Ord v) => CNFimpl v -> Solver v m (CNFimpl v)
unitProp EmptyQ = return EmptyQ
unitProp h@(NodeQ k x hs) 
  | k == 1 = do 
      let [(v,b)] = M.toList x
      hs' <- assign v b (mergeQs hs)
      unitProp hs'
  | otherwise = return h 
      
data Pure = Pure Bool
          | Impure          
  
findPureLits :: Ord v => CNFimpl v -> ([v], [v], [v])
findPureLits cs = 
  let res = foldr (flip (M.foldrWithKey (\x v -> ins x (Pure v)))) M.empty cs
      ps  = M.keys $ M.filter (\case Pure v -> v
                                     Impure -> False) res
      ns  = M.keys $ M.filter (\case Pure v -> not v
                                     Impure -> False) res
      vs  = M.keys $ M.filter (\case Pure _ -> False
                                     Impure -> True) res
  in (ps, ns, vs) 
  where
    ins = M.insertWith f
      where
        f (Pure a) (Pure b) | a == b = Pure a
        f _        _                 = Impure 
  

dpll :: (MonadPlus m, Ord v) => CNFimpl v -> Solver v m () 
dpll cs | null cs     = return ()
        | any null cs = mzero
        | otherwise  = do 
            cs'  <- unitProp cs 
            let (ps, ns, vs) = findPureLits cs'
            cs'' <- assignAll ps True =<< assignAll ns False cs' 
            case vs of
              []  -> dpll cs'' 
              v:_ -> (dpll =<< assign v True  cs'') `mplus`
                     (dpll =<< assign v False cs'')

satI :: Ord v => CNFimpl v -> Maybe [(v, Bool)]
satI cs =
  case execWriterT (dpll cs) of
    [] -> Nothing
    vs:_ -> Just vs 

sat :: Ord v => Formula v -> Maybe [(v, Bool)]
sat = satI . toImpl 

allsat :: Show v => Ord v => Formula v -> [[(v,Bool)]]
allsat cs =
  case sat cs of
    Nothing -> []
    Just vs ->
      vs : allsat (cs .&&. neg (foldr (\(a,b) r -> (if b then var a else neg (var a)) .&&. r) true vs))
  


-- t1 :: Formula Int
-- t1 = (var 1 .<=>. var 2 .||. var 3) .&&.
--      neg (var 1 .<=>. var 2 .||. var 3)
     
-- t2 :: Formula Int
-- t2 = (var 1 .<=>. var 1 .&&. neg (var 2))
--      .&&.
--      (var 2 .<=>. var 1)
              
              
  
-- t3 :: Formula Int
-- t3 = -- (var 1 .<=>. var 1 .&&. neg (var 2))
--      -- .&&.
--      (var 1 .<=>. neg (var 2))
--      .&&.
--      (var 2 .<=>. var 1)

-- t4 :: Formula Int
-- t4 = (sam 1 .<=>. sam 1 .&&. nin 2) 
--      .&&.
--      (sam 2 .<=>. sam 2 .&&. nin 1)
--      .&&.
--      (sam 1 .<=>. var 10)
--      .&&.
--      (sam 2 .<=>. neg (var 10))
--      where       
--        sam n = (var 10 .&&. var n) .||. (neg (var 10) .&&. neg (var n))
--        nin n = (var 10 .&&. neg (var n)) .||. (neg (var 10) .&&. var n)
--      -- .&&.
--      -- ((var 10 .&&. var 1) .<=>. var 10)
--      -- .&&.
--      -- ((var 10 .&&. var 2) .<=>. neg (var 10))
     
                                
