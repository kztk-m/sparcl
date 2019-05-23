{-
A simple DPLL-based SAT solver. 
-}

module Language.Sparcl.Algorithm.SAT (
  Formula, var, neg, (.&&.), (.||.), (.=>.), (.<=>.),
  true, false, sat, allsat
  ) where

import qualified Data.Map as M 
import qualified Data.Map.Merge.Lazy as M 

import Control.Monad.Writer

data Formula v = Formula { pCNF :: CNF v,
                           nDNF :: DNF v } 
type DNF v = [Clause v]
type CNF v = [Clause v]

type Clause v = M.Map v Bool 

data Var v = Var Bool v 
  deriving Show 

appC :: Ord v => Clause v -> Clause v -> Maybe (Clause v)
appC cs1 cs2 =
  M.mergeA (M.traverseMissing $ \_ x -> pure x)
           (M.traverseMissing $ \_ x -> pure x)
           (M.zipWithAMatched $ \_ x y -> if x == y then pure x else Nothing) cs1 cs2  

var :: v -> Formula v 
var v = Formula [M.singleton v True] [M.singleton v False]

neg :: Formula v -> Formula v
neg a = Formula (nDNF a) (pCNF a) 

(.&&.) :: Ord v => Formula v -> Formula v -> Formula v
(.&&.) a b = Formula (pCNF a ++ pCNF b)
                     [ c | Just c <- [ c1 `appC` c2 | c1 <- nDNF a, c2 <- nDNF b ] ]

(.||.) :: Ord v => Formula v -> Formula v -> Formula v
(.||.) a b = neg (neg a .&&. neg b)

(.=>.) :: Ord v => Formula v -> Formula v -> Formula v
(.=>.) a b = neg a .||. b

(.<=>.) :: Ord v => Formula v -> Formula v -> Formula v
(.<=>.) a b = (neg a .||. b) .&&. (neg b .||. a) 

true :: Formula v
true = Formula [] [M.empty]

false :: Formula v
false = Formula [M.empty] []

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

assign :: (Ord v, MonadPlus m) => v -> Bool -> CNFimpl v -> Solver v m (CNFimpl v) 
assign v b cs = do
  tell [(v, b)]
  return $ fromClauses [ x | Just x <- map tryAssign $ toListQ cs ]
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
  let res = foldr (\m r -> M.foldrWithKey (\x v -> ins x (Pure v)) r m) M.empty cs
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

sat :: Ord v => Formula v -> Maybe [(v, Bool)]
sat cs =
  case execWriterT (dpll $ toImpl cs) of
    []   -> Nothing
    vs:_ -> Just vs 

allsat :: Show v => Ord v => Formula v -> [[(v,Bool)]]
-- allsat cs | trace (show $ pCNF cs) False = undefined 
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
     
                                
