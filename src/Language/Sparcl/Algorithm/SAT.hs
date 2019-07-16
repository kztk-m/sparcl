{-# LANGUAGE OverloadedStrings #-}

{-
A simple DPLL-based SAT solver.
-}

module Language.Sparcl.Algorithm.SAT (
  Formula, var, neg, (.&&.), (.||.), (.=>.), (.<=>.), elim,
  true, false, sat, allsat
  ) where

import qualified Data.Map               as M
import qualified Data.IntMap.Strict            as IM 

import           Control.Monad.Writer
import           Control.Monad.State 
import           Language.Sparcl.Pretty hiding ((<$>))

import           Data.Maybe             (mapMaybe, fromJust)

data Formula v
  = FVar v
  | FAnd (Formula v) (Formula v)
  | FOr  (Formula v) (Formula v) 
  | FNot (Formula v)
  | FIff (Formula v) (Formula v) 
  | FTrue
  | FFalse
  deriving (Functor, Foldable, Traversable) 

(.&&.) :: Formula v -> Formula v -> Formula v
FFalse .&&. _  = FFalse
FTrue  .&&. t2 = t2
_  .&&. FFalse = FFalse
t1 .&&. FTrue  = t1
(FAnd t1 t2) .&&. t3 = t1 .&&. (t2 .&&. t3) 
t1 .&&. t2 = FAnd t1 t2 


(.||.) :: Formula v -> Formula v -> Formula v
FTrue  .||. _  = FTrue
FFalse .||. t2 = t2
_  .||. FTrue  = FTrue
t1 .||. FFalse = t1
t1 .||. t2  = FOr t1 t2 

neg :: Formula v -> Formula v
neg FFalse   = FTrue
neg FTrue    = FFalse
neg (FNot t) = t 
neg t = FNot t 

var :: v -> Formula v
var = FVar

elim :: Eq v => v -> Bool -> Formula v -> Formula v
elim v b = go
  where
    go (FVar x)
      | v == x    = if b then FTrue else FFalse
      | otherwise   = var x
    go (FAnd t1 t2) = go t1 .&&. go t2
    go (FOr  t1 t2) = go t1 .||. go t2
    go (FNot t)     = neg (go t)
    go FTrue        = FTrue
    go FFalse       = FFalse
    go (FIff t1 t2) = go t1 .<=>. go t2 

instance Pretty v => Pretty (Formula v) where
  pprPrec _ (FVar x) = ppr x
  pprPrec _ FTrue    = "true"
  pprPrec _ FFalse   = "false"
  pprPrec k (FAnd t1 t2) =
    let ts = t1:andChain t2
    in group $ parensIf (k > 3) $ align $ hcat $ punctuate (line <> "&" <> " ") $ map (pprPrec 4) ts
    where
      andChain (FAnd s1 s2) = s1:andChain s2
      andChain s            = [s]
  pprPrec k (FOr t1 t2) =
    let ts = t1:orChain t2
    in group $ parensIf (k > 2) $ align $ hcat $ punctuate (line <> "|" <> " ") $ map (pprPrec 3) ts
    where
      orChain (FOr s1 s2) = s1:orChain s2
      orChain s           = [s]
  pprPrec k (FIff t1 t2) = parensIf (k > 1) $
    pprPrec 2 t1 <+> "=" <+> pprPrec 2 t2 
  pprPrec k (FNot t1) = parensIf (k > 9) $
    "~" <> pprPrec 10 t1


data Clause = Clause !Int -- cached size 
                     (IM.IntMap Bool) 

lookupC :: IM.Key -> Clause -> Maybe Bool
lookupC x (Clause _ m) = IM.lookup x m

deleteC :: IM.Key -> Clause -> Clause
deleteC x (Clause s m) = (Clause (s-1) (IM.delete x m))

lookupMinC :: Clause -> Maybe (IM.Key, Bool)
lookupMinC (Clause _ m) = IM.lookupMin m 

{-# INLINE sizeC #-}
sizeC :: Clause -> Int
sizeC (Clause i _) = i 

{-# INLINE nullC #-}
nullC :: Clause -> Bool 
nullC (Clause i _) = i == 0

toListC :: Clause -> [(Int, Bool)]
toListC (Clause _ m) = IM.toList m 

(.=>.) :: Formula v -> Formula v -> Formula v
(.=>.) a b = neg a .||. b

(.<=>.) :: Formula v -> Formula v -> Formula v
FTrue  .<=>. b = b
FFalse .<=>. b = neg b
a .<=>. FTrue  = a
a .<=>. FFalse = neg a 
a .<=>. b = FIff a b -- (neg a .||. b) .&&. (neg b .||. a)

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


data Join a = Empty | NonEmpty (JoinNonEmpty a)
  deriving (Functor, Foldable, Traversable) 

data JoinNonEmpty a = Single a | Join (JoinNonEmpty a) (JoinNonEmpty a) 
  deriving (Functor, Foldable, Traversable) 

data MyQueue a = MyQueue !(Join a) -- elements of size 1 
                         !(Join a) -- other elements 
  deriving (Functor, Foldable, Traversable) 

instance Semigroup (Join a) where
  Empty <> t = t
  NonEmpty t <> Empty = NonEmpty t
  NonEmpty t1 <> NonEmpty t2 = NonEmpty (Join t1 t2) 

instance Monoid (Join a) where
  mempty = Empty

{-# INLINE singletonQ #-}
singletonQ :: (a -> Key) -> a -> MyQueue a 
singletonQ k n
  | k n == 1  = MyQueue (NonEmpty $ Single n) Empty 
  | otherwise = MyQueue Empty (NonEmpty $ Single n)

{-# INLINE emptyQ #-}
emptyQ :: MyQueue a
emptyQ = MyQueue Empty Empty 

{-# INLINE mergeQs #-}
mergeQs :: [MyQueue a] -> MyQueue a
mergeQs = foldr mergeQ emptyQ 

{-# INLINE mergeQ #-}
mergeQ :: MyQueue a -> MyQueue a -> MyQueue a
mergeQ (MyQueue xs ys) (MyQueue xs' ys') = MyQueue (xs <> xs') (ys <> ys')

pickOneJ :: Join a -> Maybe (a, Join a)
pickOneJ Empty = Nothing
pickOneJ (NonEmpty t) = go t Empty
  where
    go (Single a)   r = Just (a, r) 
    go (Join t1 t2) r = go t1 (NonEmpty t2 <> r) 

pickOne1 :: MyQueue a -> Maybe (a, MyQueue a)
pickOne1 (MyQueue xs ys) =
  case pickOneJ xs of
    Just (a, xs') -> Just (a, MyQueue xs' ys)
    Nothing       -> Nothing

pickOne :: MyQueue a -> Maybe (a, MyQueue a)
pickOne (MyQueue xs ys) =
  case pickOneJ xs of
    Just (a, xs') -> Just (a, MyQueue xs' ys)
    Nothing       -> do 
      (a, ys') <-  pickOneJ ys
      return (a, MyQueue xs ys')
        

{-# INLINE fromClauses #-}
fromClauses :: [Clause] -> MyQueue Clause
fromClauses = mergeQs . map (singletonQ sizeC)


type CNFimpl = MyQueue Clause

toImpl :: forall v. Ord v => Formula v -> (CNFimpl, M.Map Int v)
toImpl formula = -- fromClauses $ pCNF p
  let cs = evalState (convert formula) cnt
  in (fromClauses cs, i2v) 
  where
    -- Tseitin transformation
    -- [[y]]x       => (~x | y) & (x | ~y) 
    -- [[A & B]]x   => (~x | y) & (~x | z) & (~y | ~z | x) & [[A]]y & [[B]]z
    -- [[A | B]]x   => (~x | y | z) & (~y | x) & (~z | x) & [[A]]y & [[B]]z
    -- [[not A]]x   => (~x | ~y) & (x | y) & [[A]]y
    -- [[A <=> B]]x => (~x | ~y | z) & (~x | ~z | y) & (y | z | x) & (~y | ~z | x) & [[A]]y & [[B]]z
    -- [[A => B]]x  => (~x | ~y | z) & (x | y) & (x | ~z) & [[A]]y & [[B]]z 
    -- [[true]]x    => x
    -- [[false]]x   => ~x
    convert :: Formula v -> State Int [Clause]
    convert p = do n <- newVar p 
                   ($ []) <$> execWriterT (tell (wrap $ IM.singleton n True) >> go n p) 
      where
        newVar :: MonadState Int m => Formula v -> m Int 
        newVar (FVar x) = return (fromJust $ M.lookup x v2i)
        newVar _        = next
        wrap x = (Clause (IM.size x) x:)
        go :: Int -> Formula v -> WriterT ([Clause] -> [Clause]) (State Int)  () 
        go x (FVar v) =
          let Just y = M.lookup v v2i
          in if x == y then
               tell mempty
             else do 
               tell $ wrap $ IM.fromList [(x,False), (y, True)]
               tell $ wrap $ IM.fromList [(x,True), (y,False)]
        go x (FAnd t1 t2) = do 
          y <- newVar t1
          z <- newVar t2
          tell $ wrap $ IM.fromList [ (x, False), (y, True) ]
          tell $ wrap $ IM.fromList [ (x, False), (z, True) ]
          tell $ wrap $ IM.fromList [ (x, True), (y, False), (z, False) ]
          go y t1
          go z t2
        go x (FIff t1 t2) = do
          y <- newVar t1
          z <- newVar t2
          tell $ wrap $ IM.fromList [ (x, False), (y, False), (z, True) ]
          tell $ wrap $ IM.fromList [ (x, False), (y, True),  (z, False) ]
          tell $ wrap $ IM.fromList [ (x, True),  (y, True),  (z, True) ]
          tell $ wrap $ IM.fromList [ (x, True),  (y, False), (z, False) ] 
          go y t1
          go z t2


        go x (FOr (FNot t1) t2) = do -- t1 => t2
          y <- newVar t1
          z <- newVar t2
          tell $ wrap $ IM.fromList [ (x, False), (y, False), (z, True) ]
          tell $ wrap $ IM.fromList [ (x, True),  (y, True) ]
          tell $ wrap $ IM.fromList [ (x, True),  (z, False) ]
          go y t1
          go z t2          
          
        go x (FOr t1 t2) = do
          y <- newVar t1
          z <- newVar t2 
          tell $ wrap $ IM.fromList [ (x, False), (y, True), (z, True) ]
          tell $ wrap $ IM.fromList [ (x, True), (y, False) ]
          tell $ wrap $ IM.fromList [ (x, True), (z, False) ]
          go y t1
          go z t2 
          
        go x (FNot t) = do 
          y <- newVar t
          tell $ wrap $ IM.fromList [ (x, False), (y, False) ]
          tell $ wrap $ IM.fromList [ (x, True) , (y, True)  ]
          go y t 
        go x FTrue  = tell $ wrap $ IM.singleton x True 
        go x FFalse = tell $ wrap $ IM.singleton x False 
          
                            
    
    i2v = M.fromList $ map (\(x,n) -> (n,x)) $ M.toList v2i
    (v2i, cnt) =
      flip runState 0 $ 
      traverse (const next) $   
      foldr (\x -> M.insert x (1 :: Int)) M.empty formula

    next :: MonadState Int m => m Int 
    next = do
      i <- get
      put (i + 1)
      return i 

type Solver m = WriterT [(Int,Bool)] m

assign :: forall m. Monad m => Int -> Bool -> CNFimpl -> Solver m CNFimpl
assign v b cs = do
  tell [(v, b)]
--  return $ fromClauses $ mapMaybe tryAssign $ toListQ cs
  return $ foldr (\c r ->
                     case tryAssign c of
                       Nothing -> r
                       Just c' -> singletonQ sizeC c' `mergeQ` r) emptyQ cs 
  where
    {-# INLINABLE tryAssign #-}
    tryAssign :: Clause -> Maybe Clause
    tryAssign m =
      case lookupC v m of
        Just b' ->
          if b == b' then -- the assignment make the literal true
            Nothing -- the whole clause becomes true
          else
            Just $ deleteC v m
        Nothing ->
          Just m -- the assignment does not affect the clause

unitProp :: MonadPlus m => CNFimpl -> Solver m CNFimpl
unitProp q = case pickOne1 q of
  Nothing     -> return q
  Just (x,q') -> do 
    let [(v,b)] = toListC x
    q'' <- assign v b q'
    unitProp q''

-- data Pure = Pure !Bool
--           | Impure

-- findPureLits :: Ord v => CNFimpl v -> ([v], [v], [v])
-- findPureLits cs =
--   let res = foldr (flip (M.foldrWithKey (\x v -> ins x (Pure v)))) M.empty cs
--       ps  = M.keys $ M.filter (\case Pure v -> v
--                                      Impure -> False) res
--       ns  = M.keys $ M.filter (\case Pure v -> not v
--                                      Impure -> False) res
--       vs  = M.keys $ M.filter (\case Pure _ -> False
--                                      Impure -> True) res
--   in (ps, ns, vs)
--   where
--     ins = M.insertWith f
--       where
--         f (Pure a) (Pure b) | a == b = Pure a
--         f _        _                 = Impure


pickOneVariable :: CNFimpl -> Maybe Int
pickOneVariable q = do
  (c, _) <- pickOne q
  fst <$> lookupMinC c
                      
-- pickOneVariable EmptyQ        = Nothing
-- pickOneVariable (NodeQ _ m _) = fst <$> IM.lookupMin m


-- dpll :: (MonadPlus m, Ord v) => CNFimpl v -> Solver v m ()
-- dpll cs | null cs     = return ()
--         | any null cs = mzero
--         | otherwise  = do
--             cs'  <- unitProp cs
--             let (ps, ns, vs) = findPureLits cs'
--             cs'' <- assignAll ps True =<< assignAll ns False cs'
--             case vs of
--               []  -> dpll cs''
--               v:_ -> (dpll =<< assign v True  cs'') `mplus`
--                      (dpll =<< assign v False cs'')


dpll :: MonadPlus m => CNFimpl -> Solver m ()
dpll cs | null cs      = return ()
        | any nullC cs = mzero
        | otherwise  = do
            cs'  <- unitProp cs
            case pickOneVariable cs' of
              Nothing -> dpll cs'
              Just v  -> (dpll =<< assign v True  cs') `mplus`
                         (dpll =<< assign v False cs')

satI :: CNFimpl -> Maybe [(Int, Bool)]
satI cs =
  case execWriterT (dpll cs) of
    []   -> Nothing
    vs:_ -> Just vs

sat :: Ord v => Formula v -> Maybe [(v, Bool)]
sat p = do 
  let (cs, i2v) = toImpl p 
  res <- satI cs
  return $ mapMaybe (\(n,t) -> do
                        x <- M.lookup n i2v
                        return (x, t)) res

allsat :: Ord v => Formula v -> [[(v,Bool)]]
allsat cs = -- trace (show $ "<" <> ppr cs <> ">") $ 
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


