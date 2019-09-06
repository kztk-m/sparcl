{-# LANGUAGE UndecidableInstances #-}

module Language.Sparcl.FreeTyVars (FreeTyVars(..)) where

import qualified Data.Set as S

newtype GatherVars x = GatherVars { runGatherVars :: S.Set x -> (S.Set x -> S.Set x) }

instance Semigroup (GatherVars x) where
  GatherVars f <> GatherVars g = GatherVars $ \b r -> f b (g b r)

instance Monoid (GatherVars x) where
  mempty = GatherVars $ \_ -> id

foundVar :: Ord x => x -> GatherVars x
foundVar x = GatherVars $ \b r ->
                            if S.member x b then r else S.insert x r

boundVar :: Ord x => x -> GatherVars x -> GatherVars x
boundVar x (GatherVars f) = GatherVars $ \b r -> f (S.insert x b) r


class Ord x => FreeTyVars t x | t -> x where
  freeTyVars :: t -> [x]
  freeTyVars t = S.toList $ runGatherVars (foldMapVars foundVar boundVar t) S.empty S.empty

  foldMapVars :: Monoid m => (x -> m) -> (x -> m -> m) -> t -> m

instance FreeTyVars a x => FreeTyVars [a] x where
  foldMapVars f uc ts = foldMap (foldMapVars f uc) ts

instance (FreeTyVars a x, FreeTyVars b x) => FreeTyVars (a, b) x where
  foldMapVars f uc (t1, t2) = foldMapVars f uc t1 <> foldMapVars f uc t2

