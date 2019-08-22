module Language.Sparcl.Multiplicity where

import           Language.Sparcl.Pretty

data Multiplicity = One | Omega
  deriving (Eq, Ord, Show)

instance Pretty Multiplicity where
  ppr One   = text "One"
  ppr Omega = text "Omega"


instance Bounded Multiplicity where
  minBound = One
  maxBound = Omega

class MultiplicityLike a where
  one   :: a
  omega :: a
  fromMultiplicity :: Multiplicity -> a

instance MultiplicityLike Multiplicity where
  {-# INLINE one #-}
  one = One
  {-# INLINE omega #-}
  omega = Omega
  {-# INLINE fromMultiplicity #-}
  fromMultiplicity = id

class Lub a where
  lub :: a -> a -> a

instance Lub Multiplicity where
  lub One t   = t
  lub Omega _ = Omega

