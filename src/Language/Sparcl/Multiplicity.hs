module Language.Sparcl.Multiplicity where

import Language.Sparcl.Pretty 

data Multiplicity = One | Omega
  deriving (Eq, Ord, Show) 

instance Pretty Multiplicity where
  ppr One   = text "One"
  ppr Omega = text "Omega" 
