module Language.Sparcl.Literal where

import Language.Sparcl.Pretty

import Control.DeepSeq

data Literal
  = LitInt !Int
  | LitDouble !Double
  | LitChar !Char
  | LitRational !Rational
  deriving Show

instance NFData Literal where
  rnf s = seq s ()

instance Pretty Literal where
  ppr (LitInt i) = ppr i
  ppr (LitDouble d) = ppr d
  ppr (LitChar c) = ppr (show c)
  ppr (LitRational q) = ppr q
