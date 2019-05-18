module Language.Sparcl.Literal where

import Language.Sparcl.Pretty 
import qualified Text.PrettyPrint.ANSI.Leijen as D

import Control.DeepSeq 

data Literal
  = LitInt      Int
  | LitDouble   Double
  | LitChar     Char
  | LitRational Rational 
  deriving Show

instance NFData Literal where
  rnf (LitInt i) = rnf i
  rnf (LitDouble d) = rnf d
  rnf (LitChar c) = rnf c
  rnf (LitRational q) = rnf q 

instance Pretty Literal where
  ppr (LitInt i)      = D.int i
  ppr (LitDouble d)   = D.double d
  ppr (LitChar c)     = D.text (show c) 
  ppr (LitRational q) = D.rational q 
