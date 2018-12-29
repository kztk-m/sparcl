module Language.Sparcl.Literal where

import Language.Sparcl.Pretty 
import qualified Text.PrettyPrint.ANSI.Leijen as D

data Literal
  = LitInt    Int
  | LitDouble Double
  | LitChar   Char 
  deriving Show

instance Pretty Literal where
  ppr (LitInt i)    = D.int i
  ppr (LitDouble d) = D.double d
  ppr (LitChar c)   = D.text (show c) 
