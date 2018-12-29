module Language.Sparcl.Pretty (
  Doc, Precedence, Pretty(..), prettyShow, prettyPut, parensIf 
  ) where

import qualified Text.PrettyPrint.ANSI.Leijen as D
import Text.PrettyPrint.ANSI.Leijen (Doc)

type Precedence = Int 

class Pretty t where
  pprPrec :: Precedence -> t -> Doc
  pprPrec _ = ppr

  ppr :: t -> Doc
  ppr = pprPrec 0 

  pprList :: Precedence -> [t] -> Doc
  pprList k ts =
    D.brackets $ D.align $ D.cat $ D.punctuate D.comma $ map (pprPrec k) ts 

instance Pretty t => Pretty [t] where
  pprPrec = pprList 

prettyShow :: Pretty t => t -> String
prettyShow x = show (ppr x)

prettyPut :: Pretty t => t -> IO ()
prettyPut x = D.putDoc (ppr x) 

parensIf :: Bool -> Doc -> Doc 
parensIf b d = if b then D.parens d else d 
