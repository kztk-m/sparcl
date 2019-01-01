module Language.Sparcl.Pretty (
  Doc, Precedence, Pretty(..), prettyShow,
  prettyPut, prettyPutLn,
  hPrettyPut, hPrettyPutLn, 
  parensIf, pprMap
  ) where

import qualified Text.PrettyPrint.ANSI.Leijen as D
import Text.PrettyPrint.ANSI.Leijen (Doc)
import System.IO (Handle)

import qualified Data.Map as M 

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

prettyPutLn :: Pretty t => t -> IO ()
prettyPutLn x = D.putDoc (ppr x <> D.line) 

hPrettyPut :: Pretty t => Handle -> t -> IO ()
hPrettyPut h x = D.hPutDoc h (ppr x) 

hPrettyPutLn :: Pretty t => Handle -> t -> IO ()
hPrettyPutLn h x = D.hPutDoc h (ppr x <> D.line) 

parensIf :: Bool -> Doc -> Doc 
parensIf b d = if b then D.parens d else d 

pprMap :: (Pretty k , Pretty v) => M.Map k v -> Doc
pprMap m = D.align $ 
  D.vsep [ ppr k D.<+> D.text "|->" D.<+> D.align (ppr v)
         | (k, v) <- M.toList m ]
