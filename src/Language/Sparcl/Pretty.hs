module Language.Sparcl.Pretty (
  Precedence, Pretty(..), prettyShow,
  prettyPut, prettyPutLn,
  hPrettyPut, hPrettyPutLn,
  parensIf, pprMap,
  module Text.PrettyPrint.ANSI.Leijen
  ) where

import           Text.PrettyPrint.ANSI.Leijen hiding (Pretty (..))
-- import Text.PrettyPrint.ANSI.Leijen (Doc)
import           System.IO                    (Handle)

import qualified Data.Map                     as M

type Precedence = Int

class Pretty t where
  pprPrec :: Precedence -> t -> Doc
  pprPrec _ = ppr

  ppr :: t -> Doc
  ppr = pprPrec 0

  pprList :: Precedence -> [t] -> Doc
  pprList k ts =
    brackets $ align $ cat $ punctuate comma $ map (pprPrec k) ts

instance Pretty t => Pretty [t] where
  pprPrec = pprList

instance Pretty Bool where
  ppr = bool

instance Pretty Int where
  ppr = int

instance Pretty Double where
  ppr = double

instance Pretty Char where
  ppr = text . show
  pprList _ = text . show

instance (Pretty a, Pretty b) => Pretty (a, b) where
  ppr (a, b) = parens $ align (ppr a) <> comma <+> align (ppr b)

prettyShow :: Pretty t => t -> String
prettyShow x = show (ppr x)

prettyPut :: Pretty t => t -> IO ()
prettyPut x = putDoc (ppr x)

prettyPutLn :: Pretty t => t -> IO ()
prettyPutLn x = putDoc (ppr x <> line)

hPrettyPut :: Pretty t => Handle -> t -> IO ()
hPrettyPut h x = hPutDoc h (ppr x)

hPrettyPutLn :: Pretty t => Handle -> t -> IO ()
hPrettyPutLn h x = hPutDoc h (ppr x <> line)

parensIf :: Bool -> Doc -> Doc
parensIf b d = if b then parens d else d

pprMap :: (Pretty k , Pretty v) => M.Map k v -> Doc
pprMap m = align $
  vsep [ ppr k <+> text "|->" <+> align (ppr v)
       | (k, v) <- M.toList m ]
