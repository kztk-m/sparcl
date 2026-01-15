module Language.Sparcl.Pretty (
  Doc, 
  Precedence, Pretty(..), prettyShow,
  prettyPut, prettyPutLn,
  hPrettyPut, hPrettyPutLn,
  parensIf, pprMap,
  module Prettyprinter,

  -- * Utility 
  hPutDocWith, 

  -- * from Prettyprinter.Render.Terminal
  P.renderIO, 
  -- * compatibility
  (Language.Sparcl.Pretty.<$>), (<$$>), (</>), (<//>), 
  text, linebreak, empty, semiBraces, 
  
  -- ** colors/styles
  red, dullcyan, bold
  ) where

import           Prettyprinter hiding (Pretty (..), Doc)
import           qualified Prettyprinter as P 
import           qualified Prettyprinter.Render.Terminal as P 
-- import Text.PrettyPrint.ANSI.Leijen (Doc)
import           System.IO                    (Handle)

import qualified Data.Map                     as M

type Precedence = Int

type Doc = P.Doc P.AnsiStyle

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
  ppr = P.pretty 

instance Pretty Int where
  ppr = P.pretty

instance Pretty Double where
  ppr = P.pretty 

instance Pretty Char where
  ppr = P.viaShow 
  pprList _ = P.viaShow 

instance Pretty Rational where 
  ppr = P.viaShow

instance (Pretty a, Pretty b) => Pretty (a, b) where
  ppr (a, b) = parens $ align (ppr a) <> comma <+> align (ppr b)

prettyShow :: Pretty t => t -> String
prettyShow x = show (ppr x)

prettyPut :: Pretty t => t -> IO ()
prettyPut x = P.putDoc (ppr x)

prettyPutLn :: Pretty t => t -> IO ()
prettyPutLn x = P.putDoc (ppr x <> line)

hPrettyPut :: Pretty t => Handle -> t -> IO ()
hPrettyPut h x = P.hPutDoc h (ppr x)

hPrettyPutLn :: Pretty t => Handle -> t -> IO ()
hPrettyPutLn h x = P.hPutDoc h (ppr x <> line)

parensIf :: Bool -> Doc -> Doc
parensIf b d = if b then parens d else d

pprMap :: (Pretty k , Pretty v) => M.Map k v -> Doc
pprMap m = align $
  vsep [ ppr k <+> P.pretty "|->" <+> align (ppr v)
       | (k, v) <- M.toList m ]

-- compatibility 
(<$>) :: Doc -> Doc -> Doc 
x <$> y = vsep [x, y]
infixr 5 <$>

(<$$>) :: Doc -> Doc -> Doc 
x <$$> y = vcat [x, y]
infixr 5 <$$>

(</>) :: Doc -> Doc -> Doc 
x </> y = fillSep [x, y]
infixr 5 </>

(<//>) :: Doc -> Doc -> Doc 
x <//> y = fillCat [x, y] 
infixr 5 <//>

text :: String -> Doc 
text = P.pretty 

linebreak :: Doc 
linebreak = P.line' 

empty :: Doc 
empty = P.emptyDoc

red :: Doc -> Doc 
red = P.annotate (P.color P.Red) 

dullcyan :: Doc -> Doc 
dullcyan = P.annotate (P.colorDull P.Cyan)

bold :: Doc -> Doc 
bold = P.annotate P.bold 

semiBraces :: [Doc] -> Doc 
semiBraces = P.encloseSep P.lbrace P.rbrace P.semi 

hPutDocWith :: Handle -> Int -> Double -> Doc -> IO () 
hPutDocWith h textWidth ribbonWidth d = 
  P.renderIO h (P.layoutSmart (P.defaultLayoutOptions { P.layoutPageWidth = P.AvailablePerLine textWidth ribbonWidth }) d)