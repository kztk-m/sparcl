module Language.Sparcl.Surface.Parser.Helper where

import qualified Text.Megaparsec.Char.Lexer as L
import qualified Text.Megaparsec.Char as P
import qualified Text.Megaparsec as P 

import Language.Sparcl.SrcLoc
import Data.Void

type P m = P.ParsecT Void String m 

sp :: P m () 
sp = L.space P.space1 (L.skipLineComment "--") (L.skipBlockCommentNested "{-" "-}")

symbol :: String -> P m String
symbol = L.symbol sp

comma :: P m String
comma = symbol ","

parens :: P m a -> P m a
parens = P.between (symbol "(") (symbol ")")

getSrcLoc :: P m SrcSpan
getSrcLoc =
  fmap (\(P.SourcePos fp l c) -> SrcSpan (Just fp) (P.unPos l) (P.unPos c) (P.unPos l) (P.unPos c))
       P.getPosition 

withLoc :: Monad m => (SrcSpan -> P m a) -> P m a
withLoc m = getSrcLoc >>= m 

loc :: Monad m => P m a -> P m (Loc a) 
loc m = do
  (\s d e -> Loc (s <> e) d) <$> getSrcLoc <*> m <*> getSrcLoc


