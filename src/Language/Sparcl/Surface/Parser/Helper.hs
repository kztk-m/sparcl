{-# LANGUAGE CPP #-}

module Language.Sparcl.Surface.Parser.Helper where

import qualified Text.Megaparsec            as P
import qualified Text.Megaparsec.Char       as P
import qualified Text.Megaparsec.Char.Lexer as L

import           Data.Void
import           Language.Sparcl.SrcLoc

import           Control.Applicative

type P m = P.ParsecT Void String m

sp :: P m ()
sp = L.space P.space1 (L.skipLineComment "--") (L.skipBlockCommentNested "{-" "-}")

symbol :: String -> P m String
symbol = L.symbol sp

comma :: P m String
comma = symbol ","

semicolon :: P m String
semicolon = symbol ";"

rightArrow :: P m String
rightArrow = symbol "->" <|> symbol "→"

leftArrow :: P m String
leftArrow = symbol "<-" <|> symbol "←"

lollipop :: P m String
lollipop = symbol "-o" <|> symbol "⊸"

dRightArrow :: P m String
dRightArrow = symbol "=>" <|> symbol "⇒"

symForAll :: P m String
symForAll = symbol "forall" <|> symbol "∀"

parens :: P m a -> P m a
parens = P.between (symbol "(") (symbol ")")

getSrcLoc :: P m SrcSpan
getSrcLoc =
  fmap (\(P.SourcePos fp l c) -> SrcSpan (Just fp) (P.unPos l) (P.unPos c) (P.unPos l) (P.unPos c))

#if MIN_VERSION_megaparsec(7,0,0)
    P.getSourcePos
#else
    P.getPosition
#endif

withLoc :: Monad m => (SrcSpan -> P m a) -> P m a
withLoc m = getSrcLoc >>= m

loc :: Monad m => P m a -> P m (Loc a)
loc m =
  (\s d e -> Loc (s <> e) d) <$> getSrcLoc <*> m <*> getSrcLoc


