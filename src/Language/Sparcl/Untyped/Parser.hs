module Language.Sparcl.Untyped.Parser where

import Language.Sparcl.Untyped.Syntax
import Language.Sparcl.SrcLoc

import qualified Text.Megaparsec.Char.Lexer as L
import qualified Text.Megaparsec.Char as P
import qualified Text.Megaparsec as P 
import Text.Megaparsec (MonadParsec, Parsec, ParsecT)

import qualified Data.Map as M
import Data.Map (Map)

import Data.Void 
import Data.Char
import Data.List.NonEmpty ( NonEmpty(..) )

import Control.Monad 
import Control.Applicative
import Control.Monad.Reader

-- import qualified Text.PrettyPrint.ANSI.Leijen as D
-- import Text.PrettyPrint.ANSI.Leijen (Doc)


type PM = ParsecT Void String (Reader (Maybe ModuleName))

type OpTable = Map Name (Prec, Assoc) 

sp :: PM () 
sp = L.space P.space1 (L.skipLineComment "--") (L.skipBlockCommentNested "{-" "-}")

symbol :: String -> PM String
symbol = L.symbol sp

parens :: PM a -> PM a 
parens = P.between (symbol "(") (symbol ")")

comma :: PM String 
comma = symbol ";"

getSrcLoc :: PM SrcLoc
getSrcLoc =
  fmap (\(P.SourcePos fp l c) -> SrcLoc (Just fp) (P.unPos l) (P.unPos c)) P.getPosition 

loc :: PM a -> PM (Loc a) 
loc m = do
  (\s d e -> Loc (Just (s,e)) d) <$> getSrcLoc <*> m <*> getSrcLoc 

ldeclP :: OpTable -> PM (LDecl, OpTable)
ldeclP tbl = do
  Loc s (p, f) <- loc (ddefP <|> dfixityP)
  return (Loc s p, f tbl) 
  where
    ddefP = do
      symbol "def"
      f <- baseNameP 
      pcs <- P.sepBy1 decBodyP (symbol "|")
      m <- ask 
      return $ (DDef (qname m f) pcs, id)

    decBodyP = do
      ps <- P.many (lpatP minBound)
      symbol "=" 
      (ws, tbl') <- P.option ([], tbl) (symbol "where" *> local (const Nothing) (ldeclsP tbl)) 
      e  <- lexpP tbl' minBound
      e' <- P.option Nothing (symbol "with" *> fmap Just (lexpP tbl' minBound))
      return $ (ps , Clause e ws e')

    dfixityP = do
      symbol "fixity"
      f <- baseNameP
      n <- fmap Prec intP
      m <- ask 
      r <- P.option N (do { symbol "left" ; return L} `mplus` do { symbol "right" ; return R})
      return $ (DFixity (qname m f) n r , M.insert f (n, r))

ldeclsP :: OpTable -> PM ([LDecl], OpTable)
ldeclsP tbl =
  (do (d, tbl')   <- ldeclP tbl
      (ds, tbl'') <- ldeclsP tbl'
      return $ (d:ds, tbl'')) <|>
  return ([], tbl) 

qname :: Maybe ModuleName -> Name -> QName
qname Nothing  n = BName n
qname (Just m) n = QName m n  

intP :: PM Int
intP = L.decimal 

nameElemP :: PM String
nameElemP = P.try $ do
  s <- P.some (P.satisfy (\x -> isPrint x && not (x `elem` ",();{}")))
  if (s `elem` ["->"])
    then P.unexpected (P.Tokens $ '-' :| ">")
    else return s 

baseNameP :: PM Name
baseNameP = do
  f  <- P.option False (True <$ P.char '_' )
  ns <- P.sepBy1 nameElemP (P.char '_') 
  b  <- P.option False (True <$ P.char '_')
  case ns of
    [n] | not f && not b -> return $ NormalName n
    _                    -> return $ MixFix ns f b
                                                          
    

lexpP :: OpTable -> Prec -> PM LExp
lexpP tbl k = loc (expP tbl k)

{-
In the context k, the operators of precedence >= k can only occur without parens.

The basic idea is just to recursvely call parsing with with appropriate precedence.

The problematic case is left-open operators; we have to left-fact them before parsing.

Thus, for 

   P ::= P Q1 | ... | P Qn | R

where Q1 ... Qn are left-associative, left-open operators, 
we reprelace them as

   P ::= many (Q1 | ... | Qn) R

For example, consider + (at 1) and * (at 2).

  P1 ::= P1 + P2 | P2 * A | A
  P2 ::= P2 * A | A

Let opTable is the list of operators that are sorted by the precedence downwardly.

  P (ops:opTable) = many (choice [p | p <- leftAssocOp ops P opTable]) (R (ops:opTable))
  R (ops:opTable) = otherOp ops P opTable <|> A
  P [] = A

Here, xxxOp ops P tables gathers xxx operators where the P appears in the ends will be replaced by (P tables) while
other are replaced by (P initTables)

The precedence table includes: 

  "case"   rightassoc -1 
  "let"    rightassoc -1
  \ps -> e rightassoc -1


  !e       rightassoc (maxBound - 1)
  e e      leftassoc  (maxBound - 1) 



-}

expP :: OpTable -> Prec -> PM Exp
expP tbl k = undefined 

lpatP :: Prec -> PM LPat 
lpatP = undefined 
