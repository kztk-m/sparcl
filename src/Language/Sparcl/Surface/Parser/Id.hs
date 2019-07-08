module Language.Sparcl.Surface.Parser.Id where

import qualified Text.Megaparsec                       as P
import qualified Text.Megaparsec.Char                  as P

import           Language.Sparcl.Name
import           Language.Sparcl.Surface.Parser.Helper

import           Text.Megaparsec                       ((<?>), (<|>))

import           Control.Monad                         (void, when)
import qualified Data.List.NonEmpty                    as NonEmpty

modElem :: P m String
modElem = (:) <$> P.upperChar <*> P.many P.alphaNumChar

moduleName :: P m ModuleName
moduleName =
  (\a as -> ModuleName $ concat (a:as)) <$>
  modElem <*> P.many (P.try ((:) <$> P.char '.' <*> modElem))
  <?> "module name"


keyword :: Monad m => String -> P m String
keyword s = do
  r <- P.string s
  P.notFollowedBy P.alphaNumChar
  sp
  return r

qop :: Monad m => P m SurfaceName
qop =
  (do m <- moduleName
      void $ P.char '.'
      Qual m <$> opRaw)
  <|> op
  <?> "qualified operator"

op :: Monad m => P m SurfaceName
op = (Bare <$> opRaw) <?> "operator"

opRaw :: Monad m => P m NameBase
opRaw =
  P.try (do x <- P.some (P.oneOf "=+*-/^<>$|&?:#@!.")
            when (x `elem` specialOp) $
              P.unexpected $ P.Label $ NonEmpty.fromList $ "reserved op " ++ show x
            return $ User x)
  <?> "operator"

specialOp :: [String]
specialOp = ["|", "->", "=>", "<-", "\\","--", "@", "#", ":", ";"]

varidRaw :: P m String
varidRaw = (:) <$> P.lowerChar <*> P.many (P.alphaNumChar <|> P.char '\'')

keyWords :: [String]
keyWords = ["let", "in", "if", "then", "else", "where", "end",
            "case", "of", "with", "rev", "module", "import",
            "sig", "def", "data", "type", "fixity",
            "lift", "unlift", "pin",
            "revdo", "before" ]

varName :: Monad m => P m SurfaceName
varName = P.try (do x <- varidRaw
                    when (x `elem` keyWords) $
                      P.unexpected $ P.Label $ NonEmpty.fromList $ "keyword " ++ show x
                    return $ Bare (User x))
          <?> "variable name"

varOpName :: Monad m => P m SurfaceName
varOpName = varName <|> P.try (parens op)

qvarName :: Monad m => P m SurfaceName
qvarName =
  (do mm <- P.optional (moduleName <* P.char '.')
      Bare (User x) <- varName
      case mm of
        Just m  -> return $ Qual m (User x)
        Nothing -> return $ Bare (User x))
  <?> "qualified variable name"

qvarOpName :: Monad m => P m SurfaceName
qvarOpName =
  qvarName <|> P.try (parens qop)


conidRaw :: P m String
conidRaw = (:) <$> P.upperChar <*> P.many P.alphaNumChar
           <?> "constructor name"

conName :: Monad m => P m SurfaceName
conName = Bare . User <$> conidRaw

-- We have the special treatment for the case.
qconName :: Monad m => P m SurfaceName
qconName =
  (do ms <- (:) <$> modElem <*> P.many (P.char '.' *> modElem)
      case ms of
        [m] -> return $ Bare (User m)
        _   -> return $ Qual (ModuleName $ concat $ init ms) (User $ last ms))
  <?> "qualified constructor name"


lambda :: P m String
lambda = symbol "\\" <|> symbol "λ"


