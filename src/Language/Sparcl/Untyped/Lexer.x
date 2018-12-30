{
{-# OPTIONS_GHC -fno-warn-tabs #-}

module Language.Sparcl.Untyped.Lexer where

import Language.Sparcl.Name
import Language.Sparcl.SrcLoc
import Language.Sparcl.Pretty

import Data.List (break)
}

%wrapper "monadUserState"

@reserved =
  if | then | else | case | of | let | in | with | where | abort
  | import | module | with | lift | unlift | forward | backward
  | def | sig
  | rev 
  | qualified | as | forall

@punct =
  "." | "->" | "(" | ")" | "{" | "}" | "[" | "]" | ";" | ":" | "," | "=" 
  | "|" | "_" | "@" | "!" | "\" -- " 

$nl = [\n\r\f]

$small = [a-z] -- TODO: support unicodes
$large = [A-Z]

$digit = 0-9
@decimal = $digit+ 

@varId = $small ($small | $large | $digit | "'")*
@conId = $large ($small | $large | $digit | "'")*

$symbol = [\= \+ \- \* \/ \^ \< \> \$ \| \& \? \: \# \@ \!]

@op = $symbol ($symbol | "'")* 

@modElem = $large ($small | $large) * 
@moduleName = @modElem ("." @modElem)*

@qVarId = @moduleName "." @varId
@qConId = (@moduleName ".")? @conId
@qOp    = (@moduleName ".")? @op 

@string = \" ( ($printable # [\"\\]) | "\" "\" | "\n" | "\t" | "\r" | "\" [\"] )
* \" -- "
@char   = \' ( ($printable # [\'\\]) | "\" "\" | "\n" | "\t" | "\r" | "\" [\"] )
 \' 

$nbsp = $white # $nl 

tokens :-
  $white+;

  <0, comment> "{-"   { beginComment }
  <comment>    "-}"   { endComment }
  <comment>    [.\n];

  <0> "--" $nbsp * ;

  <0> {
  @reserved { tok $ TkKey }
  @punct    { tok $ TkPunct } 
  @char     { tok $ TkCharLit . read }
  @decimal  { tok $ TkIntLit . read }
  @varId     { tok $ TkVarID . NormalName } 
  @qVarId    { tok $ TkQVarID . mkName }
  @qConId    { tok $ TkConID . mkName } 
  @qOp       { tok $ TkOp . mkName } 
  }
  


{
type LexCode = Int

data AlexUserState 
  = AUS { ausCodeStack  :: [LexCode]
                          -- alex_scd s is assumeted to be a stack top
        , ausFilePath   :: !(Maybe FilePath) 
        }

data Token
  = TkKey     String
  | TkOp      QName 
  | TkVarID   Name
  | TkQVarID  QName 
  | TkConID   QName
  | TkIntLit  Int
  | TkCharLit Char
    
  | TkPunct String    
  | TkEOF
  deriving (Eq, Ord, Show)


mkName :: String -> QName
mkName = \s -> case splitByDots s of
                 [s'] -> BName (NormalName s')
                 ss   -> QName (init ss) $ NormalName (last ss)
  where
    splitByDots :: String -> [String] 
    splitByDots s = case break (== '.') s of
      ([], _)  -> []
      (xs, []) -> [xs]
      (xs, ys) -> xs : splitByDots (tail ys) 

getUST :: Alex AlexUserState
getUST = Alex $ \s@AlexState { alex_ust = ust } -> Right (s, ust)

setUST :: AlexUserState -> Alex ()
setUST ust = seq ust $ Alex $ \s -> Right (s { alex_ust = ust }, ())

alexInitUserState :: AlexUserState
alexInitUserState = AUS [] Nothing

getFilePath :: Alex (Maybe FilePath)
getFilePath = do
  ust <- getUST
  return $ ausFilePath ust

setFilePath :: FilePath -> Alex ()
setFilePath fp = do
  ust <- getUST
  setUST (ust { ausFilePath = Just fp })

pushLexCode :: LexCode -> Alex ()
pushLexCode code = do
  ust  <- getUST
  prev <- alexGetStartCode
  let ust' = ust { ausCodeStack = prev : ausCodeStack ust }
  setUST ust'
  alexSetStartCode code

popLexCode :: Alex LexCode
popLexCode = do
  ust <- getUST
  curr <- alexGetStartCode
  let code : rest = ausCodeStack ust
  let ust' = ust { ausCodeStack = rest }
  setUST ust'
  alexSetStartCode code
  return curr


lexError :: String -> Alex a
lexError s = do
  fp <- getFilePath
  AlexPn _ l c <- getAlexPosn
  alexError $ prettyShow (SrcSpan (SrcLoc fp l c) (SrcLoc fp l c)) ++ ":\n" ++ s

getAlexPosn :: Alex AlexPosn
getAlexPosn = Alex $ \s -> Right (s, alex_pos s)

getSpan :: AlexAction SrcSpan
getSpan _input len = do
  AlexPn _ sline scol <- getAlexPosn
  fp <- getFilePath
  return $ SrcSpan (SrcLoc fp sline (scol - len)) (SrcLoc fp sline scol)

-- mkTok :: SrcSpan -> Token -> Alex (Loc Token)
-- mkTok span token = do
--   return $ Loc span token

tok :: (String -> Token) -> AlexAction (Loc Token) 
tok f input@(_,_,_,str) len = do
  span <- getSpan input len
  return $ Loc span (f $ take len str)

beginComment :: AlexAction (Loc Token)
beginComment _ _ = do
  pushLexCode comment
  alexMonadScan

endComment :: AlexAction (Loc Token) 
endComment _ _ = do
  _ <- popLexCode
  alexMonadScan

alexEOF = return $ Loc NoLoc TkEOF  

}
