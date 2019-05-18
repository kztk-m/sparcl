{
{-# OPTIONS_GHC -fno-warn-tabs -Wno-unused-imports #-}

module Language.Sparcl.Surface.Lexer where

import Language.Sparcl.Name
import Language.Sparcl.SrcLoc (SrcSpan(..), Loc(..))
import qualified Language.Sparcl.Pretty as D
}

%wrapper "monadUserState"

$nl = [\n\r\f]

$small = [a-z] -- TODO: support unicodes
$large = [A-Z]

$digit = 0-9
@decimal = $digit+ 

@varId = $small ($small | $large | $digit | "'")*
@conId = $large ($small | $large | $digit | "'")*

$symbol = [\= \+ \- \* \/ \^ \< \> \$ \| \& \? \: \# \@ \! \.]

@op = ($symbol # \:) ($symbol | "'")* 

@modElem = $large ($small | $large) * 
@moduleName = @modElem ("." @modElem)*

@qVarId = (@moduleName ".") @varId
@qConId = (@moduleName ".") @conId
@qOp    = (@moduleName ".") @op 

@lam = "\" | [\955] -- lambda 
-- \"
@sharp = "#"
@omega = \969 -- ω
  
@rarr = "->" | \8594 -- ->

@lolli = "-o" | \8888               

@forall = "forall" | \8704               
                
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

  <0> "--" .* ;

  <0> {
  "if"      { theTok Tif }
  "then"    { theTok Tthen }
  "else"    { theTok Telse }

  "let"     { theTok Tlet }
  "in"      { theTok Tin  }
  "where"   { theTok Twhere }
  "end"     { theTok Tend }

  "case"    { theTok Tcase }
  "of"      { theTok Tof }
  "with"    { theTok Twith }

  "module"    { theTok Tmodule }
  "import"    { theTok Timport }
  "qualified" { theTok Tqualified }
  "as"        { theTok Tas }
  
  "def"     { theTok Tdef }
  "sig"     { theTok Tsig }
  "fixity"  { theTok Tfixity } 
  
  "data"    { theTok Tdata }
  "type"    { theTok Ttype }

  "lift"    { theTok Tlift }
  "unlift"  { theTok Tunlift }
  "rev"     { theTok Trev }
  "pin"     { theTok Tpin }
 
  
  ".."      { theTok Tddot }
  "."       { theTok Tdot }

  "::"      { theTok Tdcolon }
  ":"       { theTok Tcolon }

  ";"       { theTok Tsemi }
  ","       { theTok Tcomma } 
  
  
  "!" { theTok Tbang }
  "|" { theTok Tbar }
  "_" { theTok Tunderscore }
  "`" { theTok Tbackquote }

  "(" { theTok Tlparen }
  ")" { theTok Trparen }
  "{" { theTok Tlbrace }
  "}" { theTok Trbrace }
  "[" { theTok Tlbracket }
  "]" { theTok Trbracket }

  "=" { theTok Tequal } 
  
  @lam   { theTok Tlam }
  @rarr  { theTok Trarrow }
  @lolli { theTok Tlollipop }
  @forall { theTok Tforall }
  @sharp  { theTok Tsharp }
  @omega  { theTok Tomega } 
  
  @varId     { tok $ Tvarid . mkBName }
  @conId     { tok $ Tconid . mkBName }
  @op        { tok $ Top    . mkBName }
  @qVarId    { tok $ uncurry Tqvarid . mkQName }
  @qConId    { tok $ uncurry Tqconid . mkQName } 
  @qOp       { tok $ uncurry Tqop    . mkQName } 

  @char     { tok $ Tcharlit . read }
  @decimal  { tok $ Tintlit . read }
  }
  


{
type LexCode = Int

data AlexUserState 
  = AUS { ausCodeStack  :: [LexCode]
                          -- alex_scd s is assumeted to be a stack top
        , ausFilePath   :: !(Maybe FilePath) 
        }

data Token
  = Tif
  | Tthen
  | Telse

  | Tlet
  | Tin 
  | Twhere
  | Tend
  
  | Tcase
  | Tof
  | Twith

  | Tmodule
  | Timport
  | Tqualified
  | Tas

  | Tdef
  | Tsig
  | Tfixity
  | Tdata
  | Ttype
  | Tforall

  | Trev
  | Tlift
  | Tunlift
  | Tpin 

  -- Key punctuations
  | Tdot
  | Tddot
  | Tcolon
  | Tdcolon 
  | Tbang
  | Tsemi
  | Tcomma
  | Tunderscore
  | Tbackquote
  | Tbar
  
  | Tlam   
  | Tequal
  | Tlollipop  
  | Trarrow 
  | Tsharp
  | Tomega 

  -- parens 
  | Tlparen
  | Trparen
  | Tlbracket
  | Trbracket
  | Tlbrace
  | Trbrace 
  
  | Top       NameBase
  | Tvarid    NameBase
  | Tconid    NameBase
  | Tqop      ModuleName NameBase
  | Tqvarid   ModuleName NameBase
  | Tqconid   ModuleName NameBase 

  | Tintlit  Int
  | Tcharlit Char
    
  | Teof
  deriving (Eq, Ord, Show)


mkBName :: String -> NameBase
mkBName s = User s

mkQName :: String -> (ModuleName, NameBase)
mkQName s = case splitByLastDot s of
              (m, n) -> (ModuleName m, User n)
  where
    splitByLastDot = go "" ""

    go :: String -> String -> String -> (String, String) 
    go xs ys [] = (reverse xs, reverse ys)
    go xs ys (c:cs)
      | c == '.'  = go (reverse ys ++ "." ++ xs) "" cs
      | otherwise = go xs (c:ys) cs 
    

-- mkName :: String -> QName
-- mkName = \s -> case splitByDots s of
--                  [s'] -> BName (NormalName s')
--                  ss   -> QName (init ss) $ NormalName (last ss)
--   where
--     splitByDots :: String -> [String] 
--     splitByDots s = case break (== '.') s of
--       ([], _)  -> []
--       (xs, []) -> [xs]
--       (xs, ys) -> xs : splitByDots (tail ys) 

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
  (_, _, _, rest) <- alexGetInput 
  alexError $ show $ D.nest 2 $
    D.ppr (SrcSpan fp l c l c) D.<> D.text ":" D.<$$>
    D.text s D.</>
    D.nest 2 (D.text "near:" D.</> D.text (take 60 $ takeWhile (not . (`elem` "\n\r")) rest))

getAlexPosn :: Alex AlexPosn
getAlexPosn = Alex $ \s -> Right (s, alex_pos s)

getSpan :: AlexAction SrcSpan
getSpan _input len = do
  AlexPn _ sline scol <- getAlexPosn
  fp <- getFilePath
  return $ SrcSpan fp sline (scol - len) sline scol

-- mkTok :: SrcSpan -> Token -> Alex (Loc Token)
-- mkTok span token = do
--   return $ Loc span token

tok :: (String -> Token) -> AlexAction (Loc Token) 
tok f input@(_,_,_,str) len = do
  sp <- getSpan input len
  return $ Loc sp (f $ take len str)

theTok :: Token -> AlexAction (Loc Token)
theTok t = tok (const t) 

beginComment :: AlexAction (Loc Token)
beginComment _ _ = do
  pushLexCode comment
  alexMonadScan

endComment :: AlexAction (Loc Token) 
endComment _ _ = do
  _ <- popLexCode
  alexMonadScan

alexEOF = return $ Loc NoLoc Teof

}
