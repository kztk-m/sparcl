module Language.Sparcl.Untyped.Parser where

import Language.Sparcl.Untyped.Syntax
import Language.Sparcl.SrcLoc

import qualified Text.Megaparsec.Char.Lexer as L
import qualified Text.Megaparsec.Char as P
import qualified Text.Megaparsec as P 
import qualified Control.Monad.Combinators.Expr as P

import Text.Megaparsec (MonadParsec, Parsec, ParsecT)

import qualified Data.Map as M
import Data.Map (Map)

import Data.Void 
import Data.Char
import qualified Data.List.NonEmpty ( fromList )
import Data.List.NonEmpty ( NonEmpty(..) )

import Data.List (nub) 

import Control.Monad 
import Control.Applicative
import Control.Monad.State 
import Control.Monad.Fail (MonadFail)
import qualified Control.Monad.Fail as Fail

-- import Control.Monad.Reader

-- import qualified Text.PrettyPrint.ANSI.Leijen as D
-- import Text.PrettyPrint.ANSI.Leijen (Doc)

import System.Directory as Dir
import System.FilePath as FP 

type ModuleParser = Parsec Void String 
type PM = ParsecT Void String (State PInfo)

data PInfo = PInfo {
  piCurrentModule :: Maybe ModuleName,
  piBoundNames    :: [QName],
  piOpTable       :: OpTable 
  }

defaultPInfo :: PInfo
defaultPInfo = PInfo {
  piCurrentModule = Nothing,
  piBoundNames    = [base "+", base "-"],
  piOpTable =
      insertOp (Prec 60) R (base "+") $
      insertOp (Prec 60) R (base "-") $ M.empty 
   }
  where
    base s = QName ["Base"] (NormalName s) 

putOpTable :: MonadState PInfo m => OpTable -> m ()
putOpTable opTable = do
  s <- get
  put $! s { piOpTable = opTable }

putBoundNames :: MonadState PInfo m => [QName] -> m ()
putBoundNames ns = do
  s <- get
  put $! s { piBoundNames = ns } 

getCurrentModule :: MonadState PInfo m => m ModuleName
getCurrentModule = do
  x <- gets piCurrentModule
  case x of
    Nothing -> return ["Main"]
    Just m  -> return m 
  
refineName :: (MonadFail m, MonadState PInfo m) => QName -> m QName
refineName (QName m n) = do 
  m' <- getCurrentModule
  if m == m'
    then return (BName n)   -- Names in the current module should not be qualified 
    else return (QName m n)
refineName (BName n) = do
  ns <- gets piBoundNames
  cm <- getCurrentModule
  let res = checkNames cm n ns
  case filter (/=cm) res of
    [m]  -> return (QName m n)
    []   -> return (BName n)
    _    -> Fail.fail $ "Ambiguous name `" ++ show n ++ "' " ++ show (nub res) 
  where
    checkNames :: ModuleName -> Name -> [QName] -> [ModuleName]
    checkNames cm n [] = []
    checkNames cm n (BName n' : ns) =
      if n == n' then cm : checkNames cm n ns else checkNames cm n ns
    checkNames cm n (QName m n' : ns) =
      if n == n' then m : checkNames cm n ns else checkNames cm n ns 
  

data NameInfo = NameInfo { niCurrentModule  :: Maybe ModuleName,
                           niAvailableNames :: [QName]
                         }


type OpTable = Map Prec (Map Assoc [QName])

insertOp :: Prec -> Assoc -> QName -> OpTable -> OpTable
insertOp k assoc n tbl =
  let m' = maybe M.empty id $ M.lookup k tbl 
  in M.insert k (M.insertWith (++) assoc [n] m') tbl 


-- moduleP :: ModuleParser (ModuleName, [Export], [Import])
-- moduleP = do
--   (moduleName, exports) <- P.option (["Main"], []) moduleLineP
--   imports <- P.many importLineP
--   return (moduleName, exports, imports)
--   where
--     moduleLineP = do
--       symbol "module"
--       moduleName <- moduleNameP 
--       es <- P.option [] (parens $ P.sepEndBy (varIdentP <|> conIdentP) comma)
--       symbol "where"
--       return (moduleName, es) 
                                                   
--     importLineP = do
--       symbol "import"
--       moduleName <- moduleNameP
--       return $ Import moduleName []


-- type Parsing = StateT (Map ModuleName [LDecl]) IO 

-- parseFile :: [ModuleName] -> [FilePath] -> FilePath -> Parsing [LDecl]
-- parseFile visited dirs fp = do
--   s <- lift $ readFile fp
--   let (contState, res) = P.runParser' moduleP (initState s)
--   case res of
--     Left err          -> fail (P.parseErrorPretty err)
--     Right (n, es, is) -> do 
--       checkName dirs n fp
--       mapM (parseModule (n:visited) dirs . importModuleName) is
--       initOpTable <- M.union <$> mapM makeInitTable is
--       let decls = evalState (P.runParserT' ldeclsP contState) initOpTable
--       importedNames <- concat <$> mapM getNames is
--       tbl <- get
--       put $! M.insert n decls tbl
--       return decls'
--   where
--     initState :: String -> P.State String
--     initState s = P.State { P.stateInput = s,
--                             P.statePos = P.initialPos "fp" :| [], 
--                             P.stateTokensProcessed = 0,
--                             P.stateTabWidth = P.defaultTabWidth 
--                           }


-- parseModule :: [ModuleName] -> [FilePath] -> ModuleName -> Parsing [LDecl]
-- parseModule visited dirs mn = do
--   tbl <- get
--   case M.lookup mn tbl of
--     Just res -> return res
--     Nothing -> do 
--       let fp = moduleNameToFilePath mn
--       let searchFiles = map (FP.</> fp) dirs
--       fs <- mapM (lift . Dir.doesFileExist) searchFiles
--       case map fst $ filter snd $ zip searchFiles fs of
--         fp:_ -> parseFile visited dirs fp
--         _    -> fail $ "ERROR: Cannot find module " ++ foldr1 (\a b -> a ++ "." ++ b) mn

-- ext :: String
-- ext = "sparcl"

-- moduleNameToFilePath :: ModuleName -> FilePath
-- moduleNameToFilePath mn =
--   (foldr1 (FP.</>) mn) FP.<.> ext

-- checkName :: [FilePath] -> ModuleName -> FilePath -> Parsing ()
-- checkName dirs mn fp =
--   let f = moduleNameToFilePath mn
--   in if fp `elem` map (FP.</> f) dirs then
--        return ()
--      else
--        fail $ "ERROR: Module " ++ foldr1 (\a b -> a ++ "." ++ b) mn ++ " must be defined in " ++ f 
                                              
  
parseDeclTest :: PInfo -> String -> String -> IO [LDecl]
parseDeclTest pi source s =
  case evalState (P.runParserT ldeclsP source s) pi of
    Right r -> return r
    Left  e -> Fail.fail $ P.parseErrorPretty e 

parseExp :: PInfo -> String -> Either (P.ParseError Char Void) LExp 
parseExp pinfo s =
  evalState (P.runParserT lexpP "<interactive>" s) pinfo
    
parseExpTest :: PInfo -> String -> IO LExp
parseExpTest pinfo s =
  case parseExp pinfo s of
    Right e -> return e
    Left  e -> do
      putStrLn $ P.parseErrorPretty e
      Fail.fail ""

parseDecl' :: PInfo -> P.State String ->
              (P.State String, Either (P.ParseError Char Void) [LDecl])
parseDecl' pi pstate =
  evalState (P.runParserT' ldeclsP pstate) pi 



sp :: MonadParsec e String m => m () 
sp = L.space P.space1 (L.skipLineComment "--") (L.skipBlockCommentNested "{-" "-}")

lexeme :: MonadParsec e String m => m a -> m a
lexeme = L.lexeme sp 

symbol :: MonadParsec e String m => String -> m String
symbol = L.symbol sp

parens :: MonadParsec e String m => m a -> m a 
parens = P.between (symbol "(") (symbol ")")

braces :: MonadParsec e String m => m a -> m a
braces = P.between (symbol "{") (symbol "}")

brackets :: MonadParsec e String m => m a -> m a
brackets = P.between (symbol "[") (symbol "]") 

comma :: MonadParsec e String m => m String 
comma = symbol ","

getSrcLoc :: PM SrcLoc
getSrcLoc =
  fmap (\(P.SourcePos fp l c) -> SrcLoc (Just fp) (P.unPos l) (P.unPos c)) P.getPosition 

loc :: PM a -> PM (Loc a) 
loc m = do
  (\s d e -> Loc (SrcSpan s e) d) <$> getSrcLoc <*> m <*> getSrcLoc 

defP :: PM Decl
defP = ddefP 
  where
    ddefP :: PM Decl
    ddefP = do
      symbol "def"
      f <- rawVarIdentP  
      pcs <- P.sepBy1 decBodyP (symbol "|")
      ns <- gets piBoundNames
      putBoundNames (BName f : ns) 
      return $ DDef f pcs

    decBodyP = do
      ps <- P.many (loc simplePatP)
      symbol "="
      c <- clauseP 
      return $ (ps , c)

whereP :: PM [LDecl]
whereP = P.option [] (symbol "where" *> braces ldeclsP) 

withP :: PM (Maybe LExp)
withP = P.option Nothing (symbol "with" *> fmap Just lexpP)

normalClauseP :: PM Clause
normalClauseP = do
  e  <- lexpP
  ws <- whereP
  return $ Clause e ws Nothing

clauseP :: PM Clause
clauseP = do
  e  <- lexpP
  ws <- whereP
  e' <- withP
  return $ Clause e ws e' 
 

fixityP :: PM Decl
fixityP = do
  symbol "fixity"
  f <- rawVarIdentP
  n <- fmap Prec intP
  tbl <- gets piOpTable
  r <- P.option N $ leftP `mplus` rightP
  -- TODO: Reject double assignment of fixity.
  f' <- refineName (BName f) 
  putOpTable $! insertOp n r f' tbl 
  return $ DFixity (BName f) n r
    where
      leftP  = L <$ symbol "left"
      rightP = R <$ symbol "right" 
      


ldeclP :: PM LDecl
ldeclP = loc (defP <|> fixityP)
  where

reservedOp :: [String]
reservedOp = ["->", "!", "<-", "=>", "\\"]

reservedIdent :: [String]
reservedIdent = ["let", "in", "case", "of", "with", "def", "fixity", "sig", "type", "data", "where"]

assertNonReserved :: MonadParsec e String m => String -> [String] -> m String
assertNonReserved s ss
  | s `elem` ss = P.unexpected (P.Tokens $ Data.List.NonEmpty.fromList s)
  | otherwise   = return s 

moduleNameP :: MonadParsec e String m => m [String]
moduleNameP =
  P.sepBy1 moduleElemP (P.char '.')

moduleElemP :: MonadParsec e String m => m String 
moduleElemP =
  (:) <$> P.upperChar <*> P.many (P.lowerChar <|> P.upperChar)

modulePrefixP :: MonadParsec e String m => m [String]
modulePrefixP =
  P.endBy1 moduleElemP (P.char '.')

quantify :: MonadParsec e String m => m Name -> m QName
quantify m = do
  ms <- P.option Nothing (P.try $ Just <$> modulePrefixP )
  n  <- m
  return $ case ms of
    Nothing -> BName n
    Just ms -> QName ms n 
  

rawOpP :: MonadParsec e String m => m Name
rawOpP = do 
  s <- lexeme $
       (:) <$> (P.satisfy ok1 P.<?> "symbol") <*> P.many (P.satisfy ok2 P.<?> "symbol, mark and \"'\"")
  NormalName <$> assertNonReserved s reservedOp  
  where
    okPunct c = c `elem` "!#%&*-./:;?@"
    ok1 c = isSymbol c || okPunct c
    ok2 c = ok1 c || isMark c || c == '\''

varIdentP :: MonadParsec e String m => m QName
varIdentP = P.try (parens (quantify rawOpP)) <|> quantify rawProperVarIdentP

rawVarIdentP :: MonadParsec e String m => m Name
rawVarIdentP = P.try (parens rawOpP) <|> rawProperVarIdentP 

rawProperVarIdentP :: MonadParsec e String m => m Name
rawProperVarIdentP = do 
  s <- lexeme $ (:) <$> P.lowerChar <*> P.many (P.alphaNumChar <|> P.char '\'')
  NormalName <$> assertNonReserved s reservedIdent 

-- Currently, infix constructors are not supported. 
conIdentP :: MonadParsec e String m => m QName
conIdentP = quantify rawConIdentP 

rawConIdentP :: MonadParsec e String m => m Name
rawConIdentP = do
  s <- lexeme $ (:) <$> P.upperChar <*> P.many (P.alphaNumChar <|> P.char '\'')
  return $ NormalName s 
  
ldeclsP :: PM [LDecl]
ldeclsP = P.many ldeclP 

-- qname :: Maybe ModuleName -> Name -> QName
-- qname Nothing  n = BName n
-- qname (Just m) n = QName m n  

intP :: PM Int
intP = L.decimal 

-- nameElemP :: PM String
-- nameElemP = P.try $ do
--   s <- P.some (P.satisfy (\x -> isPrint x && not (x `elem` ",();{}")))
--   if (s `elem` ["->"])
--     then P.unexpected (P.Tokens $ '-' :| ">")
--     else return s 

-- baseNameP :: PM Name
-- baseNameP = do
--   f  <- P.option False (True <$ P.char '_' )
--   ns <- P.sepBy1 nameElemP (P.char '_') 
--   b  <- P.option False (True <$ P.char '_')
--   sp {- skip spaces -} 
--   case ns of
--     [n] | not f && not b -> return $ NormalName n
--     _                    -> return $ MixFix ns f b
                                                          
    

lexpP :: PM LExp
lexpP = loc expP 


expP :: PM Exp
expP = caseExpP <|> absExpP <|> opExpP 

caseExpP :: PM Exp
caseExpP = do
  symbol "case"
  e0 <- lexpP
  symbol "of"
  pcs <- brackets $ flip P.sepEndBy (symbol ";") $ do
    p <- lpatP
    symbol "->"
    e <- clauseP
    return (p, e)
  return $ Case e0 pcs 

absExpP :: PM Exp
absExpP = do
  symbol "\\"
  ps <- P.someTill (loc simplePatP) (symbol "->")
  e <- lexpP
  return $ Abs ps e 

lapp a b = Loc (location a <> location b) (App a b)

opExpP :: PM Exp
opExpP = do
  -- TODO: Currently, explicit fixity assignment is needed. 
  tbl <- gets piOpTable 
  unLoc <$> P.makeExprParser lappExpP (makeTable tbl) 
  where
    makeTable :: OpTable -> [[ P.Operator PM LExp ]]
    makeTable tbl =
      map (concatMap (uncurry conv) . M.toList . snd) $ M.toList tbl

    conv :: Assoc -> [QName] -> [ P.Operator PM LExp ]
    conv a ns = map (\n -> infixOf a $ do
                        (mod, base) <- case n of
                                         BName (NormalName n) -> do 
                                           m <- getCurrentModule
                                           return (m, n)
                                         QName m (NormalName n) -> return (m, n) 
                        Loc l _ <- loc (P.try (symbol $ moduleNameToStr mod ++ "." ++ base)
                                        <|> symbol base) 
                        return $ \a b ->
                          foldl lapp (Loc l $ Var n) [a,b]) ns
      where
        infixOf L = P.InfixL
        infixOf R = P.InfixR
        infoxOf _ = P.InfixN

lappExpP :: PM LExp
lappExpP =
  (do Loc l n <- loc varIdentP
      n' <- refineName n 
      es <- P.many lsimpleExpP
      return $ foldl lapp (Loc l $ Var n') es)
  <|>
  loc (do c  <- refineName =<< conIdentP 
          es <- P.many lsimpleExpP
          return $ Con c es)
  <|> bangExpP
  <|> parens lexpP
  <|> loc literalP 
  

lsimpleExpP :: PM LExp
lsimpleExpP =
  bangExpP 
  <|> parens lexpP
  <|> varP
  <|> conP 
  <|> loc literalP
  where
    varP = fmap Var <$> loc (do {n <- varIdentP ; refineName n })
    conP = loc $ do
      c <- refineName =<< conIdentP
      return $ Con c [] 

bangExpP :: PM LExp
bangExpP = symbol "!" *> lsimpleExpP 
  
literalP :: PM Exp
literalP = (P.try intLitP) <|> floatLitP <|> charLitP
  where
    intLitP   = (Lit . LitInt)    <$> lexeme L.decimal
    floatLitP = (Lit . LitDouble) <$> lexeme L.float
    charLitP  = (Lit . LitChar)   <$> lexeme (P.char '\'' *> L.charLiteral <* P.char '\'')
  

lpatP :: PM LPat 
lpatP = loc patP

patP :: PM Pat
patP =
  (do c <- refineName =<< conIdentP
      ps <- P.many (loc simplePatP)
      return $ PCon c ps)
  <|> simplePatP 
  
  

simplePatP :: PM Pat
simplePatP =
  (PBang <$> loc (symbol "!" *> simplePatP))
  <|> (PREV <$> loc (symbol "rev" *> simplePatP))
  <|> parens patP
  <|> varP
  where
    varP = PVar <$> rawVarIdentP


{-
In the context k, the operators of precedence >= k can only occur without parens.

The basic idea is just to recursvely call parsing with with appropriate precedence.

The problematic case is left-open operators; we have to left-fact them before parsing.

Thus, for 

   P ::= P Q1 | ... | P Qn | R

where Q1 ... Qn are left-associative, left-open operators, 
we reprelace them as

   P ::= R (Q1 | ... | Qn)*

For example, consider + (at 1) and * (at 2).

  P1 ::= P1 + P2 | P2 
  P2 ::= P2 * A | A

It will be left factored as follows.

  P1 ::= P2 (+ P2)*
  P2 ::= A (* A) 
 
The precedence table can include: 

  "case"   rightassoc 
  "let"    rightassoc 
  \ps -> e rightassoc 


  !e       rightassoc 
  e e      leftassoc  

-}

-- data OpSem = SemLOpen  ( (OpList -> PM LExp) -> OpList -> PM LExp -> PM (LExp -> LExp) )
--            | SemOther  ( (OpList -> PM LExp) -> OpList -> PM LExp -> PM LExp )
-- type OpList = [ [ OpSem ] ]

-- convertOpTable :: OpTable -> OpList
-- convertOpTable tbl =
--   let ls = reverse $ map snd $ M.toList tbl 
--   in map (concatMap (\(k,v) -> map (conv k) v) . M.toList) ls
--   where
--     app a b = Loc (location a <> location b) (App a b)

--     makeMiddleParser :: PM LExp -> [String] -> PM (Loc [LExp])
--     makeMiddleParser cparser ns = 
--       foldr1 (\a b -> (\(Loc l1 r1) r2 (Loc l3 r3) ->
--                                            Loc (l1 <> l3) (r1 ++ [r2] ++ r3)) <$> a <*> cparser <*> b) $
--       map (\n -> loc ([] <$ P.string n)) ns
      
--     conv :: Assoc -> Name -> OpSem    
--     conv _ (NormalName n) = SemOther $ \_ _ _ ->
--       loc (Var <$> BName <$> NormalName <$> P.string n)
--     conv L opName@(MixFix ns True b) = SemLOpen $ \p tbl cparser ->
--       case tbl of
--         [] | b -> mzero
--         _      ->
--           let middle :: PM (Loc [LExp]) 
--               middle = makeMiddleParser cparser ns 
--               tl :: PM (Loc [LExp]) 
--               tl = if b then (\(Loc l a) b -> Loc l (a ++ [b])) <$> middle <*> p (tail tbl) else middle
--           in (\(Loc l es) e -> foldl app (Loc l $ Var $ BName opName) (e:es))  <$> tl
--     conv a opName@(MixFix ns b1 b2) = SemOther $ \p tbl cparser ->
--       case tbl of
--         [] | (a /= L && b1) || (a /= R && b2) -> mzero
--         _  ->
--           let middle :: PM (Loc [LExp])
--               middle = makeMiddleParser cparser ns

--               leftEnd :: PM (Loc [LExp])
--               leftEnd =
--                 let tbl' = case a of
--                       L -> tbl
--                       _ -> tail tbl 
--                 in if b1 then (\a -> Loc mempty [a]) <$> p tbl' else pure (Loc mempty [])

--               rightEnd :: PM (Loc [LExp])
--               rightEnd =
--                 let tbl' = case a of
--                              R -> tbl
--                              _ -> tail tbl
--                 in if b2 then (\x -> Loc mempty [x]) <$> p tbl' else pure (Loc mempty [])
--           in (\(Loc l1 x1) (Loc l2 x2) (Loc l3 x3) ->
--                 foldl app (Loc (l1 <> l2 <> l3) $ Var $ BName opName) (x1 ++ x2 ++ x3)
--              ) <$> leftEnd <*> middle <*> rightEnd 
                                                                          

      
    

