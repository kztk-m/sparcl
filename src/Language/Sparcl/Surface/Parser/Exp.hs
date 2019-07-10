module Language.Sparcl.Surface.Parser.Exp where

import Language.Sparcl.Surface.Syntax hiding (whereClause)
import Language.Sparcl.Multiplicity
import Language.Sparcl.SrcLoc
import Language.Sparcl.Name
import Language.Sparcl.Pass
import Language.Sparcl.Literal

import qualified Text.Megaparsec.Char.Lexer as L
import qualified Text.Megaparsec.Char as P
import qualified Text.Megaparsec as P 

import Language.Sparcl.Surface.Parser.Helper
import Language.Sparcl.Surface.Parser.Id

import Text.Megaparsec ((<|>))

import Control.Monad 

import Data.Maybe (fromMaybe)
import qualified Data.Set as Set

-- import Language.Sparcl.Pretty (ppr)

import Control.Arrow (left) 

full :: P m a -> P m a
full p = sp *> p <* P.eof 

parseExp :: String -> Either String (LExp 'Parsing)
parseExp = left P.parseErrorPretty . P.runParser (full expr) "<unknown source>" 

parseExp' :: FilePath -> String -> Either String (LExp 'Parsing)
parseExp' fp = left P.parseErrorPretty . P.runParser (full expr) fp

parseModule :: FilePath -> String -> Either String (Module 'Parsing)
parseModule fp = left P.parseErrorPretty . P.runParser (full modul) fp 

parseDecl :: String -> Either String (Decls 'Parsing (Loc (TopDecl 'Parsing)))
parseDecl = left P.parseErrorPretty . P.runParser (full topDecls) "<unknown source>"

-- -- -- ptest :: P IO a -> String -> IO (Either (P.ParseError Char Void) a)
-- -- ptest :: (Monad m, Show (P.Token s), Show e) => ParsecT e s m b -> s -> m b
-- ptest p s = do
--   res <- P.runParserT p "<unknown source>" s
--   case res of
--     Left err -> error (P.parseErrorPretty err)
--     Right r  -> return r 


{-
E ::= \ P1 ... Pn -> E
   |  let localDecs in E
   |  case E of alts end
   |  OpExp

-}
expr :: Monad m => P m (LExp 'Parsing)
expr = getSrcLoc >>= \startLoc -> 
  (do void lambda
      ps <- P.some simplePat 
      void rightArrow
      e <- expr
      return $ Loc (startLoc <> location e) $ Abs ps e )
  <|>
  (do void $ keyword "let"
      decls <- localDecls
      void $ keyword "in"
      e <- expr
      return $ Loc (startLoc <> location e) $ Let decls e)
  <|>
  (do void $ keyword "case"
      e0   <- expr
      void $ keyword "of" 
      alts <- alternatives
      void $ keyword "end"
      endLoc <- getSrcLoc 
      return $ Loc (startLoc <> endLoc) $ Case e0 alts)
  <|>
  (do void $ keyword "revdo"
      as <- assignment `P.endBy` semicolon 
      void $ keyword "in"
      e <- expr
      return $ Loc (startLoc <> location e) $ RDO as e)
  <|> 
  (do e <- opExpr
      m <- P.optional (symbol ":" *> typeExpr)
      case m of
        Just ty -> pure $ Loc (location e <> location ty) $ Sig e ty
        Nothing -> pure e)


assignment :: Monad m => P m (LPat 'Parsing, LExp 'Parsing)
assignment = do
  p <- pat
  void leftArrow
  e <- expr
  return (p, e)

simplePat :: Monad m => P m (LPat 'Parsing)
simplePat = loc $ 
  conPat
  <|> varPat
  <|> (unLoc <$> tuplePat)
  <|> wildPat
  where
    conPat = do
      c <- L.lexeme sp qconName
      return $ PCon c []

    varPat = 
      PVar <$> L.lexeme sp varName
    
    wildPat = do
      void $ symbol "_"
      return (PWild () :: Pat 'Parsing)

tuplePat :: Monad m => P m (LPat 'Parsing)
tuplePat = mkTuplePat <$> 
  parens (pat `P.sepBy` comma)
  
pat :: Monad m => P m (LPat 'Parsing)
pat = do
  s <- getSrcLoc
  m <- P.optional (keyword "rev")
  p <- appPat 
  case m of
    Just _  -> return $ Loc (s <> location p) $ PREV p
    Nothing -> return p 

appPat :: Monad m => P m (LPat 'Parsing)   
appPat =
  P.try (loc $ do
            c <- qconName
            sp
            ps <- P.some simplePat
            return $ PCon c ps)
  <|>
  simplePat 

introForAll :: LTy 'Parsing -> LTy 'Parsing
introForAll ty =
  let freeVars = goL Set.empty ty Set.empty
  in foldr (\x -> Loc (location ty) . TForall x) ty freeVars
  where
    list _ [] = id
    list f (x:xs) = f x . list f xs

    goL xs = go xs . unLoc 

    goC xs (MEqMax t1 t2 t3) = goL xs t1 . goL xs t2 . goL xs t3
    goC xs (MSub   t1 t2)    = goL xs t1 . goL xs t2 

    go xs (TVar x) | x `Set.member` xs = id
                   | otherwise         = Set.insert x 
    go xs (TForall x t) = goL (Set.insert x xs) t
    go xs (TQual cs t)  = list (goC xs) cs . goL xs t

    go xs (TCon _ ts) = list (goL xs) ts
    go _  (TMult _)   = id

    

  
typeExpr :: Monad m => P m (LTy 'Parsing)
typeExpr = do
  ef    <- P.optional (symForAll *> P.many (varName <* sp) <* symbol ".")
  mid   <- getSrcLoc 
  ctxt  <- P.optional $ P.try (constraint <* dRightArrow)
  ty    <- arrTy
  return $ maybe id foralls ef $ maybe id (\cs -> Loc (mid <> location ty) . TQual cs) ctxt ty
    where
      foralls [] r     = r
      foralls (x:xs) r = Loc (location r) $ TForall x (foralls xs r) 

constraint :: Monad m => P m [TConstraint 'Parsing]
constraint =
  singleConstraint
  <|> parens (concat <$> constraint `P.sepBy` comma)

singleConstraint :: Monad m => P m [TConstraint 'Parsing]
singleConstraint = do
  m1 <- multiplicity 
  maxConstraint m1 <|> subConstraint m1 
    where
      maxConstraint m1 = do
        void symbolTyEq
        m2 <- multiplicity
        void symbolMult
        m3 <- multiplicity
        return [MEqMax m1 m2 m3]

      subConstraint m1 = do
        void symbolTyLE
        m2 <- multiplicity
        return [MSub m1 m2] 

      -- TODO: move them to Helper.hs with appropriate naming. 
      symbolTyLE = symbol "<=" <|> symbol "≦"
      symbolTyEq = symbol "~" <|> symbol "≡"
      symbolMult = symbol "*" <|> symbol "↑"


arrTy :: Monad m => P m (LTy 'Parsing)
arrTy =
  -- Essentially, this implements foldr by foldl. 
  (\t fs -> foldl (.) (\c -> c t) fs id)
  <$> appTy <*> P.many ((\f x c z -> f z (c x)) <$> arr <*> appTy)
  where
    mkArr m e1 e2 = Loc (location e1 <> location e2) $ TCon (BuiltIn nameTyArr) [m, e1, e2] 
    arr = 
      (do void rightArrow
          pure $ \e1 e2 -> mkArr (noLoc $ TMult Omega) e1 e2)
      <|>
      (do void lollipop 
          pure $ \e1 e2 -> mkArr (noLoc $ TMult One) e1 e2)
      <|>
      (do void $ symbol "#"
          m <- multiplicity
          void rightArrow
          pure $ \e1 e2 -> mkArr m e1 e2)

appTy :: Monad m => P m (LTy 'Parsing)
appTy =
  P.try conTy <|> revTy <|> simpleTy
  where
    conTy = do
      Loc l c <- loc qconName
      sp
      ts <- P.some simpleTy
      return $ Loc (l <> mconcat (map location ts)) $ TCon c ts

    revTy = loc $ do      
      void $ keyword "rev"
      ty <- simpleTy
      return $ TCon (BuiltIn nameTyRev) [ty]

simpleTy :: Monad m => P m (LTy 'Parsing)
simpleTy = getSrcLoc >>= \start -> 
  conTy start <|> varTy start <|> tupleTy
  where
    conTy start = do      
      c <- qconName
      end <- getSrcLoc
      sp
      return $ Loc (start <> end) $ TCon c []

    varTy start = do
      x <- varName
      end <- getSrcLoc
      sp      
      return $ Loc (start <> end) $ TVar x

tupleTy :: Monad m => P m (LTy 'Parsing)
tupleTy =
  mkTupleTy <$> 
  parens (typeExpr `P.sepBy` comma) 

mkTupleTy :: [LTy 'Parsing] -> LTy 'Parsing 
mkTupleTy [t] = t
mkTupleTy ts  = Loc (mconcat $ map location ts) $
                TCon (BuiltIn $ nameTyTuple $ length ts) ts   
    
multiplicity :: Monad m => P m (LTy 'Parsing)
multiplicity = loc (one <|> omega <|> var) <* sp 
  where
    one   = TMult One <$ (symbol "1" <|> symbol "One")
    omega = TMult Omega <$ (symbol "ω" <|> symbol "Omega" <|> symbol "Many")
    var   = TVar  <$> varName 


modul :: Monad m => P m (Module 'Parsing)
modul = do
  modDecl <- P.optional $ do
    void $ keyword "module" 
    m  <- L.lexeme sp moduleName
    es <- exportList
    void $ keyword "where"
    return (m, es) 
  is <- importList
  ds <- topDecls
  let (m', es') = fromMaybe (ModuleName "Main", Nothing) modDecl
  return $ Module m' es' is ds

exportList :: Monad m => P m (Maybe [Export 'Parsing])
exportList = 
  P.optional $ parens (surfaceName `P.sepEndBy` comma)


surfaceName :: Monad m => P m (Loc SurfaceName)   
surfaceName = loc (P.try qconName <|> qvarName)

importList :: Monad m => P m [Import 'Parsing]
importList = P.many singleImport

singleImport :: Monad m => P m (Import 'Parsing)
singleImport = do
  void $ keyword "import"
  Import <$> L.lexeme sp moduleName <*> impNames
  where
    impNames = P.optional (parens surfaceName `P.sepEndBy` comma)
  
topDecls :: Monad m => P m (Decls 'Parsing (Loc (TopDecl 'Parsing)))
topDecls = Decls () <$> P.many topDecl

topDecl :: Monad m => P m (Loc (TopDecl 'Parsing))
topDecl = typeDecl <|> dataDecl <|> (fmap DDecl <$> localDecl)
  where
    tyLHS = do
      c <- L.lexeme sp conName
      xs <- P.many (L.lexeme sp varName)
      void $ symbol "=" 
      return (c, xs) 
    
    dataDecl = loc $ do
      void $ keyword "data"
      (c, xs) <- tyLHS 
      DData c xs <$> cdecl `P.sepBy1` symbol "|"

    typeDecl = loc $ do
      void $ keyword "type"
      (c, xs) <- tyLHS 
      DType c xs <$> typeExpr

    cdecl = do
      start <- getSrcLoc 
      c  <- conName <* sp
      ts <- P.many simpleTy
      return $ Loc (start <> mconcat (map location ts)) $ CDecl c ts

localDecls :: Monad m => P m (Decls 'Parsing (LDecl 'Parsing))
localDecls = Decls () <$> P.many localDecl 

localDecl :: Monad m => P m (LDecl 'Parsing) 
localDecl = defDecl <|> sigDecl <|> fixityDecl

defDecl :: Monad m => P m (LDecl 'Parsing) 
defDecl = do
  start <- getSrcLoc
  void $ keyword "def"
  x <- varOpName
  sp
  ds <- defBody `P.sepBy1` symbol "|"
  return $ Loc (start <> compLoc ds) $ DDef x ds
    where
      compLoc = foldr (\(ps, c) r -> mconcat [ location p | p <- ps ]
                                     <> locationClause c <> r ) mempty
      locationClause (Clause e ws e') =
        location e <> locationDecls ws <> maybe mempty location e'

      locationDecls (Decls _ ds)   = mconcat $ map location ds
      locationDecls (HDecls _ dss) = mconcat $ map (mconcat . map location) dss 
  
defBody :: Monad m => P m ([LPat 'Parsing], Clause 'Parsing)
defBody = do
  ps <- P.many simplePat
  void $ symbol "="
  c <- clause
  return (ps, c) 

sigDecl :: Monad m => P m (LDecl 'Parsing)
sigDecl = do
  start <- getSrcLoc
  void $ keyword "sig" 
  x <- varOpName
  sp
  void $ symbol ":" 
  t <- introForAll <$> typeExpr
  return (Loc (start <> location t) $ DSig x t)

fixityDecl :: Monad m => P m (LDecl 'Parsing)
fixityDecl = do
  start <- getSrcLoc
  void $ keyword "fixity" 
  o <- op <* sp 
  n <- L.decimal <* sp 
  a <- fromMaybe N <$> P.optional assoc
  end <- getSrcLoc 
  return $ Loc (start <> end) $ DFixity o (Prec n) a
  where
    assoc =
      (keyword "left" >> return L)
      <|>
      (keyword "right" >> return R)
      


opExpr :: Monad m => P m (LExp 'Parsing)
opExpr =
  foldl (\a f -> f a)  <$> 
  appExpr <*> P.many ((\o e2 e1 -> lop o e1 e2) <$> (qop <* sp) <*> appExpr)
  where
    lop o e1 e2 = Loc (location e1 <> location e2) $ Op o e1 e2 
      

appExpr :: Monad m => P m (LExp 'Parsing) 
appExpr =
  (\(f:fs) -> foldl lapp f fs) <$> P.some (withLoc simpleExpr)


lapp :: Loc (Exp p) -> Loc (Exp p) -> Loc (Exp p)
lapp e1 e2 = Loc (location e1 <> location e2) $ App e1 e2

simpleExpr :: Monad m => SrcSpan -> P m (LExp 'Parsing)
simpleExpr startLoc =
  literal 
  <|> pinExpr 
  <|> liftExpr 
  <|> unliftExpr
  <|> P.try rconExpr
  <|> conExpr
  <|> varExpr
  <|> tupleExpr 
  where
    withEnd t = do
      endLoc <- getSrcLoc
      return $ Loc (startLoc <> endLoc) t 

    withEndSp t = do
      endLoc <- getSrcLoc
      sp
      return $ Loc (startLoc <> endLoc) t
    
    pinExpr = do
      void $ keyword "pin"
      withEnd RPin

    liftExpr = do
      void $ keyword "lift"
      withEnd Lift

    unliftExpr = do
      void $ keyword "unlift"
      withEnd Unlift

    conExpr = do
      c <- qconName
      withEndSp $ Con c

    rconExpr = do
      void $ keyword "rev"
      c <- qconName
      withEndSp $ RCon c

    varExpr = do
      x <- qvarOpName
      withEndSp $ Var x

tupleExpr :: Monad m => P m (LExp 'Parsing)
tupleExpr = do
  p  <- P.optional (keyword "rev")
  es <- parens (expr `P.sepBy` comma)
  case p of
    Just _  -> pure $ mkTupleExpR es
    Nothing -> pure $ mkTupleExp  es
    


mkTuplePat :: [Loc (Pat 'Parsing)] -> Loc (Pat 'Parsing)
mkTuplePat [p] = p
mkTuplePat ps  = Loc (mconcat $ map location ps) $
                 PCon (BuiltIn $ nameTuple $ length ps) ps 

  
mkTupleExp :: [Loc (Exp 'Parsing)] -> Loc (Exp 'Parsing)
mkTupleExp [e] = Loc (location e) $ Parens e
mkTupleExp es =
  foldl lapp (noLoc $ Con $ BuiltIn $ nameTuple (length es)) es

mkTupleExpR :: [Loc (Exp 'Parsing)] -> Loc (Exp 'Parsing)
mkTupleExpR [e] = Loc (location e) $ Parens e
mkTupleExpR es =
  foldl lapp (noLoc $ RCon $ BuiltIn $ nameTuple (length es)) es
      
    
literal :: Monad m => P m (LExp 'Parsing) 
literal = loc $ fmap Lit $ 
  intLit
  <|> charLit
  where
    -- TODO: Add rationals 
    intLit = LitInt <$> (L.decimal <* sp) 
    charLit = fmap LitChar $ do
      void $ P.char '\''
      c <- L.charLiteral
      void $ P.char '\''
      void sp 
      return c 
    
      

alternatives :: Monad m => P m [ (LPat 'Parsing, Clause 'Parsing) ]
alternatives = do
  void $ P.optional (symbol "|")
  alt `P.sepBy` symbol "|" 
  

alt :: Monad m => P m (LPat 'Parsing, Clause 'Parsing)    
alt = do
  p <- pat
  void rightArrow 
  c <- clause
  return (p, c)

clause :: Monad m => P m (Clause 'Parsing)
clause = do
  e <- expr
  w <- P.optional withExpr
  d <- whereClause
  return $ Clause e d w

withExpr :: Monad m => P m (LExp 'Parsing)
withExpr = keyword "with" >> expr 


whereClause :: Monad m => P m (Decls 'Parsing (LDecl 'Parsing))
whereClause = do 
  r <- P.optional $ do void $ keyword "where"
                       ds <- localDecls
                       void $ keyword "end"
                       return ds
  case r of
    Just ds -> return ds
    Nothing -> return $ Decls () [] 
          



