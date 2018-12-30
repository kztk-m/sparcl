{-# LANGUAGE ViewPatterns #-}

module Language.Sparcl.Untyped.ParserAux where

import Language.Sparcl.Untyped.Lexer
import Language.Sparcl.Untyped.Syntax
import Language.Sparcl.SrcLoc 
import Language.Sparcl.Name
import Language.Sparcl.Pretty

import Data.Char as C 

qnameTk :: Token -> QName
qnameTk (TkQVarID n) = n
qnameTk (TkVarID  n) = BName n
qnameTk (TkConID  n) = n
qnameTk (TkOp     n) = n
qnameTk _            = error "..." 

nameTk :: Token -> Name
nameTk (TkVarID n) = n
nameTk _ = error "unexpected token" 

intTk :: Token -> Int
intTk (TkIntLit i) = i
intTk _            = error "unexpected token"

charTk :: Token -> Char
charTk (TkCharLit c) = c
charTk _             = error "unexpected token" 

unquantify :: QName -> Alex Name
unquantify (BName n) = return n
unquantify qn@(QName _ _) =
  lexError $ "Quantified name " ++ prettyShow qn ++ " is not allowed here." 


lop :: Loc QName -> LExp -> LExp -> LExp
lop (Loc l q) e1 e2 =
  Loc (l <> location e1 <> location e2) $ Op q e1 e2 
  
lcase :: LExp -> [ (LPat, Clause) ] -> LExp
lcase e1 pcs = Loc (location e1 <> getLoc pcs) $ Case e1 pcs
  where
    getLoc [] = mempty 
    getLoc ((p,c):pcs) =
      location p <> locationClause c <> getLoc pcs

lddef :: Name -> [ ([LPat], Clause) ] -> LDecl
lddef q pscs = Loc (getLoc pscs) $ DDef q pscs
  where
    getLoc = foldr (\(ps,c) r -> mconcat [location p | p <- ps] <> locationClause c <> r ) mempty 

    
labs :: [ LPat ] -> LExp -> LExp
labs ps e = Loc (mconcat (map location ps) <> location e) $ Abs ps e 

lpcon :: Loc QName -> [ LPat ] -> LPat
lpcon (Loc l c) ps =
  Loc (l <> mconcat (map location ps)) $ PCon c ps 

lapp :: LExp -> LExp -> LExp
lapp (Loc l (Con c es)) e = Loc (l <> location e) $ Con c (es ++ [e])
lapp (Loc l (RCon c es)) e = Loc (l <> location e) $ RCon c (es ++ [e])
lapp e1 e2 = Loc (location e1 <> location e2) $ App e1 e2 

locationClause :: Clause -> SrcSpan
locationClause (Clause e ws e') =
  location e <> locationDecls ws <> maybe mempty id (fmap location e')

locationDecls :: [LDecl] -> SrcSpan
locationDecls = mconcat . map location 
  
expandLoc :: Loc a -> Loc b -> Loc b
expandLoc (location -> l1) (Loc l2 e) = Loc (l1 <> l2) e 

mkTupleTy :: [LTy] -> LTy
mkTupleTy [t] = t
mkTupleTy ts  = Loc (mconcat $ map location ts) $
                TCon (nameTyTuple $ length ts) ts 

mkTupleExp :: [LExp] -> LExp
mkTupleExp [e] = Loc (location e) $ Parens e
mkTupleExp es = Loc (mconcat $ map location es) $
                Con (nameTuple $ length es) es

mkTuplePat :: [LPat] -> LPat
mkTuplePat [p] = p
mkTuplePat ps  = Loc (mconcat $ map location ps) $
                 PCon (nameTuple $ length ps) ps 

toModuleName :: SrcSpan -> QName -> Alex ModuleName
toModuleName _ (QName q (NormalName n))
  | all (\c -> C.isLower c && C.isUpper c) n =
    return $ q ++ [n]
toModuleName _ qn = 
    lexError $ prettyShow qn ++ " is not a valid module name."
    
  
parseError :: Loc Token -> Alex a
parseError (Loc _l TkEOF) =
  lexError $ "Parse error on the end of the input."
parseError (Loc _l tk) =
  lexError $ "Parse error near the `" ++ tokenToString tk ++ "'."

tokenToString :: Token -> String
tokenToString (TkOp s)     = "operator " ++ prettyShow s
tokenToString (TkQVarID s) = "quantified varID " ++ prettyShow s
tokenToString (TkVarID n)  = "unquantified varID " ++ prettyShow n
tokenToString (TkConID n)  = "conID " ++ prettyShow n
tokenToString (TkKey s)    = "keyword " ++ s
tokenToString (TkPunct s)  = "key symbol " ++ s 
tokenToString (TkIntLit i) = "int literal " ++ show i
tokenToString (TkCharLit c) = "char literal " ++ show c
tokenToString TkEOF         = "<EOF>"
