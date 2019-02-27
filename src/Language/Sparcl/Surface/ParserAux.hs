{-# LANGUAGE ViewPatterns #-}

module Language.Sparcl.Surface.ParserAux where

import Language.Sparcl.Surface.Lexer
import Language.Sparcl.Surface.Syntax
import Language.Sparcl.SrcLoc 
import Language.Sparcl.Name
import Language.Sparcl.Pretty
import Language.Sparcl.Pass

import Data.Char as C 

type ExpP = Exp 'Parsing
type LExpP = LExp 'Parsing
type PatP = Pat 'Parsing
type LPatP = LPat 'Parsing
type ClauseP = Clause 'Parsing
type LDeclP = LDecl 'Parsing 
type TyP = Ty 'Parsing
type LTyP = LTy 'Parsing
type DeclsP = Decls 'Parsing
type CDeclP = CDecl 'Parsing
type TopDeclP = TopDecl 'Parsing
type ImportP = Import 'Parsing

qnameTk :: Token -> SurfaceName
qnameTk (Tvarid  n)   = Bare n
qnameTk (Tconid  n)   = Bare n
qnameTk (Top     n)   = Bare n
qnameTk (Tqvarid q n) = Qual q n
qnameTk (Tqconid q n) = Qual q n
qnameTk (Tqop    q n) = Qual q n 
qnameTk _            = error "Cannot happen."

intTk :: Token -> Int
intTk (Tintlit i) = i
intTk _           = error "Cannot happen."

charTk :: Token -> Char
charTk (Tcharlit c) = c
charTk _            = error "Cannot happen."

-- unquantify :: QName -> Alex Name
-- unquantify (BName n) = return n
-- unquantify qn@(QName _ _) =
--   lexError $ "Quantified name " ++ prettyShow qn ++ " is not allowed here." 


lop :: Loc SurfaceName -> LExpP -> LExpP -> LExpP
lop (Loc l q) e1 e2 =
  Loc (l <> location e1 <> location e2) $ Op q e1 e2 
  
lcase :: LExpP -> [ (LPatP, ClauseP) ] -> LExpP
lcase e1 alts = Loc (location e1 <> getLoc alts) $ Case e1 alts
  where
    getLoc [] = mempty 
    getLoc ((p,c):pcs) =
      location p <> locationClause c <> getLoc pcs

lddef :: SurfaceName -> [ ([LPatP], ClauseP) ] -> LDeclP 
lddef q pscs = Loc (getLoc pscs) $ DDef q pscs
  where
    getLoc = foldr (\(ps,c) r -> mconcat [location p | p <- ps] <> locationClause c <> r ) mempty 

    
labs :: [ LPatP ] -> LExpP -> LExpP
labs ps e = Loc (mconcat (map location ps) <> location e) $ Abs ps e 

lpcon :: Loc SurfaceName -> [ LPatP ] -> LPatP
lpcon (Loc l c) ps =
  Loc (l <> mconcat (map location ps)) $ PCon c ps 

lapp :: LExpP -> LExpP -> LExpP
-- lapp (Loc l (Con c es)) e = Loc (l <> location e) $ Con c (es ++ [e])
-- lapp (Loc l (RCon c es)) e = Loc (l <> location e) $ RCon c (es ++ [e])
lapp e1 e2 = Loc (location e1 <> location e2) $ App e1 e2 

locationClause :: ClauseP -> SrcSpan
locationClause (Clause e ws e') =
  location e <> locationDecls ws <> maybe mempty id (fmap location e')

locationDecls :: DeclsP LDeclP -> SrcSpan
locationDecls (Decls _ ds)   = mconcat $ map location ds
locationDecls (HDecls _ dss) = mconcat $ map (mconcat . map location) dss 
  
expandLoc :: Loc a -> Loc b -> Loc b
expandLoc (location -> l1) (Loc l2 e) = Loc (l1 <> l2) e 

mkTupleTy :: [LTyP] -> LTyP
mkTupleTy [t] = t
mkTupleTy ts  = Loc (mconcat $ map location ts) $
                TCon (BuiltIn $ nameTyTuple $ length ts) ts 

mkTupleExp :: [LExpP] -> LExpP
mkTupleExp [e] = Loc (location e) $ Parens e
mkTupleExp es =
  foldl lapp (noLoc $ Con $ BuiltIn $ nameTuple (length es)) es

mkTupleExpR :: [LExpP] -> LExpP
mkTupleExpR [e] = Loc (location e) $ Parens e
mkTupleExpR es =
  foldl lapp (noLoc $ RCon $ BuiltIn $ nameTuple (length es)) es
  
mkTuplePat :: [LPatP] -> LPatP
mkTuplePat [p] = p
mkTuplePat ps  = Loc (mconcat $ map location ps) $
                 PCon (BuiltIn $ nameTuple $ length ps) ps 

toModuleName :: SrcSpan -> SurfaceName -> Alex ModuleName
toModuleName _ (Qual (ModuleName q) (User n))
  | all (\c -> C.isLower c || C.isUpper c) n =
    return $ ModuleName (q ++ "." ++ n)
toModuleName _ qn = 
    lexError $ prettyShow qn ++ " is not a valid module name."
    
  
parseError :: Loc Token -> Alex a
parseError (Loc _l Teof) =
  lexError $ "Parse error on the end of the input."
parseError (Loc _l _tk) =
  lexError $ "Parse error" --  near the `" ++ tokenToString tk ++ "'."

-- tokenToString :: Token -> String
-- tokenToString (Top s)     = "operator " ++ prettyShow s
-- tokenToString (Tqop q s)  = "operator " ++ prettyShow q ++ "." ++ prettyShow n 
-- tokenToString (Tvarid n)  = "varID " ++ prettyShow n
-- tokenToString (Tconid n)  = "conID " ++ prettyShow n
-- tokenToString (Tqconid q n) = "conID " ++ prettyShow q ++ "." ++ prettyShow n                             
-- tokenToString (Tintlit i) = "int literal " ++ show i
-- tokenToString (Tcharlit c) = "char literal " ++ show c
-- tokenToString Teof         = "<EOF>"
