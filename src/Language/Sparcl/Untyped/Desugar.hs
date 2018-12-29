module Language.Sparcl.Untyped.Desugar where

import qualified Language.Sparcl.Untyped.Syntax as S
import Language.Sparcl.SrcLoc

import Language.Sparcl.Name
import Language.Sparcl.Literal

import Control.Monad.State 

import Control.Monad.Except
import qualified Control.Monad.Fail as Fail

import Data.List (sort, group, groupBy)

import Data.Function (on) 

import Language.Sparcl.Pretty 
import qualified Text.PrettyPrint.ANSI.Leijen as D


data Ty = TyCon   QName [Ty]     -- ^ Type constructor 
        | TyVar   Name           -- ^ Type variable         
        | TyMetaV MetaTyVar      -- ^ Metavariables (to be substituted in type inf.) 
        | TyForAll [Name] BodyTy -- ^ polymorphic types 
        | TySyn   Ty Ty          -- ^ type synonym (@TySym o u@ means @u@ but @o@ will be used for error messages) 
         deriving (Eq, Show)

instance Pretty Ty where
  pprPrec _ (TyCon c []) = ppr c
  pprPrec k (TyCon c [a,b]) | c == nameTyArr = parensIf (k > 0) $ 
    pprPrec 1 a D.</> D.text "->" D.<+> pprPrec 0 b 
  pprPrec k (TyCon c ts) = parensIf (k > 1) $
    ppr c D.<+> D.align (D.hsep (map (pprPrec 2) ts))

  pprPrec _ (TyVar x) = ppr x 

  pprPrec _ (TyMetaV m) = ppr m
  pprPrec k (TyForAll ns t) = parensIf (k > 0) $ 
    D.text "forall" D.<+>
      D.hsep (map ppr ns) D.<> D.text "."
      D.<+> D.align (pprPrec 0 t)

  pprPrec k (TySyn t _) = pprPrec k t 

data MetaTyVar = MetaTyVar Int SrcSpan
  deriving Show

instance Pretty MetaTyVar where
  ppr (MetaTyVar i _) = D.text $ "_" ++ show i 

instance Eq MetaTyVar where
  MetaTyVar i _ == MetaTyVar j _ = i == j 

type BodyTy = MonoTy  -- forall body. only consider rank 1
type PolyTy = Ty      -- polymorphic types
type MonoTy = Ty      -- monomorphic types

desugarTy :: S.Ty -> Ty
desugarTy (S.TVar q)    = TyVar q
desugarTy (S.TCon n ts) =
  TyCon n $ map (desugarTy . unLoc) ts
desugarTy (S.TForall n t) = 
  let (ns, t') = unForall $ unLoc t
  in TyForAll (n:ns) $ desugarTy t'
  where
    unForall :: S.Ty -> ([Name], S.Ty)
    unForall = go []
    go ns (S.TForall n' t') =
      go (n':ns) (unLoc t') 
    go ns t = (reverse ns, t) 



type LExp = Loc Exp 
data Exp 
  = Lit Literal
  | Var QName
  | App LExp LExp
  | Abs Name LExp
  | Con QName [LExp]
  | Bang LExp
  | Case LExp [ (LPat, LExp ) ]
  | Lift LExp LExp
  | Sig  LExp Ty
  | Let  [LDecl] LExp

  | RCon QName [LExp]
  | RCase LExp [ (LPat, LExp, LExp ) ]
  | RPin  LExp LExp
  deriving Show 

instance Pretty (Loc Exp) where
  pprPrec k = pprPrec k . unLoc

instance Pretty Exp where
  pprPrec _ (Lit l) = ppr l
  pprPrec _ (Var q) = ppr q
  pprPrec k (App e1 e2) = parensIf (k > 9) $
    pprPrec 9 e1 D.<+> pprPrec 10 e2
  pprPrec k (Abs x e) = parensIf (k > 0) $
    D.text "\\" D.<> ppr x D.<+> D.text "->" D.<+> D.align (D.nest 2 (pprPrec 0 e))

  pprPrec _ (Con c []) =
    ppr c 

  pprPrec k (Con c es) = parensIf (k > 9) $
    ppr c D.<+> D.hsep (map (pprPrec 10) es)

  pprPrec _ (Bang e) =
    D.text "!" D.<> pprPrec 10 e

  pprPrec k (Case e ps) = parensIf (k > 0) $ 
    D.text "case" D.<+> pprPrec 0 e D.<+> D.text "of" D.</>
    D.semiBraces (map pprPs ps)
    where
      pprPs (p, c) = D.align $ pprPrec 1 p D.<+> D.text "->" D.<+> (D.nest 2 $ ppr c)

  pprPrec k (Lift e1 e2) = parensIf (k > 9) $
    D.text "lift" D.<+> D.align (pprPrec 10 e1 D.</> pprPrec 10 e2)

  pprPrec k (Sig e t) = parensIf (k > 0) $
    pprPrec 0 e D.<+> D.colon D.<+> ppr t

  pprPrec k (Let ds e) = parensIf (k > 0) $
    D.align $
     D.text "let" D.<+> D.align (D.semiBraces $ map ppr ds) D.</>
     D.text "in" D.<+> pprPrec 0 e

  pprPrec k (RCon c es) = parensIf (k > 9) $
    D.text "rev" D.<+> ppr c D.<+>
     D.hsep (map (pprPrec 10) es)

  pprPrec k (RCase e ps) = parensIf (k > 0) $ 
    D.text "case" D.<+> pprPrec 0 e D.<+> D.text "of" D.</>
    D.semiBraces (map pprPs ps)
    where
      pprPs (p, c, e) = D.align $ D.text "rev" D.<+> pprPrec 1 p D.<+> D.text "->" D.<+> (D.nest 2 $ ppr c D.</> D.align (ppr e))

  pprPrec k (RPin e1 e2) = parensIf (k > 9) $
    D.text "pin" D.<+> pprPrec 10 e1 D.<+> pprPrec 10 e2 
        


type LPat = Loc Pat
data Pat = PVar Name
         | PCon QName [LPat]
         | PBang LPat
  deriving Show 

instance Pretty (Loc Pat) where
  pprPrec k = pprPrec k . unLoc 

instance Pretty Pat where
  pprPrec _ (PVar n) = ppr n

  pprPrec _ (PCon c []) = ppr c 
  pprPrec k (PCon c ps) = parensIf (k > 0) $
    ppr c D.<+> D.hsep (map (pprPrec 1) ps)
  pprPrec _ (PBang p)   =
    D.text "!" D.<+> pprPrec 1 p


type LDecl = Loc Decl 
data Decl
  = DDef Name (Maybe Ty) LExp
  deriving Show

instance Pretty Decl where
  ppr (DDef n m e) =
    D.text "def" D.<+> ppr n 
    D.<> (case m of
            Nothing -> D.empty
            Just  t -> D.space D.<> D.colon D.<+> ppr t)
    D.<+> D.text "=" D.<+> ppr e 
    
  pprList _ = D.vsep . map ppr 

instance Pretty LDecl where
  ppr (Loc l d) =
    D.text "-- " D.<+> ppr l D.<$> ppr d

  pprList _ = D.vsep . map ppr 
  

data TopDecl
  = NormalDecl Decl
  | Fixity     QName S.Prec S.Assoc


-- Monad for desugaring 
type Desugar = StateT Int (Either [(SrcSpan, String)])

desugarTest :: Desugar a -> IO a
desugarTest d =
  case evalStateT d 0 of
    Left ls ->
      Fail.fail $ unlines [ show l ++ ": " ++ s | (l,s) <- ls ]
    Right v -> return v 

newName :: Desugar Name
newName = do
  i <- get
  put $! i + 1
  return $ Generated i 

newQName :: Desugar QName
newQName = BName <$> newName

desugarLExp :: S.LExp -> Desugar LExp
desugarLExp = traverse desugarExp

desugarExp :: S.Exp -> Desugar Exp
desugarExp (S.Lit l) = return $ Lit l
desugarExp (S.Var n) = return $ Var n
desugarExp (S.App e1 e2) =
  liftM2 App (desugarLExp e1) (desugarLExp e2)
desugarExp (S.Abs ps e) = do
  xs <- mapM (const newName) ps
  e' <- desugarExp $
          S.Case (S.makeTupleExp [noLoc $ S.Var (BName x) | x <- xs])
          [ (S.makeTuplePat ps, S.Clause e [] Nothing) ]     
  return $ unLoc $ foldr (\n r -> noLoc (Abs n r)) (noLoc e') xs

desugarExp (S.Con c es) = 
  Con c <$> mapM desugarLExp es

desugarExp (S.Bang e) =
  Bang <$> desugarLExp e

desugarExp (S.Case e cs) = desugarCaseExp e cs
desugarExp (S.Lift e1 e2) =
  Lift <$> desugarLExp e1 <*> desugarLExp e2

desugarExp (S.Sig e t) = Sig <$> desugarLExp e <*> pure (desugarTy $ unLoc t) 

desugarExp (S.Let [] e) = unLoc <$> desugarLExp e 
desugarExp (S.Let ds e) =
  Let <$> desugarLDecls ds <*> desugarLExp e

desugarExp (S.RCon c es) =
  RCon c <$> mapM desugarLExp es
  
desugarExp (S.RPin e1 e2) =
  RPin <$> desugarLExp e1 <*> desugarLExp e2 

data CPat = CPHole
          | CPVar  Name
          | CPCon  QName [ Loc CPat ]
          | CPBang (Loc CPat)

equivalentCPat :: CPat -> CPat -> Bool
equivalentCPat CPHole CPHole = True
equivalentCPat (CPVar n) (CPVar n') = n == n'
equivalentCPat (CPCon c ps) (CPCon c' ps') =
  c == c' && length ps == length ps'
  && and (zipWith (equivalentCPat `on` unLoc) ps ps')
equivalentCPat (CPBang p) (CPBang p') =
  (equivalentCPat `on` unLoc) p p' 
equivalentCPat _ _ = False              
  
separateLPat :: S.LPat -> Desugar (Loc CPat, [ LPat ])
separateLPat (Loc l p) = do
  (p', sub) <- separatePat p
  return (Loc l p', sub)

separatePat :: S.Pat -> Desugar (CPat, [ LPat ])
separatePat (S.PVar n) = return (CPVar n, [])
separatePat (S.PCon c ps) = do 
  (ps', subs) <- unzip <$> mapM separateLPat ps
  return (CPCon c ps', concat subs)
separatePat (S.PBang p) =  do
  (p', sub) <- separateLPat p
  return (CPBang p', sub)
separatePat (S.PREV p) =  do
  p' <- convertLPat p 
  return (CPHole, [ p']) 

convertLPat :: S.LPat -> Desugar LPat
convertLPat (Loc l (S.PVar n)) = return $ Loc l (PVar n)
convertLPat (Loc l (S.PCon c ps)) = do
  Loc l . PCon c <$> mapM convertLPat ps
convertLPat (Loc l (S.PBang p)) =
  Loc l . PBang <$> convertLPat p
convertLPat (Loc l (S.PREV _)) =
  throwError [(l, "rev patterns cannot be nested.")] 

fillCPat :: Loc CPat -> [LPat] -> LPat
fillCPat c ps = evalState (go c) ps
  where
    next :: State [LPat] LPat 
    next = do
      (p:ps) <- get
      put ps
      return p

    go :: Loc CPat -> State [LPat] LPat 
    go (Loc l (CPVar x)) = return (Loc l (PVar x))
    go (Loc l (CPCon c ps)) =
      Loc l . PCon c <$> mapM go ps
    go (Loc l (CPBang p)) =
      Loc l . PBang <$> go p
    go (Loc _ CPHole) = next 
  
      
      
  
makeTupleExp :: [LExp] -> LExp 
makeTupleExp [e] = e
makeTupleExp es  =
  noLoc $ Con (nameTuple $ length es) es

makeTupleExpR :: [LExp] -> LExp
makeTupleExpR [e] = e
makeTupleExpR es  =
  noLoc $ RCon (nameTuple $ length es) es

makeTuplePat :: [LPat] -> LPat
makeTuplePat [p] = p
makeTuplePat ps =
  noLoc $ PCon (nameTuple $ length ps) ps 
  
                   

convertClauseU :: S.Clause -> Desugar LExp
convertClauseU (S.Clause body ws Nothing) =
  Loc (location body) <$> desugarExp (S.Let ws body)
convertClauseU (S.Clause _ _ (Just e)) =
  throwError [ (location e, "Unidirectional branch cannot have `with' expression") ]

convertClauseR :: S.Clause -> Desugar (LExp, LExp)
convertClauseR (S.Clause body ws (Just e)) = do
  body' <- Loc (location body) <$> desugarExp (S.Let ws body)
  e'    <- desugarLExp e
  return $ (body', e')
convertClauseR (S.Clause body ws Nothing) = do
  body' <- Loc (location body) <$> desugarExp (S.Let ws body)
  -- FIXME: More sophisticated with-exp generation. 
  return $ (body', noLoc $ Con conTrue []) 

  

desugarCaseExp :: Loc S.Exp -> [(Loc S.Pat, S.Clause)] -> Desugar Exp
desugarCaseExp e0 alts = do
  e0' <- desugarLExp e0
  alts' <- mapM (\(p,c) -> do { (p',sub) <- separateLPat p; return (p', sub, c) }) alts
  -- grouping alts that have the same unidir patterns. 
  let altss = groupBy (equivalentCPat `on` (\(p',_,_) -> unLoc p')) alts'
  alts <- mapM makeBCases altss 
  return $ Case e0' alts 
    where
      makeBCases :: [ (Loc CPat, [LPat], S.Clause) ] -> Desugar (Loc Pat, LExp)
      makeBCases [] = error "Cannot happen." 
      makeBCases ralts@((cp,sub,clause):_)
        | [] <- sub = do 
            -- in this case, the original pattern does not have any REV.
            -- so length xs > 1 means that there are some redundant patterns.
            -- 
            -- FIXME: say warning
            e <- convertClauseU clause 
            return (fillCPat cp [], e)
        | otherwise = do
            xs <- mapM (const newName) sub
            let lxs = zipWith (\p x -> Loc (location p) $ PVar x) sub xs
            let re0 = makeTupleExpR $ map (noLoc . Var . BName) xs
            pes <- mapM (\(_,subs,cl) -> do
                            let p = makeTuplePat subs
                            (eb, we) <- convertClauseR cl 
                            return (p, eb, we) ) ralts
            return $ (fillCPat cp lxs , noLoc $ RCase re0 pes)


desugarLDecls :: [S.LDecl] -> Desugar [LDecl]
desugarLDecls ds = do
  let defs = [ (l, n, pcs) | Loc l (S.DDef n pcs) <- ds ]
  let sigs = [ (l, n, t)   | Loc l (S.DSig n t) <- ds ]

  let defNames = [ n | (_, n, _) <- defs ]

  case filter (\(_,n,_) -> all (\m -> n /= m) defNames) sigs of 
    ns@(_:_) ->
      throwError [ (l, "No corresponding definition: " ++ show n) 
                 | (l, n, _ ) <- ns ]       
    [] -> mapM (desugarDef sigs) defs

desugarDef :: [ (SrcSpan, Name, S.Ty) ] -> (SrcSpan, Name, [ ([S.LPat], S.Clause) ])
              -> Desugar LDecl
desugarDef sigs (l, f, pcs) = do
  case map unwrap $ group $ sort [ length ps | (ps, _) <- pcs ] of
    []    -> throwError [ (l, "Empty definition: " ++ show f) ]
    [len] -> do
      xs <- mapM (const newName) [1..len]
      e' <- desugarExp $
            S.Case (S.makeTupleExp [noLoc $ S.Var (BName x) | x <- xs])
            [ (S.makeTuplePat ps, clause) | (ps, clause) <- pcs ]
      let body =
            foldr (\x r -> noLoc $ Abs x r) (noLoc e') xs
      sig <- case filter (\(_,n,_) -> n == f) sigs of
               []  -> return $ Nothing
               [(_,_,t)] -> return $ Just t
               res -> throwError $ [ (l, "Multiple signatures for " ++ show f)
                                   | (l,_,_) <- res ]

      let sig' = desugarTy <$> sig 
      return $ Loc l (DDef f sig' body)
    ls -> 
      throwError [ (l, "#Arguments differ for " ++ show f ++ show ls) ]
  where
    unwrap (a:_) = a
    unwrap _     = error "Cannot happen." 
