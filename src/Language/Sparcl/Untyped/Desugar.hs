module Language.Sparcl.Untyped.Desugar where

import qualified Language.Sparcl.Untyped.Syntax as S
import Language.Sparcl.SrcLoc

import Language.Sparcl.Name 
import Control.Monad.State 

import Control.Monad.Except
import Data.List (sort, group, groupBy)

import Data.Function (on) 

type LExp = Loc Exp 
data Exp 
  = Lit S.Literal
  | Var QName
  | App LExp LExp
  | Abs Name LExp
  | Con QName [LExp]
  | Bang LExp
  | Case LExp [ (LPat, LExp ) ]
  | Lift LExp LExp
  | Sig  LExp S.Typ
  | Let  [LDecl] LExp

  | RCon QName [LExp]
  | RCase LExp [ (LPat, LExp, LExp ) ]
  | RPin  LExp LExp

type LPat = Loc Pat
data Pat = PVar Name
         | PCon QName [LPat]
         | PBang LPat 

type LDecl = Loc Decl 
data Decl
  = DDef Name (Maybe S.Typ) LExp

data TopDecl
  = NormalDecl Decl
  | Fixity     QName S.Prec S.Assoc

-- Monad for desugaring 
type Desugar = StateT Int (Either [(SrcSpan, String)])

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

desugarExp (S.Sig e t) = Sig <$> desugarLExp e <*> pure t

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
  noLoc $ Con (tupleName $ length es) es

makeTupleExpR :: [LExp] -> LExp
makeTupleExpR [e] = e
makeTupleExpR es  =
  noLoc $ RCon (tupleName $ length es) es

makeTuplePat :: [LPat] -> LPat
makeTuplePat [p] = p
makeTuplePat ps =
  noLoc $ PCon (tupleName $ length ps) ps 
  
                   

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
            pes <- mapM (\(c,subs,cl) -> do
                            let p = makeTuplePat lxs
                            (eb, we) <- convertClauseR cl 
                            return (p, eb, we) ) ralts
            return $ (fillCPat cp lxs , noLoc $ RCase re0 pes)


            
            
            
            
            
              
        
        
      



desugarLDecls :: [S.LDecl] -> Desugar [LDecl]
desugarLDecls ds = do
  let defs = [ (l, n, pcs) | Loc l (S.DDef n pcs) <- ds ]
  let sigs = [ (l, n, t)   | Loc l (S.DSig n t) <- ds ]

  let defNames = [ n | (_, n, _) <- defs ]
  let sigNames = [ n | (_, n, _) <- sigs ]

  case filter (\(l,n,_) -> all (\m -> n /= m) defNames) sigs of 
    ns@(_:_) ->
      throwError [ (l, "No corresponding definition: " ++ show n) 
                 | (l, n, _ ) <- ns ]       
    [] -> mapM (desugarDef sigs) defs

desugarDef :: [ (SrcSpan, Name, S.Typ) ] -> (SrcSpan, Name, [ ([S.LPat], S.Clause) ])
              -> Desugar LDecl
desugarDef sigs (l, f, pcs) = do
  case concat $ group $ sort [ length ps | (ps, c) <- pcs ] of
    []    -> throwError [ (l, "Empty definition: " ++ show f) ]
    [len] -> do
      xs <- mapM (const newName) [1..len]
      let c = tupleName (length xs) 
      e' <- desugarExp $
            S.Case (S.makeTupleExp [noLoc $ S.Var (BName x) | x <- xs])
            [ (S.makeTuplePat ps, clause) | (ps, clause) <- pcs ]
      let body =
            foldr (\x r -> noLoc $ Abs x r) (noLoc e') xs
      sig <- case filter (\(_,n,t) -> n == f) sigs of
               []  -> return $ Nothing
               [(_,_,t)] -> return $ Just t
               res -> throwError $ [ (l, "Multiple signatures for " ++ show f)
                                   | (l,_,_) <- res ]
                           
      return $ Loc l (DDef f sig body)
    _ -> 
      throwError [ (l, "#Arguments differ for " ++ show f) ]

      
