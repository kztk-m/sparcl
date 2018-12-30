module Language.Sparcl.Untyped.Desugar where

import qualified Language.Sparcl.Untyped.Syntax as S
import Language.Sparcl.SrcLoc

import Language.Sparcl.Name
import Language.Sparcl.Pretty 
import Language.Sparcl.Untyped.Desugar.Syntax

import Control.Monad.State 
import Control.Monad.Reader
import Control.Monad.Except
import qualified Control.Monad.Fail as Fail 

import qualified Data.Map as M

import Data.List (sort, group, groupBy, nub)

import Data.Function (on) 

-- Monad for desugaring 
type Desugar = ReaderT NameInfo (StateT Int (Either [(SrcSpan, String)]))


desugarTest :: NameInfo -> Desugar a -> IO a
desugarTest ni d =
  case evalStateT (runReaderT d ni) 0 of
    Left ls ->
      Fail.fail $ unlines [ show l ++ ": " ++ s | (l,s) <- ls ]
    Right v -> return v 

defaultNameInfo :: NameInfo 
defaultNameInfo =
  let tbl = M.fromList [
        base "+" |-> (S.Prec 60, S.L),
        base "-" |-> (S.Prec 60, S.L), 
        base "*" |-> (S.Prec 70, S.L),
        base "/" |-> (S.Prec 70, S.L)
        ]
  in NameInfo {
    niDefinedNames  = [ nameTyArr, nameTyBang,
                        nameTyChar, nameTyDouble, nameTyInt,
                        nameTyList, nameTyRev, conTrue, conFalse ] ++ M.keys tbl ,
    niCurrentModule = ["Main"],
    niOpTable = tbl
    }
  where
    a |-> b = (a, b) 
    base s = QName baseModule (NormalName s) 



data NameInfo = NameInfo { niDefinedNames  :: [QName],
                           niCurrentModule :: ModuleName,
                           niOpTable       :: M.Map QName (S.Prec, S.Assoc) }

withName :: Name -> Desugar a -> Desugar a
withName n m = 
  local (\ni -> ni { niDefinedNames = BName n : niDefinedNames ni }) m 

withNames :: [Name] -> Desugar a -> Desugar a
withNames ns m = foldr withName m ns 

withOpEntry :: Name -> (S.Prec, S.Assoc) -> Desugar a -> Desugar a
withOpEntry n (k,a) m =
  local (\ni -> ni { niOpTable = M.insert (BName n) (k, a) $ niOpTable ni }) m

withOpEntries :: [ (Name, (S.Prec, S.Assoc)) ] -> Desugar a -> Desugar a
withOpEntries ns m = foldr (uncurry withOpEntry) m ns 

getCurrentModule :: Desugar ModuleName
getCurrentModule = asks niCurrentModule 

getOpTable :: Desugar (M.Map QName (S.Prec, S.Assoc))
getOpTable = asks niOpTable

lookupFixity :: QName -> Desugar (S.Prec, S.Assoc)
lookupFixity qname = do
  tbl <- getOpTable
  case M.lookup qname tbl of
    Just (k, a) -> return (k, a)
    Nothing     -> return (S.Prec 100, S.L)

isLeftAssoc :: (S.Prec, S.Assoc) -> (S.Prec, S.Assoc) -> Bool
isLeftAssoc (k1, a1) (k2, a2)
  | k1 >  k2 = True
  | k1 == k2, S.L <- a1, S.L <- a2 = True
  | otherwise = False

isRightAssoc :: (S.Prec, S.Assoc) -> (S.Prec, S.Assoc) -> Bool
isRightAssoc (k1, a1) (k2, a2) 
  | k1 <  k2 = True
  | k1 == k2, S.R <- a1, S.R <- a2 = True
  | otherwise = False 
      
             
refineName :: SrcSpan -> QName -> Desugar QName
refineName _ (QName m n) = do
  cm <- getCurrentModule
  if m == cm
    then return (BName n)   -- Names in the current module should not be qualified 
    else return (QName m n)
refineName l (BName n) = do
  ns <- asks niDefinedNames
  cm <- getCurrentModule
  let res = checkNames cm n ns
  case filter (/=cm) res of
    [m]  -> return (QName m n)
    []   -> return (BName n)
    _    -> throwError [ (l, "Ambiguous name `" ++ show n ++ "' " ++ show (nub res))]
  where
    checkNames :: ModuleName -> Name -> [QName] -> [ModuleName]
    checkNames _cm _n [] = []
    checkNames cm n (BName n' : ns) =
      if n == n' then cm : checkNames cm n ns else checkNames cm n ns
    checkNames cm n (QName m n' : ns) =
      if n == n' then m : checkNames cm n ns else checkNames cm n ns 
 
 

-- canonizeNameTy :: S.LTy -> Desugar S.LTy
-- canonizeNameTy (Loc l (S.TVar q)) = return $ Loc l (S.TVar q)
-- canonizeNameTy (Loc l (S.TCon n ts)) = do 
--   n' <- refineName l n 
--   Loc l . S.TCon n' <$> mapM canonizeNameTy ts
-- canonizeNameTy (Loc l (S.TForall n t)) = do
--   Loc l . S.TForall n <$> canonizeNameTy t

-- canonizeNameExp :: S.LExp -> Desugar S.LExp
-- canonizeNameExp (Loc l exp) = Loc l <$> case exp of
--   S.Var x -> do
--     x' <- refineName l x
--     return $ S.Var x'

--   S.Lit l -> return $ S.Lit l

--   S.App e1 e2 ->
--     S.App <$> canonizeNameExp e1 <*> canonizeNameExp e2

--   S.Abs ps e -> do
--     ps' <- mapM canonizeNamePat ps
--     let ns = concatMap (freeVarsP . unLoc) ps'
--     e' <- withNames (map BName ns) $
--             canonizeNameExp e 
--     return $ S.Abs ps' e' 

--   S.Con c es -> do 
--     c' <- refineName l c
--     S.Con c' <$> mapM canonizeNameExp es

--   S.Bang e -> S.Bang <$> canonizeNameExp e

--   S.Case e pcs -> do
--     S.Case <$> canonizeNameExp e <*> mapM canonizePatClause pcs
--     where
--       canonizePatClause (p, c) = do
--         p' <- canonizeNamePat p
--         c' <- canonizeNameClause  c
--         return $ (p', c')

--   S.Lift e1 e2 -> do 
--     S.Lift <$> canonizeNameExp e1 <*> canonizeNameExp e2

--   S.Sig e t -> do
--     S.Sig <$> canonizeNameExp e <*> canonizeNameTy t

--   S.Let ds e -> do
--     S.Let <$> mapM canonizeNameDecl ds <*> canonizeNameExp e

--   S.Parens e ->
--     S.Parens <$> canonizeNameExp e

--   S.Op q e1 e2 -> do
--     q' <- refineName l q
--     S.Op q' <$> canonizeNameExp e1 <*> canonizeNameExp e2

--   S.Unlift e -> S.Unlift <$> canonizeNameExp e
--   S.Fwd e -> S.Fwd <$> canonizeNameExp e
--   S.Bwd e -> S.Bwd <$> canonizeNameExp e

--   S.RCon c es -> do 
--     c' <- refineName l c
--     S.RCon c' <$> mapM canonizeNameExp es
    
--   S.RPin e1 e2 -> 
--     S.RPin <$> canonizeNameExp e1 <*> canonizeNameExp e2 
      

-- freeVarsP :: S.Pat -> [ Name ]
-- freeVarsP (S.PVar n) = [n]
-- freeVarsP (S.PCon _ ps) =
--   concatMap (freeVarsP . unLoc) ps
-- freeVarsP (S.PBang p) = freeVarsP $ unLoc p
-- freeVarsP (S.PREV p)  = freeVarsP $ unLoc p
-- freeVarsP S.PWild     = [] 

-- canonizeNamePat :: S.LPat -> Desugar S.LPat
-- canonizeNamePat (Loc l p) = Loc l <$> case p of
--   S.PVar n -> return $ S.PVar n
--   S.PCon c ps -> do 
--     c' <- refineName l c
--     S.PCon c' <$> mapM canonizeNamePat ps
--   S.PBang p -> S.PBang <$> canonizeNamePat p
--   S.PREV  p -> S.PREV  <$> canonizeNamePat p
--   S.PWild   -> return S.PWild 
    
-- canonizeNameClause :: S.Clause -> Desugar S.Clause
-- canonizeNameClause (S.Clause e ds e') =
--   S.Clause <$> canonizeNameExp e <*> mapM canonizeNameDecl ds <*> traverse canonizeNameExp e'

-- canonizeNameDecls :: [ S.LDecl ] -> Desugar ([ S.LDecl ], [Name])
-- canonizeNameDecls ds = do
--   ds' <- mapM canonizeNameDecl ds
--   let ns = [ n | Loc _ (S.DDef n _) <- ds ]
--   return (ds', ns) 

-- canonizeNameDecl :: S.LDecl -> Desugar S.LDecl
-- canonizeNameDecl (Loc l d) = fmap (Loc l) $ case d of
--   S.DDef n pscs ->
--     S.DDef n <$> mapM f pscs
--     where
--       f (ps, c) = do
--         ps' <- mapM canonizeNamePat ps
--         c'  <- canonizeNameClause c
--         return (ps', c')
--   S.DSig n t ->
--     S.DSig n <$> canonizeNameTy t

--   S.DFixity n p a ->
--     return $ S.DFixity n p a 
  
  
 
  


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



newName :: Desugar Name
newName = do
  i <- get
  put $! i + 1
  return $ Generated i 

newQName :: Desugar QName
newQName = BName <$> newName

desugarLExp :: S.LExp -> Desugar LExp
desugarLExp (Loc l e) = Loc l <$> desugarExp l e

desugarExp :: SrcSpan -> S.Exp -> Desugar Exp
desugarExp _ (S.Lit l) = return $ Lit l
desugarExp l (S.Var n) = do
  n' <- refineName l n
  return $ Var n' 
desugarExp _ (S.App e1 e2) =
  liftM2 App (desugarLExp e1) (desugarLExp e2)
desugarExp l (S.Abs ps e) = do
  xs <- mapM (const newName) ps
  e' <- desugarExp l $
          S.Case (S.makeTupleExp [noLoc $ S.Var (BName x) | x <- xs])
          [ (S.makeTuplePat ps, S.Clause e [] Nothing) ]     
  return $ unLoc $ foldr (\n r -> noLoc (Abs n r)) (noLoc e') xs

desugarExp l (S.Con c es) = do
  c' <- refineName l c 
  Con c' <$> mapM desugarLExp es

desugarExp _ (S.Bang e) =
  Bang <$> desugarLExp e

desugarExp _ (S.Case e cs) = desugarCaseExp e cs
desugarExp _ (S.Lift e1 e2) =
  Lift <$> desugarLExp e1 <*> desugarLExp e2

desugarExp _ (S.Unlift e) =
  Unlift <$> desugarLExp e 

desugarExp l (S.Fwd e) = do 
  let c = nameTuple 2
  x <- newName
  y <- newName
  e' <- desugarExp l (S.Unlift e) 
  return $ Case (noLoc e')
    [ (noLoc $ PCon c [noLoc $ PVar x, noLoc $ PVar y],
       noLoc $ Var (BName x)) ] 

desugarExp l (S.Bwd e) = do 
  let c = nameTuple 2
  x <- newName
  y <- newName
  e' <- desugarExp l (S.Unlift e) 
  return $ Case (noLoc e')
    [ (noLoc $ PCon c [noLoc $ PVar x, noLoc $ PVar y],
       noLoc $ Var (BName y)) ] 

desugarExp _ (S.Sig e t) = Sig <$> desugarLExp e <*> pure (desugarTy $ unLoc t) 

desugarExp _ (S.Let [] e) = unLoc <$> desugarLExp e 
desugarExp _ (S.Let ds e) = do
  (ds', ns, ops) <- desugarLDecls ds
  withNames ns $
   withOpEntries ops $ 
     Let ds' <$> desugarLExp e

desugarExp _ (S.Parens e) = unLoc <$> desugarLExp e
desugarExp l (S.Op op e1 e2) = do
  op' <- refineName l op 
  unLoc <$> rearrangeOp l op' e1 e2 

desugarExp l (S.RCon c es) = do
  c' <- refineName l c 
  RCon c' <$> mapM desugarLExp es
  
desugarExp _ (S.RPin e1 e2) =
  RPin <$> desugarLExp e1 <*> desugarLExp e2 


-- TODO: Currently, the equivalence between pattenrs is too strong; it 
-- does not identify patterns with the different variables.
--
-- Should we alpha-rename variable so that patterns appear in the same
-- level has will be equal if they are different only in variable names.
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
separatePat S.PWild = do
  n <- newName
  return (CPBang (noLoc $ CPVar n), [])
separatePat (S.PREV p) =  do
  p' <- convertLPat p 
  return (CPHole, [ p']) 

convertLPat :: S.LPat -> Desugar LPat
convertLPat (Loc l (S.PVar n)) = return $ Loc l (PVar n)
convertLPat (Loc l (S.PCon c ps)) = do
  Loc l . PCon c <$> mapM convertLPat ps
convertLPat (Loc l (S.PBang p)) =
  Loc l . PBang <$> convertLPat p
convertLPat (Loc l S.PWild) = do
  n <- newName 
  return $ Loc l . PBang $ Loc l (PVar n)
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
  Loc (location body) <$> desugarExp (location body) (S.Let ws body)
convertClauseU (S.Clause _ _ (Just e)) =
  throwError [ (location e, "Unidirectional branch cannot have `with' expression") ]

convertClauseR :: S.Clause -> Desugar (LExp, LExp)
convertClauseR (S.Clause body ws (Just e)) = do
  body' <- Loc (location body) <$> desugarExp (location body) (S.Let ws body)
  e'    <- desugarLExp e
  return $ (body', e')
convertClauseR (S.Clause body ws Nothing) = do
  body' <- Loc (location body) <$> desugarExp (location body) (S.Let ws body)
  -- FIXME: More sophisticated with-exp generation.
  e' <- desugarLExp $ noLoc $ S.Abs [noLoc S.PWild] (noLoc $ S.Con conTrue [])
  return $ (body', e') 

  

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
            let p = fillCPat cp [] 
            e <- withNames (freeVarsP $ unLoc p) $ convertClauseU clause
            return (p, e)
        | otherwise = do
            xs <- mapM (const newName) sub
            let lxs = zipWith (\p x -> Loc (location p) $ PVar x) sub xs
            let re0 = makeTupleExpR $ map (noLoc . Var . BName) xs
            let outP = fillCPat cp lxs 
            pes <- withNames (freeVarsP $ unLoc outP) $
                   mapM (\(_,subs,cl) -> do
                            let p = makeTuplePat subs
                            (eb, we) <- withNames (freeVarsP $ unLoc p) $
                                         convertClauseR cl 
                            return (p, eb, we) ) ralts
            return $ (outP , noLoc $ RCase re0 pes)


desugarLDecls :: [S.LDecl] -> Desugar ([LDecl], [Name], [(Name, (S.Prec, S.Assoc))]) 
desugarLDecls ds = do
  let defs = [ (l, n, pcs) | Loc l (S.DDef n pcs) <- ds ]
  let sigs = [ (l, n, t)   | Loc l (S.DSig n t) <- ds ]
  let fixities = [ (n, (k,a)) | Loc _ (S.DFixity n k a) <- ds ] 
  
  let defNames = [ n | (_, n, _) <- defs ]

  case filter (\(_,n,_) -> all (\m -> n /= m) defNames) sigs of 
    ns@(_:_) ->
      throwError [ (l, "No corresponding definition: " ++ show n) 
                 | (l, n, _ ) <- ns ]       
    [] -> do 
      ds' <- withNames defNames $
              withOpEntries fixities $ 
               mapM (desugarDef sigs) defs
      return $ (ds', defNames, fixities) 

desugarDef :: [ (SrcSpan, Name, S.LTy) ] -> (SrcSpan, Name, [ ([S.LPat], S.Clause) ])
              -> Desugar LDecl
desugarDef sigs (l, f, pcs) = do
  case map unwrap $ group $ sort [ length ps | (ps, _) <- pcs ] of
    []    -> throwError [ (l, "Empty definition: " ++ show f) ]
    [len] -> do
      xs <- mapM (const newName) [1..len]
      e' <- desugarExp l $
            S.Case (S.makeTupleExp [noLoc $ S.Var (BName x) | x <- xs])
            [ (S.makeTuplePat ps, clause) | (ps, clause) <- pcs ]
      let body =
            foldr (\x r -> noLoc $ Abs x r) (noLoc e') xs
      sig <- case filter (\(_,n,_) -> n == f) sigs of
               []  -> return $ Nothing
               [(_,_,t)] -> return $ Just t
               res -> throwError $ [ (l, "Multiple signatures for " ++ show f)
                                   | (l,_,_) <- res ]

      let sig' = (desugarTy . unLoc) <$> sig 
      return $ Loc l (DDef f sig' body)
    ls -> 
      throwError [ (l, "#Arguments differ for " ++ show f ++ show ls) ]
  where
    unwrap (a:_) = a
    unwrap _     = error "Cannot happen." 



{-
Currently, the operators are parsed as if they were left-associative
and has the same precedence. Thus,

  x1 op1 x2 op2 x3 op3 ... opn xn+1

will be parsed as

  ((...((x1 op1 x2) op2 x3)...) opn xn+1)

Here we rearrange the operators in the right way.

Let us focus on op1 and op2 first. The association (x1 op1 x2) op2 x3
is right only if

  - op1 and op2 has the same precedence and op1 and op2 are
    left-associative, or 
  - op1 has the greater precedence than op2.

Instead, it should be associated as x1 op1 (x2 op2 x3) 

  - op1 and op2 has the same precedence and op1 and op2 are
    right-associative, or 
  - op2 has the greater precedence than op1.

Otherwise, we need parentheses; that is, there is a syntax error.

In the former case, it is rather straight forward to proceed the 

-}

rearrangeOp :: SrcSpan -> QName -> S.LExp -> S.LExp -> Desugar LExp
rearrangeOp l1 op e1 e2 = do
  e2' <- desugarLExp e2
  go l1 e1 op e2'
    where
      go l2 (Loc l1 (S.Op op1 e1 e2)) op2' e3' = do
        op1' <- refineName l1 op1
        (k1, a1) <- lookupFixity op1' 
        (k2, a2) <- lookupFixity op2'
        if | isLeftAssoc (k1, a1) (k2, a2) -> do
               e2' <- desugarLExp e2
               e12' <- go l1 e1 op1' e2'
               return $ opExp l2 op2' e12' e3'
           | isRightAssoc (k1, a1) (k2, a2) -> do
               e1'  <- desugarLExp e2
               e23' <- go l2 e2 op2' e3'
               return $ opExp l1 op1' e1' e23'
           | otherwise ->
               throwError [ (l1, "Parens are needed between: _ " ++ prettyShow op1' ++ " _ " ++ prettyShow op2' ++ " _.") ]
      go l e1 op' e2' = do
        e1' <- desugarLExp e1
        return $ opExp l op' e1' e2' 

opExp :: SrcSpan -> QName -> LExp -> LExp -> LExp 
opExp l opName exp1 exp2 =
  foldl (\r a -> lapp r a) (Loc l $ Var opName) [exp1, exp2] 
  where
    lapp e1 e2 = Loc (location e1 <> location e2) (App e1 e2) 
               
        
