{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE ViewPatterns #-}
module Language.Sparcl.Desugar (
  desugarExp, desugarTopDecls, 
  runDesugar
  ) where

import Data.List     (groupBy)
import Data.Function (on) 
import Data.Void 

import Control.Monad.Reader
import Control.Monad.State

import qualified Language.Sparcl.Surface.Syntax as S
import Language.Sparcl.SrcLoc

import Language.Sparcl.Name

import qualified Language.Sparcl.Core.Syntax as C
-- import Language.Sparcl.Typing.Type 
import Language.Sparcl.Typing.TC
import qualified Language.Sparcl.Typing.Type as T 
import Language.Sparcl.Pass

-- import Language.Sparcl.Pretty hiding ((<$>))
-- import Debug.Trace


-- Desugaring may refer to types, so it will use type checking monad. 
type NameSource = Int 
type Desugar m a = MonadTypeCheck m => ReaderT NameSource m a 

type MonadDesugar m = (MonadReader Int m, MonadTypeCheck m)

withNewName :: MonadDesugar m => (Name -> m r) -> m r
withNewName k = do
  i <- ask
  local (+1) (k (Generated i))

withNewNames :: MonadDesugar m => Int -> ([Name] -> m r) -> m r
withNewNames n k = do
  i <- ask
  local (+ n) (k $ map Generated [i..i+n-1])
  
runDesugar :: MonadTypeCheck m => Desugar m a -> m a
runDesugar m = runReaderT m 0 

numberOfArgs :: T.Ty -> Int
numberOfArgs (_ T.:-@ t) = numberOfArgs t + 1
numberOfArgs _           = 0 

desugarExp :: forall m. MonadDesugar m => S.LExp 'TypeCheck -> m (C.Exp Name) 
desugarExp (Loc _ expr) = go expr
  where
    go :: S.Exp 'TypeCheck -> m (C.Exp Name) 
    go (S.Var (x, _)) = return $ C.Var x
    go (S.Lit l)      = return $ C.Lit l
    go (S.App e1 e2)  = do
      mkApp <$> desugarExp e1 <*> desugarExp e2 

    go (S.Abs [] e) = desugarExp e 
    go (S.Abs (p:ps) e) = withNewName $ \n -> do
      r <- desugarAlts [(p, S.Clause (noLoc $ S.Abs ps e) (S.HDecls () []) Nothing)]
      return $ mkAbs n (makeCase (C.Var n) r)

    go (S.Con (c, ty)) = do
      ty' <- zonkType ty
      let n = numberOfArgs ty'
      withNewNames n $ \xs -> do 
        let b = C.Con c [ C.Var x | x <- xs ]
        return $ foldr C.Abs b xs 
    -- go (S.Con (c,_ty) es) =
    --   C.Con c <$> mapM desugarExp es

    go (S.Bang e) =
      C.Bang <$> desugarExp e

    go (S.Case e alts) = do
      e' <- desugarExp e
      rs' <- desugarAlts alts
      return (C.Case e' rs')

    go S.Lift = 
      withNewNames 2 $ \[x, y] -> 
      return $ foldr C.Abs (C.Lift (C.Var x) (C.Var y)) [x,y] 
      
    go (S.Sig e _) = desugarExp e

    go (S.Let (S.Decls v _) _) = absurd v
    go (S.Let (S.HDecls xinfo bss) e) =
      case bss of
        [] -> desugarExp e
        bs:rest -> do 
          e' <- go (S.Let (S.HDecls xinfo rest) e)
          bs' <- mapM (\(Loc _ (S.DDef (n,_) pcs)) -> do
                          r <- desugarRHS pcs
                          return (n, r)) bs 
          return $ C.Let bs' e'            

    go (S.Parens e) = desugarExp e
    
    go (S.Op (op, _ty) e1 e2) = do 
      e1' <- desugarExp e1
      e2' <- desugarExp e2
      return $ C.App (C.App (C.Var op) e1') e2' 
    
    go S.Unlift =
      withNewName $ \x ->
      return $ C.Abs x (C.Unlift (C.Var x))

    go S.RPin =
      withNewName $ \x -> withNewName $ \y -> 
      return $ C.Abs x $ C.Abs y $ C.RPin (C.Var x) (C.Var y)

    -- FIXME: make fully-applied by using ty
    go (S.RCon (c, ty)) = do
      ty' <- zonkType ty
      let n = numberOfArgs ty'
      withNewNames n $ \xs -> do 
        let b = C.RCon c [ C.Var x | x <- xs ]
        return $ foldr C.Abs b xs 
      
makeTupleExpC :: [C.Exp Name] -> C.Exp Name
makeTupleExpC [e] = e
makeTupleExpC es  = C.Con (nameTuple (length es)) es

makeTuplePatS :: [S.LPat 'TypeCheck] -> S.LPat 'TypeCheck
makeTuplePatS [p] = p
makeTuplePatS ps  = noLoc (S.PCon (nameTuple len, tupleConTy len) ps)
  where
    len = length ps 

makeTuplePatC :: [C.Pat Name] -> C.Pat Name
makeTuplePatC [p] = p
makeTuplePatC ps  = C.PCon (nameTuple (length ps)) ps 

makeCase :: Eq n => C.Exp n -> [(C.Pat n, C.Exp n)] -> C.Exp n
makeCase (C.Con n []) [(C.PCon m [], e)] | n == m = e
makeCase e0 [(C.PVar x, e)] = mkApp (mkAbs x e) e0 
makeCase e0 alts = C.Case e0 alts 
  

-- Removes apparent eta-redex.
-- This is correct as Abs binds linear variable. So, occurence of x in "\x -> e x" means that
-- there is not free occurrence x in e. 
mkAbs :: Eq n => n -> C.Exp n -> C.Exp n
mkAbs n (C.App e (C.Var m)) | n == m = e
mkAbs n e                    = C.Abs n e 

mkApp :: Eq n => C.Exp n -> C.Exp n -> C.Exp n
mkApp (C.Abs n e) e1 = subst n e1 e
mkApp e1 e2          = C.App e1 e2

data CheckSubst a = Substituted a
                  | Untouched   a
                  deriving Functor


runCheckSubst :: CheckSubst a -> a
runCheckSubst (Substituted a)  = a
runCheckSubst (Untouched a) = a

-- subst n e e1 = Left  e1' means that e1 does not contain n (and e1' = e1) 
-- subst n e e1 = Right e1' means that e1 contains n (no futher substitution is needed)
subst :: Eq n => n -> C.Exp n -> C.Exp n -> C.Exp n
subst n t = runCheckSubst . go
  where
    go (C.Var x) | n == x    = Substituted t
                 | otherwise = Untouched (C.Var x)
    go (C.Lit l) = Untouched (C.Lit l)
    go (C.App e1 e2) =
      case go e1 of
        Substituted e1' -> Substituted (C.App e1' e2)
        Untouched   e1' -> C.App e1' <$> go e2

    go (C.Abs x e) | x == n    = Untouched (C.Abs x e)
                   | otherwise = C.Abs x <$> go e  

    go (C.Con c es) =
      C.Con c <$> gos es
    
    go (C.Bang e) = C.Bang <$> go e
    go (C.Case e0 alts) =
      case go e0 of
        Substituted e0' -> Substituted $ C.Case e0' alts
        Untouched e0'   -> C.Case e0' <$> goAlts alts

    go (C.Let bind e) =
      case goBind bind of
        Substituted bind' -> Substituted (C.Let bind' e) 
        Untouched bind'   -> C.Let bind' <$> go e

    go (C.Lift e1 e2) =
      uncurry C.Lift <$> goPair e1 e2 

    go (C.Unlift e) = C.Unlift <$> go e

    go (C.RCon c es) = C.RCon c <$> gos es
    
    go (C.RCase e ralts) = case go e of
      Substituted e' -> Substituted (C.RCase e' ralts)
      Untouched   e' -> C.RCase e' <$> goRAlts ralts

    go (C.RPin e1 e2) =
      uncurry C.RPin  <$> goPair e1 e2 

    gos [] = Untouched []
    gos (e:es) =
      case go e of
        Substituted e' -> Substituted (e':es)
        Untouched   e' -> (e':) <$> gos es 

    goPair e1 e2 =
      case go e1 of
        Substituted e1' -> Substituted (e1', e2)
        Untouched   e1' -> (\y -> (e1', y)) <$> go e2 

    goAlts [] = Untouched []
    goAlts ((p,e):alts) =
      if n `elem` C.freeVarsP p then
        ((p,e):) <$> goAlts alts
      else
        case go e of
          Substituted e' -> Substituted ((p,e'):alts)
          Untouched   e' -> ((p,e'):) <$> goAlts alts 
        
    goRAlts [] = Untouched []
    goRAlts ((p,e1,e2):ralts) =
      if n `elem ` C.freeVarsP p then
        ((p,e1,e2):) <$> goRAlts ralts
      else
        case goPair e1 e2 of
          Substituted (e1', e2') -> Substituted ((p,e1',e2'):ralts)
          Untouched   (e1', e2') -> ((p,e1',e2'):) <$> goRAlts ralts

    goBind bs =
      if n `elem` lhs then
        Untouched bs
      else
        zip lhs <$> gos rhs 
      where
        lhs = map fst bs
        rhs = map snd bs
                               
desugarRHS :: MonadDesugar m => [([S.LPat 'TypeCheck], S.Clause 'TypeCheck)] -> m (C.Exp Name)
desugarRHS pcs = withNewNames len $ \ns -> do 
  let e0 = makeTupleExpC [C.Var n | n <- ns]  
  let alts = map (\(ps, c) -> (makeTuplePatS ps, c)) pcs
  alts' <- desugarAlts alts  
  return $ foldr C.Abs (makeCase e0 alts') ns 
  where
    len = case pcs of
            []       -> 0
            (ps,_):_ -> length ps 

data CPat = CPHole
          | CPVar  Name
          | CPCon  Name [ CPat ]
          | CPBang CPat
          deriving Eq 

separatePat :: S.LPat 'TypeCheck -> (CPat, [S.LPat 'TypeCheck])
separatePat pat = go (unLoc pat) 
  where
    go (S.PVar (x, _ty)) = (CPVar x, [])
    go (S.PCon (c, _ty) ps) =
      let (ps', subs) = gos ps
      in (CPCon c ps', subs) 
      
    go (S.PREV p)  = (CPHole, [p])
    go (S.PWild (x, _ty)) = (CPBang (CPVar x), [])
    go (S.PBang p) =
      let (p', subs) = go (unLoc p)
      in (CPBang p', subs)

    gos []       = ([], []) 
    gos (p:ps) =
      let (p', subsP) = go (unLoc p)
          (ps', subsPs) = gos ps
      in (p':ps', subsP ++ subsPs) 

fillCPat :: CPat -> [C.Pat Name] -> C.Pat Name
fillCPat = evalState . go 
  where
    next :: State [C.Pat Name] (C.Pat Name)
    next = do
      (p:ps) <- get
      put ps
      return p

    go :: CPat -> State [C.Pat Name] (C.Pat Name)
    go (CPVar x) = return (C.PVar x)
    go (CPCon c ps) = C.PCon c <$> mapM go ps
    go (CPBang p)   = C.PBang <$> go p
    go CPHole       = next 

convertClauseU :: MonadDesugar m => S.Clause 'TypeCheck -> m (C.Exp Name)
convertClauseU (S.Clause body ws Nothing) =
  desugarExp (noLoc $ S.Let ws body)
convertClauseU _ = error "Cannot happen."

convertClauseR :: MonadDesugar m => S.Clause 'TypeCheck -> m (C.Exp Name, C.Exp Name)
convertClauseR (S.Clause body ws wi) = do 
  body' <- desugarExp (noLoc $ S.Let ws body)
  we' <- case wi of
           Just e  -> desugarExp e
           Nothing -> generateWithExp body' 
  return (body', we')
  where
    generateWithExp _ = withNewName $ \n -> withNewName $ \n' ->
      -- FIXME: more sophisticated with-exp generation. 
      return $ C.Bang $ C.Abs n $ C.Case (C.Var n) [ (C.PBang (C.PVar n'), C.Con conTrue []) ]

desugarAlts :: forall m. MonadDesugar m => [(S.LPat 'TypeCheck, S.Clause 'TypeCheck)] -> m [(C.Pat Name, C.Exp Name)]
desugarAlts alts = do
  let alts' = map (\(p,c) ->
                      let (cp, subs) = separatePat p
                      in (cp, subs, c)) alts
  -- grouping alts that have the same unidir patterns.
  let altss = groupBy ((==) `on` (\(cp,_,_) -> cp)) alts'
  mapM makeBCases altss
  where
    makeBCases :: [ (CPat, [S.LPat 'TypeCheck], S.Clause 'TypeCheck) ] -> m (C.Pat Name, C.Exp Name)
    makeBCases [] = error "Cannot happen"
    makeBCases ((cp, [], c):_) = do 
          -- In this case, the original pattern does not have any REV.
          -- so @length ralts > 1@ means that thare are some redundant patterns. 
          -- TOOD: say warning.

          let p = fillCPat cp []
          e <- convertClauseU c
          return (p, e)
    makeBCases ralts@((cp, firstSub, _):_) = do 
          -- Notice that all @cp@ and @length sub@ are the same in @ralts@.
          withNewNames len $ \xs -> do 
            let outP = fillCPat cp [C.PVar x | x <- xs]
            let re0 = makeTupleExpC [ C.Var x | x <- xs ] 

            pes <- forM ralts $ \(_, sub, c) -> do
              sub' <- mapM desugarPat sub 
              let rp = makeTuplePatC sub'
              (re, rw) <- convertClauseR c
              return (rp, re, rw)
            return (outP, C.RCase re0 pes)
     where
       len = length firstSub


desugarPat :: MonadDesugar m => S.LPat 'TypeCheck -> m (C.Pat Name)
desugarPat = go . unLoc
  where
    go (S.PVar (x, _ty))    = return $ C.PVar x
    go (S.PCon (c, _ty) ps) = C.PCon c <$> mapM desugarPat ps
    go _                    = error "desugarPat: Cannot happen."
    
desugarTopDecls ::
  MonadDesugar m => S.Decls 'TypeCheck (S.LDecl 'TypeCheck) -> m (C.Bind Name)
desugarTopDecls (S.Decls v _) = absurd v
desugarTopDecls (S.HDecls _ bss) = do 
  let defs = [ (n, pcs) | bs <- bss, Loc _ (S.DDef (n, _ty) pcs) <- bs ]
  forM defs $ \(n, pcs) -> do
    e <- desugarRHS pcs
    return (n, e)
    
                
  
-- -- Monad for desugaring 
-- type Desugar = ReaderT NameInfo (Either [(SrcSpan, String)])

-- type AlphaEnv = M.Map Name Name 

-- data NameInfo = NameInfo { niDefinedNames  :: [QName],
--                            niCurrentModule :: ModuleName,
--                            niNameCounter   :: Int,
--                            niAlphaEnv      :: AlphaEnv, 
--                            niOpTable       :: M.Map QName (S.Prec, S.Assoc) }

-- runDesugar :: ModuleName -> [QName] -> OpTable -> Desugar a -> IO a
-- runDesugar currentModule definedNames opTable d =
--   let ni = NameInfo { niDefinedNames = definedNames,
--                       niCurrentModule = currentModule,
--                       niNameCounter = 0,
--                       niAlphaEnv = M.empty,
--                       niOpTable = opTable }
--   in case runReaderT d ni of
--        Left ls ->
--          Fail.fail $ unlines [ show l ++ ": " ++ s | (l,s) <- ls ]
--        Right v -> return v 

-- -- defaultNameInfo :: NameInfo 
-- -- defaultNameInfo =
-- --   let tbl = M.fromList [
-- --         base "+" |-> (S.Prec 60, S.L),
-- --         base "-" |-> (S.Prec 60, S.L), 
-- --         base "*" |-> (S.Prec 70, S.L),
-- --         base "/" |-> (S.Prec 70, S.L)
-- --         ]
-- --   in NameInfo {
-- --     niDefinedNames  = [ nameTyArr, nameTyBang,
-- --                         nameTyChar, nameTyDouble, nameTyInt,
-- --                         nameTyList, nameTyRev, conTrue, conFalse ] ++ M.keys tbl ,
-- --     niCurrentModule = ["Main"],
-- --     niNameCounter = 1,
-- --     niAlphaEnv = M.empty, 
-- --     niOpTable = tbl
-- --     }
-- --   where
-- --     a |-> b = (a, b) 
-- --     base s = QName baseModule (NormalName s) 

-- withAlphaEntry :: Name -> Name -> Desugar a -> Desugar a
-- withAlphaEntry n1 n2 =
--   local (\ni -> ni { niAlphaEnv = M.insert n1 n2 $ niAlphaEnv ni })

-- withAlphaEntries :: [(Name, Name)] -> Desugar a -> Desugar a
-- withAlphaEntries ns m =
--   foldr (uncurry withAlphaEntry) m ns 

-- withDefinedName :: QName -> Desugar a -> Desugar a
-- withDefinedName n m = 
--   local (\ni -> ni { niDefinedNames = n : niDefinedNames ni }) m 

-- withDefinedNames :: [QName] -> Desugar a -> Desugar a
-- withDefinedNames ns m = foldr withDefinedName m ns 

-- withOpEntry :: QName -> (S.Prec, S.Assoc) -> Desugar a -> Desugar a
-- withOpEntry n (k,a) m =
--   local (\ni -> ni { niOpTable = M.insert n (k, a) $ niOpTable ni }) m

-- withOpEntries :: [ (QName, (S.Prec, S.Assoc)) ] -> Desugar a -> Desugar a
-- withOpEntries ns m = foldr (uncurry withOpEntry) m ns 

-- getCurrentModule :: Desugar ModuleName
-- getCurrentModule = asks niCurrentModule 

-- getOpTable :: Desugar (M.Map QName (S.Prec, S.Assoc))
-- getOpTable = asks niOpTable

-- lookupFixity :: QName -> Desugar (S.Prec, S.Assoc)
-- lookupFixity qname = do
--   tbl <- getOpTable
--   case M.lookup qname tbl of
--     Just (k, a) -> return (k, a)
--     Nothing     -> return (S.Prec 100, S.L)

-- isLeftAssoc :: (S.Prec, S.Assoc) -> (S.Prec, S.Assoc) -> Bool
-- isLeftAssoc (k1, a1) (k2, a2)
--   | k1 >  k2 = True
--   | k1 == k2, S.L <- a1, S.L <- a2 = True
--   | otherwise = False

-- isRightAssoc :: (S.Prec, S.Assoc) -> (S.Prec, S.Assoc) -> Bool
-- isRightAssoc (k1, a1) (k2, a2) 
--   | k1 <  k2 = True
--   | k1 == k2, S.R <- a1, S.R <- a2 = True
--   | otherwise = False 
      
             
-- refineName :: SrcSpan -> QName -> Desugar QName
-- refineName _ (QName m n) = return $ QName m n 
-- refineName l (BName n) = do
--   ns <- asks niDefinedNames
--   let res = checkNames n ns
--   case res of
--     [m]  -> return (QName m n)
--     []   -> do
--       env <- asks niAlphaEnv
--       case M.lookup n env of
--         Just n' -> return (BName n')
--         Nothing -> return (BName n)
--     _    -> throwError [ (l, "Ambiguous name `" ++ show n ++ "' " ++ show (nub res))]
--   where
--     -- assumes that QNames can only occur after BNames    
--     checkNames :: Name -> [QName] -> [ModuleName]
--     checkNames _ []            = [] 
--     checkNames n (BName n':ns)
--       | n == n'   = [] -- Ok. n is locally bound name.
--       | otherwise = checkNames n ns 
--     checkNames n (QName m n':ns)
--       | n == n'   = m:checkNames n ns -- n is defined in m 
--       | otherwise = checkNames n ns 
    
    
--     -- checkNames :: ModuleName -> Name -> [QName] -> [ModuleName]
--     -- checkNames _cm _n [] = []
--     -- checkNames cm n (BName n' : ns) =
--     --   if n == n' then cm : checkNames cm n ns else checkNames cm n ns
--     -- checkNames cm n (QName m n' : ns) =
--     --   if n == n' then m : checkNames cm n ns else checkNames cm n ns 
 
-- desugarTy :: S.Ty -> Desugar Ty
-- desugarTy (S.TVar q)    = return $ TyVar (BoundTv q) 
-- desugarTy (S.TCon n ts) = do
--   n' <- refineName NoLoc n 
--   TyCon n' <$> mapM (desugarTy . unLoc) ts
-- desugarTy (S.TForall n t) = do 
--   let (ns, t') = unForall $ unLoc t
--   TyForAll (map BoundTv $ n:ns) <$> desugarTy t'
--   where
--     unForall :: S.Ty -> ([Name], S.Ty)
--     unForall = go []
--     go ns (S.TForall n' t') =
--       go (n':ns) (unLoc t') 
--     go ns t = (reverse ns, t) 


-- newName :: (Name -> Desugar r) -> Desugar r 
-- newName f = do
--   i <- asks niNameCounter
--   local (\ni -> ni { niNameCounter = i + 1 }) $ f (Generated i)

-- newNameFrom :: Name -> (Name -> Desugar r) -> Desugar r
-- newNameFrom n f = do
--   i <- asks niNameCounter
--   local (\ni -> ni { niNameCounter = i + 1 }) $ f (Alpha n i) 

-- newNames :: Int -> ([Name] -> Desugar r) -> Desugar r
-- newNames n f = do
--   i <- asks niNameCounter
--   local (\ni -> ni { niNameCounter = i + n }) $ f (map Generated [i..i+n-1])

-- -- withNewNamesFor :: [Name] -> Desugar r -> Desugar r
-- -- withNewNamesFor ns m = 
-- --   newNames (length ns) $ \ns' ->
-- --     withAlphaEntries (zip ns ns') $ m

  
-- -- newQName :: (QName -> Desugar r) -> Desugar r 
-- -- newQName f = newName (f . BName) 


-- {-

-- desugar* functions perform the following transformations at once.

--  - Alpha-rename lambda and pattern bound names
--    while keeping def-bound names.
--    (based on de Bruijn indices) 

--  - Replace rules with patterns by case expressions.
--    This depends on the alpha renaming as we dig out patterns
--    in "rev" to introduce reversible case expressions where
--    the outer parts of the patterns have the same form. 

--  - Canonize def-bound names
--    + add qualifiers to names from other modules.
--    + remove quanlifiers from names from the current module. 
--    [TODO] Check: This procedue would have bugs, when shadowing. 

--  - Rearrange operators accordingly to their fixities.
--    [TODO] Test the conversion. 

-- -}

-- desugarLExp :: S.LExp -> Desugar OLExp
-- desugarLExp orig@(Loc l e) = do
--   e' <- desugarExp l e
--   return $ Orig (Just orig) (Loc l e') 

-- desugarExp :: SrcSpan -> S.Exp -> Desugar Exp
-- desugarExp _ (S.Lit l) = return $ Lit l
-- desugarExp l (S.Var n) = do
--   n' <- refineName l n
--   return $ Var n' 
-- desugarExp _ (S.App e1 e2) =
--   liftM2 App (desugarLExp e1) (desugarLExp e2)
-- desugarExp l (S.Abs ps e) = do
--   newNames (length ps) $ \xs -> do 
--     e' <- desugarExp l $
--           S.Case (S.makeTupleExp [noLoc $ S.Var (BName x) | x <- xs])
--           [ (S.makeTuplePat ps, S.Clause e [] Nothing) ]     
--     return $ unLoc $ desugared $ foldr (\n r -> noOrig $ noLoc (Abs n r)) (noOrig $ noLoc e') xs

-- desugarExp l (S.Con c es) = do
--   c' <- refineName l c 
--   Con c' <$> mapM desugarLExp es

-- desugarExp _ (S.Bang e) =
--   Bang <$> desugarLExp e

-- desugarExp _ (S.Case e cs) = desugarCaseExp e cs
-- desugarExp _ (S.Lift e1 e2) =
--   Lift <$> desugarLExp e1 <*> desugarLExp e2

-- desugarExp _ (S.Unlift e) =
--   Unlift <$> desugarLExp e 

-- desugarExp l (S.Fwd e) = do 
--   let c = nameTuple 2
--   newName $ \x ->
--     newName $ \y -> do 
--       e' <- desugarExp l (S.Unlift e) 
--       return $ Case (noOrig $ Loc (location e) e')
--         [ (noLoc $ PCon c [noLoc $ PBang $ noLoc $ PVar x, noLoc $ PBang $ noLoc $ PVar y],
--            noOrig $ noLoc $ Var (BName x)) ] 

-- desugarExp l (S.Bwd e) = do 
--   let c = nameTuple 2
--   newName $ \x ->
--     newName $ \y -> do 
--       e' <- desugarExp l (S.Unlift e) 
--       return $ Case (noOrig $ Loc (location e) e')
--         [ (noLoc $ PCon c [noLoc $ PBang $ noLoc $ PVar x, noLoc $ PBang $ noLoc $ PVar y],
--            noOrig $ noLoc $ Var (BName y)) ] 

-- desugarExp _ (S.Sig e t) = Sig <$> desugarLExp e <*> desugarTy (unLoc t)

-- desugarExp _ (S.Let [] e) = unLoc . desugared <$> desugarLExp e 
-- desugarExp _ (S.Let ds e) = do
--   (ds', ns, ops) <- desugarLDecls BName ds
--   withDefinedNames ns $
--    withOpEntries ops $ 
--      Let ds' <$> desugarLExp e

-- desugarExp _ (S.Parens e) = unLoc . desugared <$> desugarLExp e
-- desugarExp l (S.Op op e1 e2) = do
--   op' <- refineName l op 
--   unLoc . desugared <$> rearrangeOp l op' e1 e2 

-- desugarExp l (S.RCon c es) = do
--   c' <- refineName l c 
--   RCon c' <$> mapM desugarLExp es
  
-- desugarExp _ (S.RPin e1 e2) =
--   RPin <$> desugarLExp e1 <*> desugarLExp e2 


-- data CPat = CPHole
--           | CPVar  Name
--           | CPCon  QName [ Loc CPat ]
--           | CPBang (Loc CPat)

-- equivalentCPat :: CPat -> CPat -> Bool
-- equivalentCPat CPHole CPHole = True
-- equivalentCPat (CPVar n) (CPVar n') = n == n'
-- equivalentCPat (CPCon c ps) (CPCon c' ps') =
--   c == c' && length ps == length ps'
--   && and (zipWith (equivalentCPat `on` unLoc) ps ps')
-- equivalentCPat (CPBang p) (CPBang p') =
--   (equivalentCPat `on` unLoc) p p' 
-- equivalentCPat _ _ = False              

-- -- rename patterns under "PREV"
-- renamePatUnderRev :: S.LPat -> (LPat -> Desugar r) -> Desugar r
-- renamePatUnderRev p k0 = go p k0
--   where
--     go (Loc l (S.PVar n)) k = newNameFrom n $ \n' -> withAlphaEntry n n' $
--       k (Loc l (PVar n'))
--     go (Loc l (S.PCon c ps)) k = do
--       c' <- refineName l c 
--       gos ps $ \ps' -> k (Loc l (PCon c' ps')) 
--     go (Loc l _) _ = do
--       throwError [ (l, "reversible patterns cannot contain !, rev, _") ]

--     gos [] k = k []  
--     gos (p:ps) k =
--       go p $ \p' -> gos ps $ \ps' -> k (p':ps') 

-- -- patterns under "PREV" is not renamed 
-- renameAndSeparatePat :: S.LPat -> Desugar (Loc CPat, [S.LPat], [ (Name, Name) ], Int)
-- renameAndSeparatePat p = goL p $ \cp sub binds adv -> return (cp, sub,binds, adv)
--   where
--     goL (Loc l p) k = go l p $ \cp sub binds adv -> k (Loc l cp) sub binds adv
--     go _ (S.PVar n) k = newNameFrom n $ \n' ->
--       k (CPVar n') [] [(n,n')] 1
--     go l (S.PCon c ps) k = do
--       c' <- refineName l c
--       goLs ps $ \cps sub binds adv -> k (CPCon c' cps) sub binds adv
--     go _ (S.PBang p) k = do
--       goL p $ \cp sub binds adv -> k (CPBang cp) sub binds adv
--     go _ (S.PREV p) k = do
--       k CPHole [p] [] 0
--     go _ S.PWild k = newName $ \n' -> 
--       k (CPBang $ noLoc $ CPVar n') [] [] 1

--     goLs [] k = k [] [] [] 0
--     goLs (p:ps) k =
--       goL p $ \cp sub binds adv ->
--        goLs ps $ \cps sub' binds' adv' ->
--                  k (cp:cps) (sub ++ sub') (binds ++ binds') (adv + adv') 
  
-- -- separateLPat :: S.LPat -> Desugar (Loc CPat, [ LPat ])
-- -- separateLPat (Loc l p) = do
-- --   (p', sub) <- separatePat p
-- --   return (Loc l p', sub)

-- -- separatePat :: S.Pat -> Desugar (CPat, [ LPat ])
-- -- separatePat (S.PVar n) = return (CPVar n, [])
-- -- separatePat (S.PCon c ps) = do 
-- --   (ps', subs) <- unzip <$> mapM separateLPat ps
-- --   return (CPCon c ps', concat subs)
-- -- separatePat (S.PBang p) =  do
-- --   (p', sub) <- separateLPat p
-- --   return (CPBang p', sub)
-- -- separatePat S.PWild = error "Cannot happen" 
-- -- separatePat (S.PREV p) =  do
-- --   p' <- convertLPat p 
-- --   return (CPHole, [ p']) 

-- -- convertLPat :: S.LPat -> Desugar LPat
-- -- convertLPat (Loc l (S.PVar n)) = return $ Loc l (PVar n)
-- -- convertLPat (Loc l (S.PCon c ps)) = do
-- --   Loc l . PCon c <$> mapM convertLPat ps
-- -- convertLPat (Loc l (S.PBang p)) =
-- --   Loc l . PBang <$> convertLPat p
-- -- convertLPat (Loc _ S.PWild) = error "Cannot happen." 
-- -- convertLPat (Loc l (S.PREV _)) =
-- --   throwError [(l, "rev patterns cannot be nested.")] 

-- fillCPat :: Loc CPat -> [LPat] -> LPat
-- fillCPat c ps = evalState (go c) ps
--   where
--     next :: State [LPat] LPat 
--     next = do
--       (p:ps) <- get
--       put ps
--       return p

--     go :: Loc CPat -> State [LPat] LPat 
--     go (Loc l (CPVar x)) = return (Loc l (PVar x))
--     go (Loc l (CPCon c ps)) =
--       Loc l . PCon c <$> mapM go ps
--     go (Loc l (CPBang p)) =
--       Loc l . PBang <$> go p
--     go (Loc _ CPHole) = next 
  
      
      
  
-- -- makeTupleExp :: [LExp] -> LExp 
-- -- makeTupleExp [e] = e
-- -- makeTupleExp es  =
-- --   noLoc $ Con (nameTuple $ length es) es

-- makeTupleExpR :: [OLExp] -> OLExp
-- makeTupleExpR [e] = e
-- makeTupleExpR es  =
--   noOrig $ noLoc $ RCon (nameTuple $ length es) es

-- -- makeTuplePat :: [LPat] -> LPat
-- -- makeTuplePat [p] = p
-- -- makeTuplePat ps =
-- --   noLoc $ PCon (nameTuple $ length ps) ps 
  
                   

-- convertClauseU :: S.Clause -> Desugar OLExp
-- convertClauseU (S.Clause body ws Nothing) =
--   noOrig <$> Loc (location body) <$> desugarExp (location body) (S.Let ws body)
-- convertClauseU (S.Clause _ _ (Just e)) =
--   throwError [ (location e, "Unidirectional branch cannot have `with' expression") ]

-- convertClauseR :: S.Clause -> Desugar (OLExp, OLExp)
-- convertClauseR (S.Clause body ws (Just e)) = do
--   body' <- noOrig <$> Loc (location body) <$> desugarExp (location body) (S.Let ws body)
--   e'    <- desugarLExp e
--   return $ (body', e')
-- convertClauseR (S.Clause body ws Nothing) = do
--   body' <- noOrig <$> Loc (location body) <$> desugarExp (location body) (S.Let ws body)
--   -- FIXME: More sophisticated with-exp generation.
--   e' <- desugarLExp $ noLoc $ S.Bang $ noLoc $ S.Abs [noLoc S.PWild] (noLoc $ S.Con conTrue [])
--   return $ (body', e') 

  

-- desugarCaseExp :: Loc S.Exp -> [(Loc S.Pat, S.Clause)] -> Desugar Exp
-- desugarCaseExp e0 alts = do
--   e0' <- desugarLExp e0
--   alts' <- mapM (\(p,c) -> do
--                     (cp, sub, binds, adv) <- renameAndSeparatePat p 
--                     return (cp, sub, binds, adv, c)) alts
--   -- grouping alts that have the same unidir patterns. 
--   let altss = groupBy (equivalentCPat `on` (\(cp,_,_,_,_) -> unLoc cp)) alts'
--   alts <- mapM makeBCases altss 
--   return $ Case e0' alts 
--     where
--       makeBCases :: [ (Loc CPat, [S.LPat], [(Name,Name)], Int, S.Clause) ] -> Desugar (Loc Pat, OLExp)
--       makeBCases [] = error "Cannot happen." 
--       makeBCases ralts@((cp, sub, binds, adv, clause):_)
--         | [] <- sub = newNames adv $ \_ -> withAlphaEntries binds $ do 
--             -- in this case, the original pattern does not have any REV.
--             -- so length xs > 1 means that there are some redundant patterns.
--             -- 
--             -- FIXME: say warning            
--             let p = fillCPat cp [] 
--             e <- -- withNames (freeVarsP $ unLoc p) $
--                  convertClauseU clause
--             return (p, e)
--         | otherwise = newNames adv $ \_ -> do
--             -- Notice that, length sub, adv are equivalence 
--             -- in ralts, while binds can differ. 
--             newNames (length sub) $ \xs -> do 
--               let lxs = zipWith (\p x -> Loc (location p) $ PVar x) sub xs
--               let re0 = makeTupleExpR $ map (noOrig . noLoc . Var . BName) xs
--               let outP = fillCPat cp lxs 
--               pes <- mapM (\(_,subs,binds,_,cl) ->
--                               withAlphaEntries binds $ do 
--                                 let p = S.makeTuplePat subs
--                                 renamePatUnderRev p $ \p' -> do 
--                                   (eb, we) <- convertClauseR cl 
--                                   return (p', eb, we) ) ralts
--               return $ (outP , noOrig $ noLoc $ RCase re0 pes)


-- desugarLDecls :: (Name -> QName) -> [S.LDecl] -> Desugar ([LDecl], [QName], [(QName, (S.Prec, S.Assoc))]) 
-- desugarLDecls qualifier ds = do
--   let defs = [ (l, n, pcs) | Loc l (S.DDef n pcs) <- ds ]
--   let sigs = [ (l, n, t)   | Loc l (S.DSig n t) <- ds ]
--   let fixities = [ (qualifier n, (k,a)) | Loc _ (S.DFixity n k a) <- ds ] 
  
--   let defNames = [ n | (_, n, _) <- defs ]
--   let defQNames = map qualifier defNames

--   case filter (\(_,n,_) -> all (\m -> n /= m) defNames) sigs of 
--     ns@(_:_) ->
--       throwError [ (l, "No corresponding definition: " ++ show n) 
--                  | (l, n, _ ) <- ns ]       
--     [] -> do 
--       ds' <- withDefinedNames defQNames $
--               withOpEntries fixities $ 
--                mapM (desugarDef qualifier sigs) defs
--       return $ (ds', defQNames, fixities) 

-- desugarTopDecls ::
--   [Loc S.TopDecl]
--   -> Desugar ([LDecl], [QName], OpTable, TypeTable, SynTable)
-- desugarTopDecls tdecls = do
--   cm <- getCurrentModule
--   let decls = [ Loc l d | Loc l (S.DDecl d) <- tdecls ]
--   -- dataDecls <- sequence    
--   --   [ do cdecls' <- mapM desugarCDecl cdecls 
--   --        return $ Loc l (DData n ns cdecls')
--   --   | Loc l (S.DData n ns cdecls) <- tdecls ]

--   -- typeDecls <- sequence
--   --   [ do ty' <- desugarTy (unLoc ty)
--   --        return $ Loc l (DType n ns ty')
--   --   | Loc l (S.DType n ns ty) <- tdecls ]

--   let newTyNames = [ QName cm n | Loc _ (S.DData n _ _) <- tdecls ]
--                    ++ [ QName cm n | Loc _ (S.DType n _ _) <- tdecls ]

--   withDefinedNames newTyNames $ do   
--     dataTable <- fmap M.fromList $ fmap concat $ sequence 
--                  [ mapM (procCDecl cm n ns) cdecls 
--                  | Loc _ (S.DData n ns cdecls) <- tdecls ]

--     synTable <- M.fromList <$> sequence
--                 [ do ty' <- desugarTy (unLoc ty)
--                      let ns' = map BoundTv ns 
--                      when (not $ isClosed ns' ty') $ 
--                        throwError [(loc, prettyShow ty ++ " contains unboudn variable(s).")]
--                      return (BName n, (ns', ty')) 
--                 | Loc loc (S.DType n ns ty) <- tdecls ]

--     (decls', qnames, entries) <-
--       withDefinedNames (M.keys dataTable) $
--         desugarLDecls (QName cm) decls

--     let opTable = M.fromList [ (n,v) | (n, v) <- entries ]
  
--     return (decls', qnames++newTyNames++M.keys dataTable, opTable, dataTable, synTable)
--   where
--     procCDecl :: ModuleName -> Name -> [Name] -> Loc S.CDecl -> Desugar (QName, Ty)
--     procCDecl cm n ns (Loc loc (S.CDecl c ts)) = do
--       let ns' = map BoundTv ns 
--       ty <- foldr (\t m -> do
--                       r  <- m 
--                       t' <- desugarTy (unLoc t) 
--                       return $ TyCon nameTyLArr [t', r])
--                   (pure $ TyCon (QName cm n) $ map TyVar ns') ts

--       when (not $ isClosed ns' ty) $
--         throwError [(loc, prettyShow ty ++ " contains unbound variable")]

--       return (QName cm c, TyForAll ns' ty) 
      

--     isClosed bs (TyVar ty)      = ty `elem` bs
--     isClosed bs (TyForAll ns t) = isClosed (ns ++ bs) t
--     isClosed bs (TyCon _ ts)    = all (isClosed bs) ts
--     isClosed _  _               = error "Cannot happen (at this point)." 
    
--     -- desugarCDecl (Loc _ (S.CDecl n ts)) = do
--     --   ts' <- mapM (desugarTy . unLoc) ts
--     --   return $ CDecl n ts'
     
      
-- desugarDef ::
--   (Name -> QName) 
--   -> [ (SrcSpan, Name, S.LTy) ]
--   -> (SrcSpan, Name, [ ([S.LPat], S.Clause) ])
--   -> Desugar LDecl
-- desugarDef qualifier sigs (l, f, pcs) = do
--   case map unwrap $ group $ sort [ length ps | (ps, _) <- pcs ] of
--     []    -> throwError [ (l, "Empty definition: " ++ show f) ]
--     [len] -> do
--       newNames len $ \xs -> do 
--         e' <- desugarExp l $
--               S.Case (S.makeTupleExp [noLoc $ S.Var (BName x) | x <- xs])
--               [ (S.makeTuplePat ps, clause) | (ps, clause) <- pcs ]
--         let body =
--               foldr (\x r -> noOrig $ noLoc $ Abs x r) (noOrig $ noLoc e') xs
--         sig <- case filter (\(_,n,_) -> n == f) sigs of
--                  []  -> return $ Nothing
--                  [(_,_,t)] -> return $ Just t
--                  res -> throwError $ [ (l, "Multiple signatures for " ++ show f)
--                                      | (l,_,_) <- res ]

--         sig' <- traverse (desugarTy . unLoc) sig
--         return $ Loc l (DDef (qualifier f) sig' body)
--     ls -> 
--       throwError [ (l, "#Arguments differ for " ++ show f ++ show ls) ]
--   where
--     unwrap (a:_) = a
--     unwrap _     = error "Cannot happen." 



-- {-
-- Currently, the operators are parsed as if they were left-associative
-- and has the same precedence. Thus,

--   x1 op1 x2 op2 x3 op3 ... opn xn+1

-- will be parsed as

--   ((...((x1 op1 x2) op2 x3)...) opn xn+1)

-- Here we rearrange the operators in the right way.

-- Let us focus on op1 and op2 first. The association (x1 op1 x2) op2 x3
-- is right only if

--   - op1 and op2 has the same precedence and op1 and op2 are
--     left-associative, or 
--   - op1 has the greater precedence than op2.

-- Instead, it should be associated as x1 op1 (x2 op2 x3) 

--   - op1 and op2 has the same precedence and op1 and op2 are
--     right-associative, or 
--   - op2 has the greater precedence than op1.

-- Otherwise, we need parentheses; that is, there is a syntax error.

-- In the former case, it is rather straight forward to proceed the 

-- -}

-- rearrangeOp :: SrcSpan -> QName -> S.LExp -> S.LExp -> Desugar OLExp
-- rearrangeOp l1 op e1 e2 = do
--   e2' <- desugarLExp e2
--   go l1 e1 op e2'
--     where
--       go l2 (Loc l1 (S.Op op1 e1 e2)) op2' e3' = do
--         op1' <- refineName l1 op1
--         (k1, a1) <- lookupFixity op1' 
--         (k2, a2) <- lookupFixity op2'
--         if | isLeftAssoc (k1, a1) (k2, a2) -> do
--                e2' <- desugarLExp e2
--                e12' <- go l1 e1 op1' e2'
--                return $ opExp l2 op2' e12' e3'
--            | isRightAssoc (k1, a1) (k2, a2) -> do
--                e1'  <- desugarLExp e1
--                e23' <- go l2 e2 op2' e3'
--                return $ opExp l1 op1' e1' e23'
--            | otherwise ->
--                throwError [ (l1, "Parens are needed between: _ " ++ prettyShow op1' ++ " _ " ++ prettyShow op2' ++ " _.") ]
--       go l e1 op' e2' = do
--         e1' <- desugarLExp e1
--         return $ opExp l op' e1' e2' 

-- opExp :: SrcSpan -> QName -> OLExp -> OLExp -> OLExp 
-- opExp l opName exp1 exp2 =
--   foldl (\r a -> lapp r a) (noOrig $ Loc l $ Var opName) [exp1, exp2] 
--   where
--     lapp e1 e2 = noOrig $ Loc (location (desugared e1) <> location (desugared e2)) (App e1 e2) 
               
        
