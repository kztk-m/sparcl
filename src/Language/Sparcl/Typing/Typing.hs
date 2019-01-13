{-# LANGUAGE ViewPatterns #-}
module Language.Sparcl.Typing.Typing where

import Data.Void

import Language.Sparcl.Typing.TC
import Language.Sparcl.Typing.Type
import Language.Sparcl.SrcLoc 
import Language.Sparcl.Surface.Syntax hiding (Ty(..))
import Language.Sparcl.Pass
import Language.Sparcl.Literal
import Language.Sparcl.Name

import qualified Language.Sparcl.Surface.Syntax as S


import Control.Monad.Except
import qualified Data.Map as M 

import Language.Sparcl.Pretty as D hiding ((<$>))

import Data.List ((\\))

-- import Control.Exception (evaluate)

-- import Debug.Trace 

-- checkUnificationError :: MonadTypeCheck m => SrcSpan -> Ty -> Ty -> m a -> m a
-- checkUnificationError loc ty1 ty2 e = do
--   catchError e $ \d -> do 
--       ty1' <- zonkType ty1
--       ty2' <- zonkType ty2
--       throwError $ ppr loc D.<$> (D.align $ D.nest 2 $ 
--                                   D.vsep [D.text "Type error",
--                                           D.nest 2 $ D.hsep [D.text "Expected:", D.align $ ppr ty2'],
--                                           D.nest 2 $ D.hsep [D.text "Inferred:", D.align $ ppr ty1'] ])
--                    D.<$> D.text "Detail:" D.<+> d

ty2ty :: S.LTy 'Renaming -> Ty
ty2ty (Loc _ ty) = go ty
  where
    go (S.TVar x) = TyVar (BoundTv x)
    go (S.TCon c ts) = TyCon c $ map ty2ty ts
    go (S.TForall x t) = gatherBoundTv [BoundTv x] t

    gatherBoundTv xs (unLoc -> S.TForall y t) = gatherBoundTv (BoundTv y:xs) t
    gatherBoundTv xs t                        = TyForAll (reverse xs) $ ty2ty t 
  

tryUnify :: MonadTypeCheck m => SrcSpan -> Ty -> Ty -> m () 
tryUnify loc ty1 ty2 =
  catchError (atLoc loc $ unify ty1 ty2) $ \(TypeError loc' ctxt reason) ->
    case reason of
      UnMatchTy ty3 ty4 -> do
        ty1' <- zonkType ty1
        ty2' <- zonkType ty2
        -- mp   <- M.fromList <$> traverseTy ty1'
        -- trace (show $ D.text "Snap shot" D.<+> D.align (pprMap mp)) $
        throwError $ TypeError loc' ctxt (UnMatchTyD ty1' ty2' ty3 ty4)  
      _ ->
        throwError $ TypeError loc' ctxt reason

  -- where

traverseTys :: (Traversable t, MonadTypeCheck f) => t Ty -> f [(Int, Ty)]
traverseTys ts = concat <$> mapM traverseTy ts

traverseTy :: MonadTypeCheck f => Ty -> f [(Int, Ty)]
traverseTy (TyCon _ ts) = traverseTys ts
traverseTy (TyVar _)    = return []
traverseTy (TyMetaV tv@(MetaTyVar i _)) = do
  res <- readTyVar tv
  case res of
    Nothing -> return []
    Just ty -> ((i, ty) :) <$> traverseTy ty
traverseTy (TyForAll _ t) = traverseTy t
traverseTy (TySyn _ ty)   = traverseTy ty 


-- atExp :: MonadTypeCheck m => m a -> Exp -> m a
-- atExp m e =
--   catchError m $ \doc ->
--     throwError $ doc D.<$>
--                  D.nest 2 (D.text "when checking expression:"
--                            D.</> ppr e)

-- tryUnifyE :: MonadTypeCheck m => SrcSpan -> Exp -> Ty -> Ty -> m ()
-- tryUnifyE loc e ty1 ty2 =
--   tryUnify loc ty1 ty2 `atExp` e 

instantiate :: MonadTypeCheck m => PolyTy -> m MonoTy
instantiate (TyForAll ts t) = do
  ms <- mapM (const newMetaTy) ts
  return $ substTy (zip ts ms) t
instantiate t = return t 

instPoly :: MonadTypeCheck m => SrcSpan -> PolyTy -> BodyTy -> m () 
instPoly loc polyTy expectedTy = do  
  t <- instantiate polyTy
  tryUnify loc t expectedTy

inferExp :: MonadTypeCheck m => LExp 'Renaming -> m (LExp 'TypeCheck, PolyTy)
inferExp expr = do
  (expr', ty) <- inferTy expr
  ty' <- zonkType ty
  envMetaVars <- getMetaTyVarsInEnv
  let mvs = metaTyVars [ty']
  polyTy <- quantify (mvs \\ envMetaVars) ty'
  return (expr', polyTy) 
  
  
inferTy :: MonadTypeCheck m => LExp 'Renaming -> m (LExp 'TypeCheck, BodyTy)
inferTy (Loc loc expr) = go expr
  where
    go (Sig e tySyn) = do
      let ty = ty2ty tySyn
      e' <- checkTy e (ty2ty tySyn)
      return (e', ty) 
    go e = do 
      ty <- newMetaTy
      e' <- checkTy (Loc loc e) ty
      return (e', ty) 

ensureFunTy :: MonadTypeCheck m => SrcSpan -> MonoTy -> m (MonoTy, MonoTy)
ensureFunTy loc ty = do
  argTy <- newMetaTy 
  resTy <- newMetaTy 
  tryUnify loc (argTy -@ resTy) ty
  return (argTy, resTy) 

ensureBangTy :: MonadTypeCheck m => SrcSpan -> MonoTy -> m MonoTy
ensureBangTy loc ty = do
  argTy <- newMetaTy 
  tryUnify loc (bangTy argTy) ty
  return argTy 

ensureRevTy :: MonadTypeCheck m => SrcSpan -> MonoTy -> m MonoTy
ensureRevTy loc ty = do
  argTy <- newMetaTy 
  tryUnify loc (revTy argTy) ty
  return argTy 

ensurePairTy :: MonadTypeCheck m => SrcSpan -> MonoTy -> m (MonoTy, MonoTy)
ensurePairTy loc ty = do
  fstTy <- newMetaTy 
  sndTy <- newMetaTy 
  tryUnify loc (TyCon (nameTyTuple 2) [fstTy, sndTy]) ty
  return (fstTy, sndTy) 
   
checkTy :: MonadTypeCheck m => LExp 'Renaming -> BodyTy -> m (LExp 'TypeCheck) 
checkTy lexp@(Loc loc expr) expectedTy = fmap (Loc loc) $ atLoc loc $ atExp lexp $ go expr
  where
    go (Var x) = do
      tyOfX <- askType loc x 
      instPoly loc tyOfX expectedTy
      return (Var (x, tyOfX))

    go (Lit l) = do
      case l of
        LitInt _ ->
          tryUnify loc (TyCon nameTyInt []) expectedTy
        LitChar _ ->
          tryUnify loc (TyCon nameTyChar []) expectedTy
        LitDouble _ ->
          tryUnify loc (TyCon nameTyDouble []) expectedTy
      return (Lit l)

    go (Abs pats e) = do
      ts <- mapM (const newMetaTy) pats
      (pats', ubind, lbind) <- checkPatsTy pats ts
      retTy <- newMetaTy
      e' <- withUVars ubind $ withLVars lbind $ checkTy e retTy  
      tryUnify loc (foldr (-@) retTy ts) expectedTy
      return $ Abs pats' e' 
        
    go (App e1 e2) = do
      (e1', ty1) <- inferTy e1
      (argTy, resTy) <- atExp e1 $ ensureFunTy (location $ e1) ty1 
      e2' <- checkTy e2 argTy
      tryUnify loc resTy expectedTy
      return (App e1' e2')

    go (Con c es) = do
      tyOfC <- instantiate =<< askType loc c
      (es', retTy) <- foldM inferApp ([], tyOfC) es
--      trace (show $ ppr c D.<+> D.colon D.<+> D.align (ppr tyOfC)) $
      tryUnify loc retTy expectedTy
      return (Con (c, tyOfC) (reverse es'))
        where
          inferApp (es', ty) e = do 
            (argTy, resTy) <- ensureFunTy (location e) ty
            e' <- checkTy e argTy
            return (e':es', resTy)

    go (Bang e) = do
      ty <- ensureBangTy loc expectedTy
      e' <- withoutLinear $ checkTy e ty
      return $ Bang e' 

    go (Case e alts) = do
      tyPat <- newMetaTy 
      e' <- checkTy e tyPat 
      alts' <- checkAltsTy alts tyPat expectedTy
      return (Case e' alts')

    -- e1 : !(!a -o b)
    -- e2 : !(!b -o a)
    -- --------------
    -- lift e1 e2 : !(rev a -o rev b) 

    go (Lift e1 e2) = do
      ty <- ensureBangTy loc expectedTy
      (argTy, resTy) <- ensureFunTy loc ty
      tyA <- ensureRevTy loc argTy
      tyB <- ensureRevTy loc resTy
      let expectedTy1 = bangTy (bangTy tyA -@ tyB)
      let expectedTy2 = bangTy (bangTy tyB -@ tyA)
      e1' <- checkTy e1 expectedTy1
      e2' <- checkTy e2 expectedTy2
      return (Lift e1' e2')
  
    -- e : !(rev a -o rev b)
    -- ---------------------
    -- unlift e : (!(!a -o b) x !(!b -o a))

    go (Unlift e) = do
      (tyFst, tySnd) <- ensurePairTy loc expectedTy 
      
      tyFst' <- ensureBangTy loc tyFst -- !a -o b
      tySnd' <- ensureBangTy loc tySnd -- !b -o a

      (tyBangA,  tyB) <- ensureFunTy loc tyFst'
      (tyBangB', tyA') <- ensureFunTy loc tySnd'
      tyA  <- ensureBangTy loc tyBangA
      tyB' <- ensureBangTy loc tyBangB'

      tryUnify loc tyA' tyA
      tryUnify loc tyB' tyB 
      
      e' <- checkTy e (bangTy $ revTy tyA -@ revTy tyB)
      return (Unlift e')
        
    go (Sig e tySyn) = do
      let ty = ty2ty tySyn       
      ty' <- instantiate ty
      tryUnify loc ty' ty
      e' <- checkTy e ty'
      return $ unLoc e'

    go (Parens e) = do
      e' <- checkTy e expectedTy
      return (Parens e')

    go (Op op e1 e2) = do
      tyOfOp <- instantiate =<< askType loc op
      ty1    <- newMetaTy
      ty2    <- newMetaTy
      e1' <- checkTy e1 ty1
      e2' <- checkTy e2 ty2
      tryUnify loc (ty1 -@ ty2 -@ expectedTy) tyOfOp 
      return $ Op (op, tyOfOp) e1' e2' 


    go (RCon c es) = do
      tyOfC <- fmap addRev . instantiate =<< askType loc c
      (es',retTy) <- foldM inferApp ([], tyOfC) es
      tryUnify loc retTy expectedTy
      return $ RCon (c, tyOfC) (reverse es')
        where
          inferApp (es',ty) e = do 
            (argTy, resTy) <- ensureFunTy (location e) ty
            e' <- checkTy e argTy
            return (e':es', resTy)

          addRev (TyCon t [t1,t2]) | t == nameTyLArr = TyCon t [revTy t1, addRev t2]
          addRev t                                   = revTy t 
                                                       
    -- go (RCase e ralts) = do
    --   tyPat <- newMetaTy 
    --   checkTy e (revTy tyPat)
    --   ty <- ensureRevTy loc expectedTy 
    --   checkRAltsTy ralts tyPat ty 
      
    -- e1 : rev a   
    -- e2 : !a -> rev b
    -- ----------------
    -- pin e1 e2 : rev (a, b)

    go (RPin e1 e2) = do
      tyAB <- ensureRevTy loc expectedTy
      (tyA, tyB) <- ensurePairTy loc tyAB 

      e1' <- checkTy e1 (revTy tyA)
      e2' <- checkTy e2 (bangTy tyA -@ revTy tyB)

      return (RPin e1' e2')

    go (Let decls e) = do
      (decls', bind) <- inferDecls decls 
      e' <- withUVars bind $ checkTy e expectedTy
      return $ Let decls' e' 

inferMutual :: MonadTypeCheck m => [LDecl 'Renaming] -> m ([LDecl 'TypeCheck], [(Name, PolyTy)])
inferMutual decls = do
--  let nes = [ (n,e) | Loc _ (DDef n _) <- decls ]
  let ns  = [ n | Loc _ (DDef n _) <- decls ]
  let defs = [ (loc, n, pcs) | Loc loc (DDef n pcs) <- decls ]
  let sigMap = M.fromList [ (n, ty2ty t) | Loc _ (DSig n t) <- decls ]

  tys <- mapM (\n -> case M.lookup n sigMap of
                       Just t  -> return t
                       Nothing -> newMetaTy) ns

  nts0 <- withUVars (zip ns tys) $ forM defs $ \(loc, n, pcs) -> do
    ty  <- newMetaTy
    pcs' <- mapM (flip (checkTyPC loc) ty) pcs 
    tyE <- askType loc n -- type of n in the environment 
    when (not $ M.member n sigMap) $
      -- Defer unification if a declaration comes with a signature because
      -- the signature can be a polytype while unification targets monotypes. 
      tryUnify loc ty tyE
    return (n, loc, ty, pcs') 

  envMetaVars <- getMetaTyVarsInEnv

  nts1 <- forM nts0 $ \(n, loc, t, pcs') -> do 
    tt <- zonkType t 
    let mvs = metaTyVars [tt]
    polyTy <- quantify (mvs \\ envMetaVars) tt 
    
    case M.lookup n sigMap of
      Nothing    -> return (n, loc, polyTy, pcs')
      Just sigTy -> do 
        checkMoreGeneral loc polyTy sigTy
        return (n, loc, sigTy, pcs')

  let decls' = [ Loc loc (DDef (n, ty) pcs') | (n, loc, ty, pcs') <- nts1 ]
  let binds' = [ (n, ty) | (n, _, ty, _) <- nts1 ]

  return (decls', binds') 
    where
      checkTyPC loc (ps, c) expectedTy = do
        tys <- mapM (const newMetaTy) ps 
        (ps', ubind, lbind) <- checkPatsTy ps tys
        retTy <- newMetaTy 
        c' <- withUVars ubind $ withLVars lbind $ checkClauseTy c retTy
        tryUnify loc (foldr (-@) retTy tys) expectedTy
        return (ps', c')
        
inferDecls :: MonadTypeCheck m => Decls 'Renaming (LDecl 'Renaming) ->
              m (Decls 'TypeCheck (LDecl 'TypeCheck), [(Name, PolyTy)])
inferDecls (Decls v _) = absurd v
inferDecls (HDecls _ dss) = do
  (dss', bind) <- go [] dss
  return (HDecls () dss', bind)
  where 
    go bs [] = return ([], bs)
    go bs (ds:rest) = do
      (ds', bind) <- inferMutual ds
      (rest', bs') <- withUVars bind $ go (bind ++ bs) rest
      return (ds':rest', bs')


inferTopDecls ::
  MonadTypeCheck m =>
  Decls 'Renaming (LDecl 'Renaming) ->
  [Loc (Name, [Name], [Loc (CDecl 'Renaming)])] -> 
  [Loc (Name, [Name], LTy 'Renaming)] ->
  m (Decls 'TypeCheck (LDecl 'TypeCheck), [(Name, PolyTy)],
     TypeTable, SynTable)
inferTopDecls decls dataDecls typeDecls = do 
  let synTable = M.fromList $ 
        flip map typeDecls $ \(Loc _ (n, ns, lty)) ->
                               let ty = ty2ty lty
                               in (n, (map BoundTv ns, ty))
        
  let typeTable = M.fromList $
        [ (n, foldr (-@) typeKi (map (const typeKi) ns)) | Loc _ (n, ns, _) <- dataDecls ]
        ++
        [ (cn, TyForAll tvs (foldr (-@) (TyCon n $ map TyVar tvs) $ map ty2ty tys)) |
          Loc _ (n, ns, cdecls) <- dataDecls,
          let tvs = map BoundTv ns, 
          Loc _ (CDecl cn tys) <- cdecls ]

  withUVars (M.toList typeTable) $
   withSyns (M.toList synTable) $ do
     (decls', nts) <- inferDecls decls
     return (decls', nts, typeTable, synTable)

checkClauseTy :: MonadTypeCheck m => Clause 'Renaming -> Ty -> m (Clause 'TypeCheck)
checkClauseTy (Clause e ws wi) expectedTy = do
  (ws', bind) <- inferDecls ws
  withUVars bind $ do
    e'  <- checkTy e expectedTy
    wi' <- case wi of
             Just ewi -> do
               ty   <- ensureRevTy (location e) expectedTy
               ewi' <- checkTy ewi (bangTy (bangTy ty -@ boolTy))
               return (Just ewi')
             Nothing -> return Nothing
    return (Clause e' ws' wi')
  
        
-- inferDecls :: MonadTypeCheck m => [LDecl] -> m [(Name, PolyTy)]
-- inferDecls decls = do
--   let declss = map unSCC (G.stronglyConnComp graph)
--   foldr (\ds m -> do 
--             bind <- inferMutual ds
--             withUVars bind $ fmap (bind ++) m ) (return []) declss    
--   where
--     unSCC (G.AcyclicSCC x) = [x]
--     unSCC (G.CyclicSCC xs) = xs

--     graph = [ (decl, n, freeVars e) | decl@(Loc _ (DDef n _ e)) <- decls ]
    
  

skolemize :: MonadTypeCheck m => PolyTy -> m ([TyVar], BodyTy)
skolemize (TyForAll tvs ty) = do
  sks <- mapM newSkolemTyVar tvs
  return (sks, substTy (zip tvs $ map TyVar sks) ty)
skolemize ty = return ([], ty) 

checkMoreGeneral :: MonadTypeCheck m => SrcSpan -> PolyTy -> PolyTy -> m ()
checkMoreGeneral loc polyTy1 polyTy2@(TyForAll _ _) = do
  (skolemTyVars, ty2) <- skolemize polyTy2
  checkMoreGeneral loc polyTy1 ty2
  escapedTyVars <- freeTyVars [polyTy1]

  let badTyVars = filter (`elem` escapedTyVars) skolemTyVars
  unless (null badTyVars) $
    typeError $ Other $ D.group $
    D.cat [ D.text "The inferred type",
            D.nest 2 (D.line D.<> D.dquotes (ppr polyTy1)),
            D.text "is not polymorphic enough for:",
            D.nest 2 (D.line D.<> D.dquotes (ppr polyTy2)) ]
checkMoreGeneral loc polyTy1@(TyForAll _ _) ty2 = do
  ty1 <- instantiate polyTy1
  checkMoreGeneral loc ty1 ty2

checkMoreGeneral loc ty1 ty2 = do
  tryUnify loc ty1 ty2 
                                           
                         
quantify :: MonadTypeCheck m => [MetaTyVar] -> BodyTy -> m PolyTy
quantify mvs ty = do
  forM_ (zip mvs newBinders) $
    \(mv, tyv) -> writeTyVar mv (TyVar tyv) 
  ty' <- zonkType ty
  return $ TyForAll newBinders ty'   
  where
    binders (TyForAll bs t) = bs ++ binders t
    binders (TyCon _ ts) = concatMap binders ts
    binders (TyVar _)    = []
    binders (TySyn t  _) = binders t 
    binders (TyMetaV _)  = []
    
    usedBinders = binders ty
    newBinders = take (length mvs) $ allFancyBinders \\ usedBinders

allFancyBinders :: [TyVar]
allFancyBinders = map (BoundTv . Local . User) $
  [ [x] | x <- ['a'..'z'] ] ++
  [ x : show i | i <- [1::Integer ..], x <- ['a'..'z'] ] 


checkAltsTy ::
  MonadTypeCheck m => [ (LPat 'Renaming, Clause 'Renaming) ] ->
  MonoTy -> BodyTy -> m [ (LPat 'TypeCheck, Clause 'TypeCheck) ]
checkAltsTy alts patTy bodyTy = mapM checkAltTy alts
  where
    checkAltTy (p, c) = do
      (p', ubind, lbind) <- checkPatTy p patTy
      c' <- withUVars ubind $ withLVars lbind $ checkClauseTy c bodyTy
      return (p', c') 
        

-- checkAltsTy :: MonadTypeCheck m => [ (Loc Pat, LExp) ] -> MonoTy -> BodyTy -> m ()
-- checkAltsTy [] _ _ = return ()
-- checkAltsTy ((p,e):alts) pty bty = do
--   (ubinds, lbinds) <- checkPatTy p pty
--   withLVars lbinds $
--    withUVars ubinds $ do
--     -- mp   <- M.fromList <$> traverseTy pty
--     -- mps  <- foldr M.union M.empty <$> mapM (fmap M.fromList . traverseTy . snd) lbinds
--     -- mps2 <- foldr M.union M.empty <$> mapM (fmap M.fromList . traverseTy . snd) ubinds 
--     -- pty' <- zonkType pty 
--     -- trace (show $ D.vsep [ D.text "pat:" D.<+> D.align (ppr p),
--     --                        D.text "pty:" D.<+> D.align (ppr pty'), 
--     --                        D.text "ubind:" D.<+> D.align (pprMap (M.fromList ubinds)),
--     --                        D.text "lbind:" D.<+> D.align (pprMap (M.fromList lbinds)),
--     --                        D.text "ss:" D.<+> D.align (pprMap (M.unions [mp, mps,mps2])),
--     --                        D.empty ])
--     checkTy e bty
--   checkAltsTy alts pty bty 

-- checkRAltsTy :: MonadTypeCheck m => [ (Loc Pat, OLExp, OLExp) ] -> MonoTy -> BodyTy -> m ()
-- checkRAltsTy [] _ _ = return ()
-- checkRAltsTy ((p,e,e'):ralts) pty bty = do
--   -- the top level "rev" are already removed in pty and bty
--   (ubinds, lbinds) <- checkPatTy p pty
--   case ubinds of
--     (_:_) ->
--       typeError $ Other $ D.hsep [ ppr (location p), D.text "Patterns in reversible computation cannot bind unrestricted variable." ]
--     _ -> do 
--       withLVars [ (x, revTy t) | (x, t) <- lbinds ] $
--         checkTy e (revTy bty) 
--       checkTy e' (bangTy (bangTy bty -@ boolTy))
--       checkRAltsTy ralts pty bty 

checkPatsTy :: MonadTypeCheck m => [LPat 'Renaming] -> [MonoTy] -> m ([LPat 'TypeCheck], [(Name, MonoTy)], [(Name, MonoTy)])
checkPatsTy [] [] = return ([], [], [])
checkPatsTy (p:ps) (t:ts) = do
  (p', ubind, lbind) <- checkPatTy p t
  (ps', ubind', lbind') <- checkPatsTy ps ts
  return (p':ps', ubind++ubind', lbind++lbind')    
checkPatsTy _ _ = error "checkPatsTy: Cannot happen."

checkPatTy :: MonadTypeCheck m => LPat 'Renaming -> MonoTy -> m (LPat 'TypeCheck, [(Name, MonoTy)], [(Name,MonoTy)] )
checkPatTy = checkPatTyWork False

checkPatTyWork ::
  MonadTypeCheck m =>
  Bool -> LPat 'Renaming -> MonoTy -> m (LPat 'TypeCheck, [(Name, MonoTy)], [(Name, MonoTy)])
checkPatTyWork flg (Loc loc pat) expectedTy = do
  (pat', ubind, lbind) <- go pat
  return (Loc loc pat', ubind, lbind)
    where
      go (PVar x) =
        return (PVar (x,expectedTy), [], [(x,expectedTy)])
        
      go (PBang p) = do
        ty <- ensureBangTy loc expectedTy
        (p', ubind, lbind) <- checkPatTyWork flg p ty
        return (PBang p', ubind ++ lbind, [])
        
      go (PCon c ps) = do
       tyOfC <- instantiate =<< askType loc c
       (ps', retTy, ubind, lbind) <- foldM inferApp ([], tyOfC, [], []) ps
       tryUnify loc retTy expectedTy
       retTy' <- zonkType retTy
       case retTy' of
         TyCon n [_,_] | n == nameTyLArr ->
           atLoc loc $ typeError $ Other $ text "Constructor" <+> ppr n <+> text "must be fully applied."
         _ -> 
       -- mp <- traverseTys [tyOfC, retTy, expectedTy]
       -- trace (show $ D.text "ty: " D.<+> D.align (ppr retTy) D.<+> D.align (ppr expectedTy)
       --               D.<$> D.text "ss (for c):" D.<+> D.align (pprMap $ M.fromList mp)) $         
           return (PCon (c, tyOfC) (reverse ps'), ubind, lbind) 
       where
         inferApp (ps', ty, ubind, lbind) p = do 
           (argTy, resTy) <- ensureFunTy (location p) ty
           (p', ubind', lbind') <- checkPatTyWork flg p argTy 
           return (p':ps', resTy, ubind'++ubind, lbind' ++ lbind)

      go (PREV p)
        | flg = atLoc loc $ typeError $ Other $ text "rev patterns cannot be nested."
        | otherwise = do
            ty <- ensureRevTy loc expectedTy
            (p', ubind, lbind) <- checkPatTyWork True p ty
            when (not $ null ubind) $
              atLoc loc $ typeError $ Other $ text "rev patterns cannot contain !."
            let ubind' = map (\(x, t) -> (x, revTy t)) ubind
            let lbind' = map (\(x, t) -> (x, revTy t)) lbind
            return (PREV p', ubind', lbind')

      go (PWild x) = do 
        (PBang (Loc _ (PVar x')), ubind, lbind) <- go (PBang (noLoc $ PVar x))
        return (PWild x', ubind, lbind) 
        
--   where
--      go (PVar x) expectedTy = return ([], [(BName x,expectedTy)])
--      go (PBang p) expectedTy = do
--        ty <- ensureBangTy loc expectedTy  
--        (ubind, lbind) <- checkPatTy p ty
--        -- mp <- traverseTy expectedTy
--        -- trace (show $ D.text "ty: " D.<+> D.align (ppr ty)
--        --               D.<$> D.text "ss (for !pat):" D.<+> D.align (pprMap $ M.fromList mp)) $ 
--        return $ (ubind ++ lbind, [])
--      go (PCon c ps) expectedTy = do
--        tyOfC <- instantiate =<< askType loc c
--        (retTy, ubind, lbind) <- foldM inferApp (tyOfC, [], []) ps
--        tryUnify loc retTy expectedTy
--        -- mp <- traverseTys [tyOfC, retTy, expectedTy]
--        -- trace (show $ D.text "ty: " D.<+> D.align (ppr retTy) D.<+> D.align (ppr expectedTy)
--        --               D.<$> D.text "ss (for c):" D.<+> D.align (pprMap $ M.fromList mp)) $         
--        return (ubind, lbind) 
--        where
--          inferApp (ty, ubind, lbind) p = do 
--            (argTy, resTy) <- ensureFunTy (location p) ty
--            (ubind', lbind') <- checkPatTy p argTy 
--            return (resTy, ubind'++ubind, lbind' ++ lbind)

  
  
