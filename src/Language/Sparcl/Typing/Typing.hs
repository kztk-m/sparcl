module Language.Sparcl.Typing.Typing where

import Language.Sparcl.Typing.TC
import Language.Sparcl.Untyped.Desugar.Syntax

import Control.Monad.Except
import qualified Data.Map as M 

import qualified Text.PrettyPrint.ANSI.Leijen as D
import Language.Sparcl.Pretty

import Data.List ((\\))

import qualified Data.Graph as G

-- import Debug.Trace 

checkUnificationError :: MonadTypeCheck m => SrcSpan -> Ty -> Ty -> m a -> m a
checkUnificationError loc ty1 ty2 e = do
  catchError e $ \d -> do 
      ty1' <- zonkType ty1
      ty2' <- zonkType ty2
      throwError $ ppr loc D.<$> (D.align $ D.nest 2 $ 
                                  D.vsep [D.text "Type error",
                                          D.nest 2 $ D.hsep [D.text "Expected:", D.align $ ppr ty2'],
                                          D.nest 2 $ D.hsep [D.text "Inferred:", D.align $ ppr ty1'] ])
                   D.<$> D.text "Detail:" D.<+> d


tryUnify :: MonadTypeCheck m => SrcSpan -> Ty -> Ty -> m () 
tryUnify loc ty1 ty2 =
  checkUnificationError loc ty1 ty2 $ unify ty1 ty2 

atExp :: MonadTypeCheck m => m a -> Exp -> m a
atExp m e =
  catchError m $ \doc ->
    throwError $ doc D.<$>
                 D.nest 2 (D.text "when checking expression:"
                           D.</> ppr e)

tryUnifyE :: MonadTypeCheck m => SrcSpan -> Exp -> Ty -> Ty -> m ()
tryUnifyE loc e ty1 ty2 =
  tryUnify loc ty1 ty2 `atExp` e 

instantiate :: MonadTypeCheck m => PolyTy -> m MonoTy
instantiate (TyForAll ts t) = do
  ms <- mapM (const $ newMetaTy NoLoc) ts
  return $ substTy (zip ts ms) t
instantiate t = return t 

instPoly :: MonadTypeCheck m => SrcSpan -> PolyTy -> BodyTy -> m () 
instPoly loc polyTy expectedTy = do  
  t <- instantiate polyTy
  -- trace (show $ D.hsep [ppr polyTy, D.text "-->", D.align (ppr t)]) $
  tryUnify loc t expectedTy 
inferTy :: MonadTypeCheck m => Loc Exp -> m BodyTy
inferTy (Loc loc e) = go e
  where
    go (Sig e ty) = do 
      checkTy e ty
      return ty
    go e = do 
      ty <- newMetaTy NoLoc
      checkTy (Loc loc e) ty
      return ty 

ensureFunTy :: MonadTypeCheck m => SrcSpan -> MonoTy -> m (MonoTy, MonoTy)
ensureFunTy loc ty = do
  argTy <- newMetaTy NoLoc
  resTy <- newMetaTy NoLoc 
  tryUnify loc ty (argTy -@ resTy)
  return (argTy, resTy) 

ensureBangTy :: MonadTypeCheck m => SrcSpan -> MonoTy -> m MonoTy
ensureBangTy loc ty = do
  argTy <- newMetaTy NoLoc
  tryUnify loc ty (bangTy argTy)
  return argTy 

ensureRevTy :: MonadTypeCheck m => SrcSpan -> MonoTy -> m MonoTy
ensureRevTy loc ty = do
  argTy <- newMetaTy NoLoc
  tryUnify loc ty (revTy argTy)
  return argTy 

ensurePairTy :: MonadTypeCheck m => SrcSpan -> MonoTy -> m (MonoTy, MonoTy)
ensurePairTy loc ty = do
  fstTy <- newMetaTy NoLoc
  sndTy <- newMetaTy NoLoc
  tryUnify loc ty (TyCon (nameTyTuple 2) [fstTy, sndTy])
  return (fstTy, sndTy) 
                  
checkTy :: MonadTypeCheck m => Loc Exp -> BodyTy -> m ()
checkTy (Loc loc exp) expectedTy = go exp
  where
    go (Var x) = do
      tyOfX <- askType loc x `atExp` exp 
      instPoly loc tyOfX expectedTy `atExp` exp 

    go (Lit l) = case l of
      LitInt _ ->
        tryUnifyE loc exp (TyCon nameTyInt []) expectedTy
      LitChar _ ->
        tryUnifyE loc exp (TyCon nameTyChar []) expectedTy
      LitDouble _ ->
        tryUnifyE loc exp (TyCon nameTyDouble []) expectedTy         

    go (Abs x e) = do
      (argTy, resTy) <- ensureFunTy loc expectedTy `atExp` exp
      (withLVar x argTy $ checkTy e resTy) `atExp` exp 
        
    go (App e1 e2) = do
      ty1 <- inferTy e1
      (argTy, resTy) <- ensureFunTy (location e1) ty1 `atExp` (unLoc e1)
      checkTy e2 argTy
      tryUnifyE loc (unLoc e2) resTy expectedTy 

    go (Con c es) = do
      tyOfC <- instantiate =<< askType loc c
      retTy <- foldM inferApp tyOfC es
      tryUnifyE loc exp retTy expectedTy
        where
          inferApp ty e = do 
            (argTy, resTy) <- ensureFunTy (location e) ty
            checkTy e argTy
            return resTy 

    go (Bang e) = do
      ty <- ensureBangTy loc expectedTy
      withoutLinear $ checkTy e ty

    go (Case e alts) = do
      tyPat <- newMetaTy NoLoc
      checkTy e tyPat 
      checkAltsTy alts tyPat expectedTy

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
      checkTy e1 expectedTy1
      checkTy e2 expectedTy2 
  
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

      tryUnifyE loc exp tyA' tyA
      tryUnifyE loc exp tyB' tyB 
      
      checkTy e (bangTy $ revTy tyA -@ revTy tyB)
        
    go (Sig e ty) = do
      ty' <- instantiate ty
      tryUnifyE loc exp ty' ty
      checkTy e ty'


    go (RCon c es) = do
      tyOfC <- fmap addRev . instantiate =<< askType loc c
      retTy <- foldM inferApp tyOfC es
      tryUnifyE loc exp retTy expectedTy
        where
          inferApp ty e = do 
            (argTy, resTy) <- ensureFunTy (location e) ty
            checkTy e argTy
            return resTy

          addRev (TyCon t [t1,t2]) | t == nameTyLArr = TyCon t [revTy t1, addRev t2]
          addRev t                                   = revTy t 
                                     
    go (RCase e ralts) = do
      tyPat <- newMetaTy NoLoc
      checkTy e (revTy tyPat)
      ty <- ensureBangTy loc expectedTy `atExp` exp
      checkRAltsTy ralts tyPat ty 
      
    -- e1 : rev a   
    -- e2 : !a -> rev b
    -- ----------------
    -- pin e1 e2 : rev (a, b)

    go (RPin e1 e2) = do
      tyAB <- ensureRevTy loc expectedTy `atExp` exp
      (tyA, tyB) <- ensurePairTy loc tyAB `atExp` exp 

      checkTy e1 (revTy tyA)
      checkTy e2 (bangTy tyA -@ revTy tyB) 

    go (Let decls e) = do
      bind <- inferDecls decls 
      withUVars bind $ checkTy e expectedTy

inferMutual :: MonadTypeCheck m => [LDecl] -> m [(Name, PolyTy)]
inferMutual decls = do
  let nes = [ (n,e) | Loc _ (DDef n _ e) <- decls ]
  let ns  = map fst nes 
  let sigMap = M.fromList [ (n, t) | Loc _ (DDef n (Just t) _) <- decls ]

  tys <- mapM (\n -> case M.lookup n sigMap of
                       Just t  -> return t
                       Nothing -> newMetaTy NoLoc) ns

  nts0 <- withUVars (zip ns tys) $ forM decls $ \(Loc loc (DDef n _ e)) -> do 
    ty  <- inferTy e              -- type of e 
    tyE <- askType (location e) (BName n) -- type of n in the environment 
    when (not $ M.member n sigMap) $
      -- Defer unification if a declaration comes with a signature because
      -- the signature can be a polytype while unification targets monotypes. 
      tryUnify (location e) ty tyE
    return (n, loc, ty) 

  envMetaVars <- getMetaTyVarsInEnv

  nts1 <- forM nts0 $ \(n, loc, t) -> do 
    tt <- zonkType t 
    let mvs = metaTyVars [tt]
    polyTy <- quantify (mvs \\ envMetaVars) tt 
    
    case M.lookup n sigMap of
      Nothing    -> return (n, t)
      Just sigTy -> do 
        checkMoreGeneral loc polyTy sigTy
        return (n, sigTy) 

  return nts1

inferDecls :: MonadTypeCheck m => [LDecl] -> m [(Name, PolyTy)]
inferDecls decls = do
  let declss = map unSCC (G.stronglyConnComp graph)
  foldr (\ds m -> do 
            bind <- inferMutual ds
            withUVars bind $ fmap (bind ++) m ) (return []) declss    
  where
    unSCC (G.AcyclicSCC x) = [x]
    unSCC (G.CyclicSCC xs) = xs

    graph = [ (decl, n, freeBVars e) | decl@(Loc _ (DDef n _ e)) <- decls ]
    
  

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
    typeError $ D.group $ D.cat [ D.text "The inferred type",
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
    binders (TySyn ty _) = binders ty
    binders (TyMetaV _)  = []
    
    usedBinders = binders ty
    newBinders = take (length mvs) $ allFancyBinders \\ usedBinders

allFancyBinders :: [TyVar]
allFancyBinders = map (BoundTv . NormalName) $
  [ [x] | x <- ['a'..'z'] ] ++
  [ x : show i | i <- [1::Integer ..], x <- ['a'..'z'] ] 


checkAltsTy :: MonadTypeCheck m => [ (Loc Pat, Loc Exp) ] -> MonoTy -> BodyTy -> m ()
checkAltsTy [] _ _ = return ()
checkAltsTy ((p,e):alts) pty bty = do
  (ubinds, lbinds) <- checkPatTy p pty
  withLVars lbinds $
   withUVars ubinds $
    checkTy e bty
  checkAltsTy alts pty bty 

checkRAltsTy :: MonadTypeCheck m => [ (Loc Pat, Loc Exp, Loc Exp) ] -> MonoTy -> BodyTy -> m ()
checkRAltsTy [] _ _ = return ()
checkRAltsTy ((p,e,e'):ralts) pty bty = do
  -- the top level "rev" are already removed in pty and bty
  (ubinds, lbinds) <- checkPatTy p pty
  case ubinds of
    (_:_) ->
      typeError $ D.hsep [ ppr (location p), D.text "Patterns in reversible computation cannot bind unrestricted variable." ]
    _ -> do 
      withLVars [ (x, revTy t) | (x, t) <- lbinds ] $
        checkTy e (revTy bty) 
      checkTy e' (bangTy (bangTy bty -@ boolTy))
      checkRAltsTy ralts pty bty 

checkPatTy :: MonadTypeCheck m => Loc Pat -> MonoTy -> m ( [(Name, MonoTy)], [(Name,MonoTy)] )
checkPatTy (Loc loc p) expectedTy = go p
  where
     go (PVar x) = return ([], [(x,expectedTy)])
     go (PBang p) = do
       ty <- ensureBangTy loc expectedTy  
       (ubind, lbind) <- checkPatTy p ty
       return $ (ubind ++ lbind, [])
     go (PCon c ps) = do
       tyOfC <- instantiate =<< askType loc c
       (retTy, ubind, lbind) <- foldM inferApp (tyOfC, [], []) ps
       tryUnify loc retTy expectedTy
       return (ubind, lbind) 
       where
         inferApp (ty, ubind, lbind) p = do 
           (argTy, resTy) <- ensureFunTy (location p) ty
           (ubind', lbind') <- checkPatTy p argTy 
           return (resTy, ubind'++ubind, lbind' ++ lbind)

  
  
