{-# LANGUAGE ViewPatterns #-}
module Language.Sparcl.Typing.Typing where

import Data.Void
import Control.Monad.Except
import Control.Monad.Writer
import qualified Data.Map as M 
import qualified Data.Map.Merge.Lazy as M 

import qualified Data.Graph as G

import Language.Sparcl.Typing.TCMonad
import Language.Sparcl.Typing.Type
import Language.Sparcl.SrcLoc 
import Language.Sparcl.Surface.Syntax hiding (Ty(..), TConstraint(..))
import Language.Sparcl.Pass
import Language.Sparcl.Literal
import Language.Sparcl.Name
import Language.Sparcl.Multiplicity

import Language.Sparcl.Algorithm.SAT as SAT 

import qualified Language.Sparcl.Core.Syntax as C (DDecl(..), TDecl(..)) 

import qualified Language.Sparcl.Surface.Syntax as S



import Language.Sparcl.Pretty as D hiding ((<$>))

-- import Data.Maybe (isNothing)
import Data.List (nub, partition, (\\))

-- import Control.Exception (evaluate)
-- import Debug.Trace 


-- TODO: Implement kind checking
ty2ty :: S.LTy 'Renaming -> Ty
ty2ty (Loc _ ty) = go ty
  where
    go (S.TVar x)      = TyVar (BoundTv x)
    go (S.TCon c ts)   = TyCon c $ map ty2ty ts
    go (S.TForall x t) = gatherBoundTv [BoundTv x] t
    go (S.TMult m)     = TyMult m
    go t@(S.TQual _ _) =
      let (t', cs') = gatherConstraints t
      in TyForAll [] $ TyQual cs' t'

    gatherBoundTv xs (unLoc -> S.TForall y t) = gatherBoundTv (BoundTv y:xs) t
    gatherBoundTv xs t                        = let (t', cs) = gatherConstraintsL t
                                                in TyForAll (reverse xs) $ TyQual cs t' 

    gatherConstraintsL = gatherConstraints . unLoc 

    gatherConstraints (S.TVar x)      = (TyVar (BoundTv x), [])
    gatherConstraints (S.TCon c ts)   = let tcs = map gatherConstraintsL ts
                                      in (TyCon c (map fst tcs), concatMap snd tcs)
    gatherConstraints (S.TForall x t) = (gatherBoundTv [BoundTv x] t, [])
    gatherConstraints (S.TQual cs t)  = let (t', cs')  = gatherConstraintsL t
                                        in (t', map c2c cs ++ cs')
    gatherConstraints (S.TMult m)     = (TyMult m, [])

    c2c (S.MSub t1 t2)      = msub (go $ unLoc t1) (go $ unLoc t2)
    c2c (S.MEqMax t1 t2 t3) = MEqMax (go $ unLoc t1) (go $ unLoc t2) (go $ unLoc t3) 

msub :: Ty -> Ty -> TyConstraint
msub t1 t2 = MEqMax t2 t1 t2 
 

tryUnify :: MonadTypeCheck m => Ty -> Ty -> m ()
tryUnify t1 t2 = whenChecking (CheckingEquality t1 t2) $ unify t1 t2 

-- tryUnify :: MonadTypeCheck m => SrcSpan -> Ty -> Ty -> m () 
-- tryUnify loc ty1 ty2 =
--   catchError (atLoc loc $ unify ty1 ty2) $ \(TypeError loc' ctxt reason) ->
--     case reason of
--       UnMatchTy ty3 ty4 -> do
--         ty1' <- zonkType ty1
--         ty2' <- zonkType ty2
--         -- mp   <- M.fromList <$> traverseTy ty1'
--         -- trace (show $ D.text "Snap shot" D.<+> D.align (pprMap mp)) $
--         throwError $ TypeError loc' ctxt (UnMatchTyD ty1' ty2' ty3 ty4)  
--       _ ->
--         throwError $ TypeError loc' ctxt reason

--   -- where

-- traverseTys :: (Traversable t, MonadTypeCheck f) => t Ty -> f [(Int, Ty)]
-- traverseTys ts = concat <$> mapM traverseTy ts

-- traverseTy :: MonadTypeCheck f => Ty -> f [(Int, Ty)]
-- traverseTy (TyCon _ ts) = traverseTys ts
-- traverseTy (TyVar _)    = return []
-- traverseTy (TyMetaV tv@(MetaTyVar i _)) = do
--   res <- readTyVar tv
--   case res of
--     Nothing -> return []
--     Just ty -> ((i, ty) :) <$> traverseTy ty
-- traverseTy (TyForAll _ t) = traverseTy t
-- traverseTy (TySyn _ ty)   = traverseTy ty 


-- -- atExp :: MonadTypeCheck m => m a -> Exp -> m a
-- -- atExp m e =
-- --   catchError m $ \doc ->
-- --     throwError $ doc D.<$>
-- --                  D.nest 2 (D.text "when checking expression:"
-- --                            D.</> ppr e)

-- -- tryUnifyE :: MonadTypeCheck m => SrcSpan -> Exp -> Ty -> Ty -> m ()
-- -- tryUnifyE loc e ty1 ty2 =
-- --   tryUnify loc ty1 ty2 `atExp` e 

instantiate :: MonadTypeCheck m => PolyTy -> m ([TyConstraint], MonoTy) 
instantiate (TyForAll ts qt) = do
  ms <- mapM (const newMetaTy) ts
  let subs = zip ts ms 
  let TyQual cs' t' = substTyQ subs qt 
  return (cs', t')
instantiate t = return ([], t) 

-- instPoly :: MonadTypeCheck m => SrcSpan -> PolyTy -> BodyTy -> m () 
-- instPoly loc polyTy expectedTy = do  
--   t <- instantiate polyTy
--   tryUnify loc t expectedTy

-- inferExp :: MonadTypeCheck m => LExp 'Renaming -> m (LExp 'TypeCheck, PolyTy)
-- inferExp expr = do
--   (expr', ty) <- inferTy expr
--   ty' <- zonkType ty
--   envMetaVars <- getMetaTyVarsInEnv
--   let mvs = metaTyVars [ty']
--   polyTy <- quantify (mvs \\ envMetaVars) ty'
--   trace (prettyShow ty' ++ " --> " ++ prettyShow polyTy) $ return (expr', polyTy) 
  
  
-- inferTy :: MonadTypeCheck m => LExp 'Renaming -> m (LExp 'TypeCheck, BodyTy)
-- inferTy (Loc loc expr) = go expr
--   where
--     go (Sig e tySyn) = do
--       let ty = ty2ty tySyn
--       e' <- checkTy e (ty2ty tySyn)
--       return (e', ty) 
--     go e = do 
--       ty <- newMetaTy
--       e' <- checkTy (Loc loc e) ty
--       return (e', ty) 

-- ensureFunTy :: MonadTypeCheck m => SrcSpan -> MonoTy -> m (MonoTy, MonoTy)
-- ensureFunTy loc ty = do
--   argTy <- newMetaTy 
--   resTy <- newMetaTy 
--   tryUnify loc (argTy -@ resTy) ty
--   return (argTy, resTy) 

-- ensureBangTy :: MonadTypeCheck m => SrcSpan -> MonoTy -> m MonoTy
-- ensureBangTy loc ty = do
--   argTy <- newMetaTy 
--   tryUnify loc (bangTy argTy) ty
--   return argTy 

ensureRevTy :: MonadTypeCheck m => MonoTy -> m MonoTy
ensureRevTy ty = do
  argTy <- newMetaTy 
  tryUnify (revTy argTy) ty
  return argTy 

-- ensurePairTy :: MonadTypeCheck m => SrcSpan -> MonoTy -> m (MonoTy, MonoTy)
-- ensurePairTy loc ty = do
--   fstTy <- newMetaTy 
--   sndTy <- newMetaTy 
--   tryUnify loc (TyCon (nameTyTuple 2) [fstTy, sndTy]) ty
--   return (fstTy, sndTy)

ensureFunTy :: MonadTypeCheck m => MonoTy -> m (MonoTy, MonoTy, MonoTy)
ensureFunTy ty = do
  argTy <- newMetaTy
  m     <- newMetaTy 
  resTy <- newMetaTy 
  tryUnify (TyCon nameTyArr [m, argTy, resTy]) ty 
  return (argTy, m, resTy) 


litTy :: MonadTypeCheck m => Literal -> m MonoTy
litTy (LitInt _)      = return $ TyCon nameTyInt []
litTy (LitChar _)     = return $ TyCon nameTyChar []
litTy (LitDouble _)   = return $ TyCon nameTyDouble []
litTy (LitRational _) = return $ TyCon nameTyRational []

checkPatsTy :: MonadTypeCheck m =>
  [LPat 'Renaming] -> [MultTy] -> [MonoTy] ->
  m ([LPat 'TypeCheck], [(Name,MonoTy,MultTy)], [TyConstraint])
checkPatsTy [] [] [] = return ([], [], [])
checkPatsTy (p:ps) (m:ms) (t:ts) = do
  (ps', bind,  cs)  <- checkPatsTy ps ms ts
  (p',  pbind, pcs) <- checkPatTy p m t
  return (p':ps', pbind ++ bind, pcs ++ cs) 
checkPatsTy _ _ _ = error "Cannot happen."  

checkPatTy :: MonadTypeCheck m =>
              LPat 'Renaming -> MultTy -> MonoTy ->
              m (LPat 'TypeCheck, [(Name, MonoTy, MultTy)], [TyConstraint])
checkPatTy = checkPatTyWork False 

checkPatTyWork ::
  MonadTypeCheck m =>
  Bool -> 
  LPat 'Renaming -> MultTy -> MonoTy ->
  m (LPat 'TypeCheck, [(Name, MonoTy, MultTy)], [TyConstraint])
checkPatTyWork isUnderRev (Loc loc pat) pmult patTy = do
  (pat', bind, cs) <- atLoc loc $ go pat
  return (Loc loc pat', bind, cs) 
  where
    go (PVar x) =
      return (PVar (x, patTy), [(x,patTy, pmult)],  [])

    -- TODO: to be removed 
    go (PBang p) = do
      unify pmult (TyMult Omega)
      (p', bind, cs) <- checkPatTyWork isUnderRev p (TyMult Omega) patTy
      return (PBang p', bind, cs) 

    go (PCon c ps) = do
      (cs, tyOfC) <- instantiate =<< askType loc c
      (ps', retTy, bind, csR) <- foldM inferApp ([], tyOfC, [], cs) ps
      tryUnify retTy patTy
      retTy' <- zonkType retTy
      case retTy' of
        TyCon n [_,_,_] | n == nameTyArr ->
          reportError $ Other $ text "Constructor" <+> ppr n <+> text "must be fully applied."
        _ ->
          return ()
      return (PCon (c, tyOfC) (reverse ps'), bind, csR)
        where
          inferApp (ps', ty, bind, cs) p = do
            (argTy, m, resTy) <- atLoc (location p) $ ensureFunTy ty
            (mm, cm) <- maxMult m pmult 
            (p', bind', cs') <- checkPatTyWork isUnderRev p mm argTy
            return (p':ps', resTy, bind'++bind, cm ++ cs'++cs)

          maxMult m1 m2 = do
            mm <- newMetaTy
            return (mm, [MEqMax mm m1 m2])
            
            
          
          
    go (PREV p) = do
      when isUnderRev $ (atLoc $ location p) $ reportError $ Other $ text "rev patterns cannot be nested."
          
      ty <- ensureRevTy patTy
      (p', bind, cs) <- checkPatTyWork True p pmult ty
      let bind' = map (\(x,t,m) -> (x, revTy t,m)) bind 

      -- forM_ xqs $ \(_, q) ->
      --   -- TODO: Add good error messages.
      --   unify q (TyMult One) 
      
      return (PREV p', bind', cs)

    go (PWild x) = do -- this is only possible when multp is omega
      tryUnify pmult (TyMult Omega) 
      (Loc _ (PVar x'), _bind, cs) <- checkPatTyWork isUnderRev (noLoc $ PVar x) (TyMult Omega) patTy
      return (PWild x', [], cs)
       
      -- go (PVar x) =
      --   return (PVar (x,expectedTy), [], [(x,expectedTy)])
        
      -- go (PBang p) = do
      --   ty <- ensureBangTy loc expectedTy
      --   (p', ubind, lbind) <- checkPatTyWork isUnderRev True p ty
      --   return (PBang p', ubind ++ lbind, [])
        
      -- go (PCon c ps) = do
      --  tyOfC <- instantiate =<< askType loc c
      --  (ps', retTy, ubind, lbind) <- foldM inferApp ([], tyOfC, [], []) ps
      --  tryUnify loc retTy expectedTy
      --  retTy' <- zonkType retTy
      --  case retTy' of
      --    TyCon n [_,_] | n == nameTyLArr ->
      --      atLoc loc $ typeError $ Other $ text "Constructor" <+> ppr n <+> text "must be fully applied."
      --    _ -> 
      --  -- mp <- traverseTys [tyOfC, retTy, expectedTy]
      --  -- trace (show $ D.text "ty: " D.<+> D.align (ppr retTy) D.<+> D.align (ppr expectedTy)
      --  --               D.<$> D.text "ss (for c):" D.<+> D.align (pprMap $ M.fromList mp)) $         
      --      return (PCon (c, tyOfC) (reverse ps'), ubind, lbind) 
      --  where
      --    inferApp (ps', ty, ubind, lbind) p = do 
      --      (argTy, resTy) <- ensureFunTy (location p) ty
      --      (p', ubind', lbind') <- checkPatTyWork isUnderRev isUnderBang p argTy 
      --      return (p':ps', resTy, ubind'++ubind, lbind' ++ lbind)

      -- go (PREV p)
      --   | isUnderRev = atLoc loc $ typeError $ Other $ text "rev patterns cannot be nested."
      --   | otherwise = do
      --       ty <- ensureRevTy loc expectedTy
      --       (p', ubind, lbind) <- checkPatTyWork True isUnderBang p ty
      --       when (not $ null ubind) $
      --         atLoc loc $ typeError $ Other $ text "rev patterns cannot contain !."
      --       let ubind' = map (\(x, t) -> (x, revTy t)) ubind
      --       let lbind' = map (\(x, t) -> (x, revTy t)) lbind
      --       return (PREV p', ubind', lbind')

      -- go (PWild x)
      --   | isUnderBang = do
      --       (PVar x', ubind, lbind) <- go (PVar x)
      --       return (PWild x', ubind, lbind)
      --   | otherwise = do 
      --       (PBang (Loc _ (PVar x')), ubind, lbind) <- go (PBang (noLoc $ PVar x))
      --       return (PWild x', ubind, lbind) 


simplifyConstraints :: MonadTypeCheck m => [TyConstraint] -> m [TyConstraint]
simplifyConstraints constrs = whenChecking (CheckingConstraint constrs) $ go constrs
  where
    go cs = do
      cs' <- propagateConstantsToFixedpoint cs
      --  liftIO $ putStrLn $ ("CP: " ++ show (hsep [ppr xs, text "-->>", ppr ys]))
      isEffective <- loopToEquiv cs'
      if length cs' < length cs || isEffective
        then go cs'
        else return cs'
  

-- | The function yield equality constraints by detecting loops in the dependency. 
--   For example, from the constraint a = max b c and b = max a d, we can conclude
--   a = b as we have b <= a, c <= a, a <= b, d <= b from the constraint.
--
--   The function returns true if it yields at least one equality constraint. 
--   
loopToEquiv :: forall m. MonadTypeCheck m => [TyConstraint] -> m Bool
loopToEquiv constraints = do
  sccs <- makeSCC constraints
  -- liftIO $ print $ red $ text "CS:" <+> ppr constraints
  -- liftIO $ print $ red $ text "SCC" <+> (align $ vcat $ map (\case G.AcyclicSCC x -> text "Acyc" <+> ppr x
  --                                                                  G.CyclicSCC x  -> text "Cyc " <+> ppr x) sccs)
  isEffective <- foldM procSCCs False sccs
  return isEffective
  where
    procSCCs :: Bool -> G.SCC Ty -> m Bool
    procSCCs  isE (G.AcyclicSCC _)  = return isE
    procSCCs  isE (G.CyclicSCC [_]) = return isE 
    procSCCs _isE (G.CyclicSCC xs)  = 
      equate xs >> return True

    equate []       = error "Cannot happen." 
    equate (ty:tys) = equate' tys
      where
        equate' []       = return ()
        equate' (ty':ts) = unify ty ty' >> equate' ts 
          
                      
    
    makeSCC :: [TyConstraint] -> m [G.SCC Ty]
    makeSCC xs = do
      t <- makeLeMap xs
      return $ G.stronglyConnComp $ map (\(k,vs) -> (k,k,vs)) $ M.toList t

    makeLeMap :: [TyConstraint] -> m (M.Map Ty [Ty])
    makeLeMap [] = return M.empty
    makeLeMap (MEqMax t1 t2 t3:cs) = do
      t <- makeLeMap cs
      t1' <- zonkType t1
      t2' <- zonkType t2
      t3' <- zonkType t3
      return $ M.insertWith (++) t2' [t1'] $ M.insertWith (++) t3' [t1'] t 
        
            
    
    
propagateConstantsToFixedpoint :: MonadTypeCheck m => [TyConstraint] -> m [TyConstraint]
propagateConstantsToFixedpoint xs = do 
  ys <- propagateConstants xs
  if length xs > length ys
    then propagateConstantsToFixedpoint ys
    else return ys
    
propagateConstants :: MonadTypeCheck m => [TyConstraint] -> m [TyConstraint]
propagateConstants [] = return []
propagateConstants (MEqMax t1 t2 t3:cs) = do
  t1' <- zonkType t1 
  t2' <- zonkType t2
  t3' <- zonkType t3
  case t1' of
    TyMult One   -> do
      unify t2' (TyMult One) -- 1 = max a b implies a = b = 1
      unify t3' (TyMult One) --
      propagateConstants cs
    _ ->
      case tryComputeMax t2' t3' of
        Just t  -> 
          unify t1' t >> propagateConstants cs
        Nothing -> (MEqMax t1' t2' t3':) <$> propagateConstants cs 
  where
    tryComputeMax :: MultTy -> MultTy -> Maybe MultTy 
    tryComputeMax (TyMult Omega) _ = Just $ TyMult Omega
    tryComputeMax (TyMult One)   ty = Just ty
    tryComputeMax _ty            (TyMult Omega) = Just $ TyMult Omega
    tryComputeMax ty              (TyMult One)   = Just ty
    tryComputeMax ty1            ty2 =
      if ty1 == ty2 then Just ty1
      else               Nothing 
        



  

constrainVars :: MonadTypeCheck m => [(Name, MultTy)] -> UseMap -> m [TyConstraint]
constrainVars []          _ = return []
constrainVars ((x,q):xqs) m = do
  let dx = hsep [ text "linearity of", dquotes (ppr x) <> text ", but it is used more than once" ] 
  case toTy <$> M.lookup x m of
    Just t -> do 
      t' <- zonkType t 
      case t' of
        TyMult Omega -> do
          whenChecking (OtherContext dx) $ unify q (TyMult Omega)
          constrainVars xqs m
        TyMult One   -> 
          constrainVars xqs m
        TyMetaV pp -> do 
          -- unify q (TyMetaV pp) 
          -- cs <- constrainVars xqs m
          -- return cs
          cs <- constrainVars xqs m 
          return $ msub (TyMetaV pp) q : cs
        _ ->
          error $ "Kind mismatch: expected multiplicity, but received: " ++ show (ppr t')
    Nothing               -> do 
      whenChecking (OtherContext dx) $ unify q (TyMult Omega)
      constrainVars xqs m 
    where
      toTy (MulConst mc) = TyMult mc
      toTy (MulVar   qq) = TyMetaV qq

-- boundLower :: MultTy -> UseMap -> [TyConstraint]
-- boundLower m = go . M.elems
--   where
--     go [] = []
--     go (MulConst c:ts) = MSub m (TyMult c)  : go ts
--     go (MulVar   x:ts) = MSub m (TyMetaV x) : go ts 

maxUseMap :: MonadTypeCheck m => UseMap -> UseMap -> m (UseMap, [TyConstraint])
maxUseMap m1 m2 =
  runWriterT $ M.mergeA
                    (M.mapMissing $ \_ _ -> MulConst Omega)
                    (M.mapMissing $ \_ _ -> MulConst Omega)
                    (M.zipWithAMatched $ \_ x y -> case x of
                        MulConst One   -> pure y
                        MulConst Omega -> pure (MulConst Omega)
                        MulVar p -> case y of
                                      MulConst One   -> pure (MulVar p)
                                      MulConst Omega -> pure (MulConst Omega)
                                      MulVar q       -> do
                                        r <- lift newMetaTyVar
                                        tell [MEqMax (TyMetaV r) (TyMetaV p) (TyMetaV q)]
                                        return (MulVar r))
                    m1 m2 
                        
                          

raiseUse :: MonadTypeCheck m => MultTy -> UseMap -> m (UseMap, [TyConstraint])
raiseUse m = runWriterT . traverse f
  where
    f :: MonadTypeCheck m => Mul -> WriterT [TyConstraint] m Mul
    f (MulConst One) =
      case m of
        TyMult  c -> pure (MulConst c)
        TyMetaV x -> pure (MulVar   x)
        _         -> error "Kind error."
    f (MulConst Omega) = pure (MulConst Omega)
    f (MulVar   q)     = do
      r <- lift $ newMetaTyVar
      tell [MEqMax (TyMetaV r) m (TyMetaV q) ]
      return (MulVar r)
      

-- TODO: sig-expression is buggy.

inferTy :: MonadTypeCheck m => LExp 'Renaming -> m (LExp 'TypeCheck, BodyTy, UseMap, [TyConstraint])
inferTy (Loc loc expr) = go expr
  where
    -- go (Sig e tySyn) = do
    --   let sigTy = ty2ty tySyn
    --   (e', polyTy, umap, cs) <- inferPolyTy e  
    --   tryCheckMoreGeneral loc polyTy sigTy
    --   (cs', ty') <- instantiate sigTy
    --   -- (e', umap, cs) <- checkTy e ty'
    --   return (e', ty', umap, cs'++cs) 
    go e = do 
      ty <- newMetaTy
      (e', umap, cs) <- checkTy (Loc loc e) ty
      return (e', ty, umap, cs) 


checkTyM :: MonadTypeCheck m => LExp 'Renaming -> BodyTy -> MultTy -> m (LExp 'TypeCheck, UseMap, [TyConstraint])
checkTyM lexp ty m = do
  (lexp', umap, cs) <- checkTy lexp ty
  (umap', cs') <- raiseUse m umap 
  return (lexp', umap', cs' ++ cs)

checkTy :: MonadTypeCheck m => LExp 'Renaming -> BodyTy -> m (LExp 'TypeCheck, UseMap, [TyConstraint])
checkTy lexp@(Loc loc expr) expectedTy = fmap (first3 $ Loc loc) $ atLoc loc $ atExp lexp $ go expr
  where
    first3 f (a,b,c) = (f a, b, c)
    
    go (Var x) = do
      tyOfX <- askType loc x
      (cs, t) <- instantiate tyOfX 
      tryUnify t expectedTy
      return (Var (x, tyOfX), M.singleton x (MulConst One), cs)

    go (Lit l) = do
      ty <- litTy l
      tryUnify ty expectedTy 
      return (Lit l, M.empty, []) 
    
    go (Abs pats e) = do
      -- multiplicity of arguments 
      qs <- mapM (const newMetaTy) pats
      ts <- mapM (const newMetaTy) pats

      (pats', bind, csPat) <- checkPatsTy pats qs ts
      retTy <- newMetaTy
      (e', umap, cs) <- withMultVars qs $ withVars bind $ checkTy e retTy

      let xqs = map (\(x,_,q) -> (x,q)) bind 

      tryUnify (foldr (uncurry tyarr) retTy $ zip qs ts) expectedTy
      csVars <- constrainVars xqs umap 
      
      return (Abs pats' e', foldr M.delete umap (map fst xqs), csVars ++ cs ++ csPat)
               
    go (App e1 e2) = do
      (e1', ty1, umap1, cs1) <- inferTy e1
      (argTy, m, resTy) <- atExp e1 $ atLoc (location e1) $ ensureFunTy ty1
      (e2', umap2, cs2) <- checkTyM e2 argTy m 

      tryUnify resTy expectedTy 

      return (App e1' e2', mergeUseMap umap1 umap2, cs1 ++ cs2)
      
    go (Con c) = do
      tyOfC <- askType loc c
      (cs, t) <- instantiate tyOfC
      tryUnify t expectedTy 
      return (Con (c, t), M.empty, cs)

    -- TODO: to be removed 
    go (Bang e) = do
      (e', umap, cs) <- checkTy e expectedTy
      (umap', cs') <- raiseUse (TyMult Omega) umap 
      return $ (Bang e', umap', cs' ++ cs)

    go (Sig e tySyn) = do
      let sigTy = ty2ty tySyn
      (e', polyTy, umap, csO) <- inferPolyTy False e  
      tryCheckMoreGeneral loc polyTy sigTy
      (csI, monoTy) <- instantiate sigTy

      -- liftIO $ print $ red $ text "CSI:" <+> ppr csI
      -- liftIO $ print $ red $ text "CSO:" <+> ppr csO 

      tryUnify monoTy expectedTy
      return (unLoc e', umap, csI ++ csO) 
      
      -- let ty = ty2ty tySyn       
      -- (cs, ty') <- instantiate ty
      -- tryUnify ty' expectedTy
      -- (e', umap, cs') <- checkTy e ty'
      -- return (unLoc e', umap, cs ++ cs')

    go Lift = do
      tyA <- newMetaTy
      tyB <- newMetaTy 
      tryUnify (liftTy tyA tyB) expectedTy
      return (Lift, M.empty, [])
      where
        liftTy tyA tyB =
          (tyA *-> tyB) *-> (tyB *-> tyA) *-> (revTy tyA -@ revTy tyB)

    go Unlift = do
      tyA <- newMetaTy
      tyB <- newMetaTy
      tryUnify (unliftTy tyA tyB) expectedTy
      return (Unlift, M.empty, [])
      where
        unliftTy tyA tyB =
          (revTy tyA -@ revTy tyB) *-> tupleTy [tyA *-> tyB, tyB *-> tyA]

    go RPin = do
      tyA <- newMetaTy
      tyB <- newMetaTy
      tryUnify (pinTy tyA tyB) expectedTy
      return (RPin, M.empty, [])
        where
          pinTy tyA tyB =
            revTy tyA *-@ (tyA *-> revTy tyB) *-@ revTy (tupleTy [tyA, tyB])

    go (Parens e) = do
      (e', umap, cs) <- checkTy e expectedTy
      return (Parens e', umap, cs)

    go (Op op e1 e2) = do
      (csOp, tyOfOp) <- instantiate =<< askType loc op
      ty1    <- newMetaTy
      ty2    <- newMetaTy
      m1     <- newMetaTy
      m2     <- newMetaTy

      tryUnify tyOfOp (TyCon nameTyArr [m1, ty1, TyCon nameTyArr [m2, ty2, expectedTy]])
      (e1', umap1, cs1) <- withMultVars [m1,m2] $ checkTyM e1 ty1 m1
      (e2', umap2, cs2) <- withMultVars [m1,m2] $ checkTyM e2 ty2 m2 
      return (Op (op, tyOfOp) e1' e2', mergeUseMap umap1 umap2, csOp ++ cs1 ++ cs2) 

    go (RCon c) = do
      (csOp, tyOfC_) <- instantiate =<< askType loc c
      let tyOfC = addRev tyOfC_
      tryUnify tyOfC expectedTy
      return (RCon (c, tyOfC), M.empty, csOp)
        where
          -- FIXME: m must be one 
          addRev (TyCon t [m, t1,t2]) | t == nameTyArr = TyCon t [m, revTy t1, addRev t2]
          addRev t                                     = revTy t 

    go (Let decls e) = do
      (decls', bind, umapLet, csLet) <- inferDecls decls 
      (e', umap, cs)                 <- withUnrestrictedVars bind $ checkTy e expectedTy
      return (Let decls' e', mergeUseMap umap umapLet, cs ++ csLet) 

    go (Case e0 alts) = do
      p <- newMetaTyVar -- multiplicity of `e`
      tyPat <- newMetaTy 
      (e0', umap0, cs0)   <- withMultVar (TyMetaV p) $ checkTyM e0 tyPat (TyMetaV p) 
      (alts', umapA, csA) <- withMultVar (TyMetaV p) $ checkAltsTy alts tyPat p expectedTy 

      return (Case e0' alts', mergeUseMap umap0 umapA, cs0 ++ csA) 

    go (RDO as0 er) = do
      (as0', bind, umap, csAs) <- goAs as0
      let bind' = map (\(x,t,_) -> (x, revTy t, TyMult One)) bind
      let xs = map (\(x,_,_) -> x) bind'
      let xqs = [ (x, TyMult One) | x <- xs ]      

      (er', umapr, csr) <- withVars bind' $ checkTy er expectedTy
      csVars <- constrainVars xqs umapr

      return (RDO as0' er', mergeUseMap umap (foldr M.delete umapr xs), csVars ++ csr ++ csAs)
      where
        goAs [] = return ([], [], M.empty, [])
        goAs ((p,e):as) = do
          tyE <- newMetaTy
          (e', umapE, csE) <- checkTy e (revTy tyE)
          (p', bind, csP) <- checkPatTy p (TyMult Omega) tyE

          let xqs = map (\(x,_,q) -> (x,q)) bind 

          (as', bindAs, umapAs, csAs) <- withVars bind $ goAs as

          csV <- constrainVars xqs umapAs

          return ((p',e'):as', bindAs ++ bind, mergeUseMap (foldr M.delete umapAs $ map fst xqs) umapE, csV ++ csE ++ csP ++ csAs) 
          


    

inferPolyTy :: MonadTypeCheck m => Bool -> LExp 'Renaming -> m (LExp 'TypeCheck, PolyTy, UseMap, [TyConstraint])
inferPolyTy isMultipleUse expr = do
  (expr', ty, umap, cs) <- inferTy expr
  
  (umapM, csM) <- if isMultipleUse then raiseUse (TyMult Omega) umap
                  else return (umap, [])
  
  cs' <- simplifyConstraints (cs ++ csM)
  (csI, csO) <- splitConstraints cs'

  ty' <- zonkTypeQ (TyQual csI ty)
  
  envMetaVars <- getMetaTyVarsInEnv

  -- We cannot generalize variables in umap 
  umapVars <- metaTyVars <$> mapM zonkMetaTyVar [ x | MulVar x <-  M.elems umapM ]

  let mvs = metaTyVarsQ [ty'] 
  polyTy <- quantify (mvs \\ (envMetaVars ++ umapVars)) ty'

  -- liftIO $ print $ red $ text "[inferPolyTy]" <+> ppr ty' <+> text "--->"  <+> ppr polyTy 

  return (expr', polyTy, umapM, csO) 

inferExp :: MonadTypeCheck m => LExp 'Renaming -> m (LExp 'TypeCheck, PolyTy)
inferExp expr = do
  -- ty <- newMetaTy 
  -- (expr', _, cs) <- checkTy expr ty 
  -- cs' <- simplifyConstraints cs 
  -- ty' <- zonkTypeQ (TyQual cs' ty)
  -- envMetaVars <- getMetaTyVarsInEnv
  -- let mvs = metaTyVarsQ [ty']
  -- polyTy <- quantify (mvs \\ envMetaVars) ty'
  -- trace (prettyShow ty' ++ " --> " ++ prettyShow polyTy) $ return (expr', polyTy) 
  (expr', polyTy, _, _) <- inferPolyTy True expr
  return (expr', polyTy) 
  

checkAltsTy ::
  MonadTypeCheck m => [ (LPat 'Renaming, Clause 'Renaming) ] ->
  MonoTy -> MetaTyVar -> BodyTy -> m ([ (LPat 'TypeCheck, Clause 'TypeCheck) ], UseMap, [TyConstraint])
checkAltsTy alts patTy q bodyTy =
  -- parallel $ map checkAltTy alts
  gatherAltUC =<< mapM checkAltTy alts 
  where
    checkAltTy (pat, c) = do
      (pat', bind, csP) <- checkPatTy pat (TyMetaV q) patTy
      (c', umap, cs) <- withVars bind $ checkClauseTy c bodyTy

      let xqs = map (\(x,_,qq) -> (x,qq)) bind 
      csVars <- constrainVars xqs umap 
      return ((pat', c'), foldr M.delete umap (map fst xqs), csVars ++ cs ++ csP)  
    -- checkAltTy (p, c) = do
    --   (p', ubind, lbind) <- checkPatTy p patTy
    --   c' <- withUVars ubind $ withLVars lbind $ checkClauseTy c bodyTy
    --   return (p', c') 

gatherAltUC :: MonadTypeCheck m =>
               [(a,UseMap, [TyConstraint])] ->
               m ([a], UseMap, [TyConstraint])
gatherAltUC []                           = return ([], M.empty, [])
gatherAltUC ((obj,umap,constrs):triples) = go obj umap constrs triples
  where
    go s um cs [] = return ([s], um, cs)
    go s um cs ((s',um',cs'):ts) = do 
      (ss, umR, csR) <- go s' um' cs' ts
      (um2, cs2) <- maxUseMap um umR 
      return (s:ss, um2, cs2 ++ cs ++ csR)
      


      

inferDecls :: MonadTypeCheck m => Decls 'Renaming (LDecl 'Renaming) ->
              m (Decls 'TypeCheck (LDecl 'TypeCheck), [(Name, PolyTy)], UseMap, [TyConstraint])
inferDecls (Decls v _) = absurd v
inferDecls (HDecls _ dss) = do
  (dss', bind , umap, cs) <- go [] dss
  return (HDecls () dss', bind, umap, cs )
  where 
    go bs [] = return ([], bs, M.empty, [])
    go bs (ds:rest) = do
      (ds', bind,  umap,  csLet)  <- inferMutual ds
      (rest', bs', umap', csLet') <- withUnrestrictedVars bind $ go (bind ++ bs) rest
      return (ds':rest', bs', mergeUseMap umap umap', csLet ++ csLet')
    

inferTopDecls ::
  MonadTypeCheck m =>
  Decls 'Renaming (LDecl 'Renaming) ->
  [Loc (Name, [Name], [Loc (CDecl 'Renaming)])] -> 
  [Loc (Name, [Name], LTy 'Renaming)] ->
  m (Decls 'TypeCheck (LDecl 'TypeCheck), [(Name, PolyTy)],
     [C.DDecl Name],
     [C.TDecl Name], 
     TypeTable, SynTable)
inferTopDecls decls dataDecls typeDecls = do
  let dataDecls' = [ C.DDecl n (map BoundTv ns) [ (cn, map ty2ty tys) | Loc _ (CDecl cn tys) <- cdecls ] 
                   | Loc _ (n,ns,cdecls) <- dataDecls ]

  let typeDecls' = [ C.TDecl n (map BoundTv ns) (ty2ty lty) | Loc _ (n, ns, lty) <- typeDecls ]
  
  let synTable = M.fromList $ 
        flip map typeDecls $ \(Loc _ (n, ns, lty)) ->
                               let ty = ty2ty lty
                               in (n, (map BoundTv ns, ty))

        
  let typeTable = M.fromList $
        [ (n, foldr (-@) typeKi (map (const typeKi) ns)) | Loc _ (n, ns, _) <- dataDecls ]
        ++
        [ (cn, TyForAll tvs $ TyQual [] (foldr (-@) (TyCon n $ map TyVar tvs) $ map ty2ty tys)) |
          Loc _ (n, ns, cdecls) <- dataDecls,
          let tvs = map BoundTv ns, 
          Loc _ (CDecl cn tys) <- cdecls ]

  withUnrestrictedVars (M.toList typeTable) $
   withSyns (M.toList synTable) $ do
     (decls', nts, _, _) <- inferDecls decls
     -- liftIO $ putStrLn $ show cs 
     return (decls', nts, dataDecls', typeDecls', typeTable, synTable)


splitConstraints :: MonadTypeCheck m =>
                    [TyConstraint] -> m ([TyConstraint], [TyConstraint])
splitConstraints cs = do
  env <- getMetaTyVarsInEnv
--  liftIO $ print $ blue $ text "MEnv:" <+> ppr env
  cs' <- mapM zonkTypeC cs 
  let (csO, csI) = partition (allIn env) cs'
  return (csI, csO)
    where
      allIn env (MEqMax t1 t2 t3) =
        all (\t -> t `elem` env) $ metaTyVars [t1,t2,t3]


inferMutual :: MonadTypeCheck m =>
               [LDecl 'Renaming] -> m ([LDecl 'TypeCheck], [(Name, PolyTy)], UseMap, [TyConstraint])
inferMutual decls = do
--  let nes = [ (n,e) | Loc _ (DDef n _) <- decls ]
  let ns  = [ n | Loc _ (DDef n _) <- decls ]
  let defs = [ (loc, n, pcs) | Loc loc (DDef n pcs) <- decls ]
  let sigMap = M.fromList [ (n, ty2ty t) | Loc _ (DSig n t) <- decls ]

  tys <- mapM (\n -> case M.lookup n sigMap of
                       Just t  -> return t
                       Nothing -> newMetaTy) ns

  (nts0, umap) <- fmap gatherU $ withUnrestrictedVars (zip ns tys) $ forM defs $ \(loc, n, pcs) -> do
    ty  <- newMetaTy
    qs  <- mapM (const newMetaTy) [1..numPatterns pcs]
    (pcs', umap, cs) <- gatherAltUC =<< mapM (flip (checkTyPC loc qs) ty) pcs 
    tyE <- askType loc n -- type of n in the environment

    when (not $ M.member n sigMap) $ do 
      -- Defer unification if a declaration comes with a signature because
      -- the signature can be a polytype while unification targets monotypes.

      -- ty' <- zonkType ty
      -- tyE' <- zonkType tyE 
      -- liftIO $ putStrLn $ show $ hsep [ text "Inf.:", ppr ty']
      -- liftIO $ putStrLn $ show $ hsep [ text "Exp.:", ppr tyE']
      atLoc loc $ tryUnify ty tyE

    (umapM, csM) <- raiseUse (TyMult Omega) umap 

    -- do ty' <- zonkType ty
    --    liftIO $ print $ blue $ text "CS:" <+> ppr cs'
    --    liftIO $ print $ blue $ text "CSO:" <+> ppr csO
    --    liftIO $ print $ blue $ ppr n <+> text ":" <+> ppr (TyQual csI ty')
    
    return ((n, loc, ty, csM++cs, pcs'), umapM)

  envMetaVars <- getMetaTyVarsInEnv

  (nts1, csOuter) <- fmap gatherC $ forM nts0 $ \(n, loc, ty, cs, pcs') -> do
    cs' <- simplifyConstraints cs

    -- NB: splitConstraints must be done outside of this mutual definition..
    (csI, csO) <- splitConstraints cs'

    let qt = TyQual csI ty 
    
    tt <- zonkTypeQ qt 
    let mvs = metaTyVarsQ [tt]    
    polyTy <- quantify (mvs \\ envMetaVars) tt 
    
    case M.lookup n sigMap of
      Nothing    -> return ((n, loc, polyTy, pcs'), csO)
      Just sigTy -> do 
        whenChecking (CheckingMoreGeneral polyTy sigTy) $ checkMoreGeneral loc polyTy sigTy
        return ((n, loc, sigTy, pcs'), csO)

  let decls' = [ Loc loc (DDef (n, ty) pcs') | (n, loc, ty, pcs') <- nts1 ]
  let binds' = [ (n, ty) | (n, _, ty, _) <- nts1 ]

  return (decls', binds', umap, csOuter) 
    where
      numPatterns ((ps,_):_) = length ps 
      numPatterns _          = error "Cannot happen."

      gatherU [] = ([], M.empty)
      gatherU ((x,u):ts) =
        let (xs,u') = gatherU ts
        in (x:xs, mergeUseMap u u')

      gatherC [] = ([],[])
      gatherC ((x,c):ts) =
        let (xs, c') = gatherC ts
        in (x:xs, c++c')

      -- gatherUC :: [(a,UseMap,[b])] -> ([a], UseMap, [b])
      -- gatherUC [] = ([], M.empty, [])
      -- gatherUC ((x,u,c):ts) =
      --   let (xs, u',c') = gatherUC ts
      --   in  (x:xs, mergeUseMap u u', c ++ c')
      
      checkTyPC loc qs (ps, c) expectedTy = atLoc loc $ do
        tys <- mapM (const newMetaTy) ps 
        (ps', bind, csPat) <- checkPatsTy ps qs tys 
        retTy <- newMetaTy 
        (c', umap, cs) <- withVars bind $ checkClauseTy c retTy
        tryUnify (foldr (uncurry tyarr) retTy $ zip qs tys) expectedTy

        (umap', csR) <- raiseUse (TyMult Omega) umap

        let xqs = map (\(x,_,q) -> (x,q)) bind 

        csVars <- constrainVars xqs umap 
        return ((ps', c'), foldr M.delete umap' (map fst xqs), csR ++ csVars ++ cs ++ csPat)


checkClauseTy :: MonadTypeCheck m => Clause 'Renaming -> Ty -> m (Clause 'TypeCheck, UseMap, [TyConstraint])
checkClauseTy (Clause e ws wi) expectedTy = do
  (ws', bind, umap, cs) <- inferDecls ws
  withUnrestrictedVars bind $ do
    (e',  umapE, csE) <- checkTy e expectedTy
    (wi', umapWi, csWi) <- case wi of
             Just ewi -> do
               ty   <- atLoc (location e) $ ensureRevTy expectedTy
               (ewi', umapWi, csWi) <- checkTyM ewi (ty *-> boolTy) (TyMult Omega) 
               return (Just ewi', umapWi, csWi)
             Nothing -> return (Nothing, M.empty, [])
    return (Clause e' ws' wi', umap `mergeUseMap` umapE `mergeUseMap` umapWi, cs ++ csE ++ csWi)

  

skolemize :: MonadTypeCheck m => PolyTy -> m ([TyVar], QualTy)
skolemize (TyForAll tvs ty) = do
  sks <- mapM newSkolemTyVar tvs
  return (sks, substTyQ (zip tvs $ map TyVar sks) ty)
skolemize ty = return ([], TyQual [] ty) 

tryCheckMoreGeneral :: MonadTypeCheck m => SrcSpan -> Ty -> Ty -> m ()
tryCheckMoreGeneral loc ty1 ty2 = do
  -- liftIO $ print $ red $ group $ text "Checking" <+> align (ppr ty1 <+>  text "is more general than" <> line <> ppr ty2)
  whenChecking (CheckingMoreGeneral ty1 ty2) $ checkMoreGeneral loc ty1 ty2

checkMoreGeneral :: MonadTypeCheck m => SrcSpan -> PolyTy -> PolyTy -> m ()
checkMoreGeneral loc polyTy1 polyTy2@(TyForAll _ _) = do
  -- liftIO $ print $ hsep [ text "Signature:", ppr polyTy2 ]
  -- liftIO $ print $ hsep [ text "Inferred: ", ppr polyTy1 ] 
  (skolemTyVars, ty2) <- skolemize polyTy2

  -- liftIO $ print $ hsep [ text "Skolemized sig:", ppr ty2 ]

  checkMoreGeneral2 loc polyTy1 ty2
  escapedTyVars <- freeTyVars [polyTy1]
  
  let badTyVars = filter (`elem` escapedTyVars) skolemTyVars
  unless (null badTyVars) $
    reportError $ Other $ D.group $
    D.hcat [ D.text "The inferred type",
             D.nest 2 (D.line D.<> D.dquotes (D.align $ ppr polyTy1)),
             D.line <> D.text "is not polymorphic enough for:",
             D.nest 2 (D.line D.<> D.dquotes (D.align $ ppr polyTy2)) ]

checkMoreGeneral loc polyTy1 ty = checkMoreGeneral2 loc polyTy1 (TyQual [] ty)
    
checkMoreGeneral2 :: MonadTypeCheck m => SrcSpan -> Ty -> QualTy -> m ()
checkMoreGeneral2 loc polyTy1@(TyForAll _ _) ty2 = do

  -- it could be possible that the function is called
  -- polyTy that can contain meta type variables. 
  let origVars = metaTyVars [polyTy1] 
  
  (cs, ty1) <- instantiate polyTy1
  checkMoreGeneral3 loc origVars (TyQual cs ty1) ty2

checkMoreGeneral2 loc ty1 ty2 = checkMoreGeneral3 loc (metaTyVars [ty1]) (TyQual [] ty1) ty2

checkMoreGeneral3 :: MonadTypeCheck m => SrcSpan -> [MetaTyVar] -> QualTy -> QualTy -> m ()
checkMoreGeneral3 loc origVars (TyQual cs1 ty1) (TyQual cs2 ty2) = atLoc loc $ do
  atLoc loc $ unify ty1 ty2

  -- liftIO $ print $ red $ group $ text "Checking mono type" <+> align (ppr (TyQual cs1 ty1) <+>  text "is more general than" <> line <> ppr (TyQual cs2 ty2))


  cs1' <- simplifyConstraints =<< mapM zonkTypeC cs1
  cs2' <- simplifyConstraints =<< mapM zonkTypeC cs2

  let cs1'' = filter (not . (`elem` cs2')) cs1' 

  let undetermined = metaTyVarsC (cs1'' ++ cs2') \\ origVars 
  -- let props = foldr (\a rs ->
  --                     [ ((a,True):xs, SAT.var (MV a) .&&. r) | (xs,r) <- rs ]
  --                     ++ [ ((a, False):xs, neg (SAT.var (MV a)) .&&. r) | (xs,r) <- rs])
  --                  [([], toFormula cs2' .&&. SAT.neg (toFormula cs1''))]
  --                  undetermined         

  let prop = foldr (\a cnf ->
                      (SAT.elim (MV a) True  cnf) .&&.
                      (SAT.elim (MV a) False cnf))
                   (toFormula cs2' .&&. SAT.neg (toFormula cs1''))
                   undetermined 
                        
  -- liftIO $ print $ red $ text "CS1:" <+> ppr cs1''
  -- liftIO $ print $ red $ text "CS2:" <+> ppr cs2'
  -- liftIO $ print $ red $ text "Undetermined vars." <+> ppr undetermined
  -- liftIO $ print $ red $ text "Prop:" <+> ppr prop 
  
  case cs1'' of
    [] -> return ()   
    _  -> do
      case SAT.sat prop of
        Nothing -> return () 
        Just bs -> do 
--          liftIO $ print $ red $ text "SAT." 
          reportError $ Other $ D.group $
            vcat [ hsep [pprC cs2', text "does not imply", pprC cs1']
                   <> (if null undetermined then empty
                       else line <> text "with any choice of" <+> ppr undetermined),
                   nest 2 (vcat [ text "a concrete counter example:",
                                  vcat (map pprS bs) ]) ]
      -- let results = map (\(xs,p) -> (xs, SAT.sat p)) props
      -- if any (isNothing . snd) results
      --   then return ()
      --   else do
      --   reportError $ Other $ D.group $
      --        hsep [pprC cs2', text "does not imply", pprC cs1' ]
      --        <> (if null undetermined then empty
      --            else line <> text "with any choice of" <+> ppr undetermined)
      --        <> vcat (map pprRes results)
  where
    -- pprRes (xs, ~(Just bs)) =
    --   vcat [ text "for" <+> align (hsep (map pprS xs)),
    --          text "we have a counter example:", 
    --          text "  " <> align (vcat (map pprS bs)) ]
    pprS (x, b) = ppr x <+> text "=" <+> text (if b then "Omega" else "One")
    pprC = parens . hsep . punctuate comma . map ppr 
      -- liftIO $ print $ hsep [ red (text "[TODO : Implement SAT-based check]"),
      --                         parens $ hsep $ punctuate comma $ map ppr cs2', text  "||-" ,
      --                         parens $ hsep $ punctuate comma $ map ppr cs1' ]


           
data VV = MV MetaTyVar | SV TyVar
  deriving (Eq, Ord)

instance Pretty VV where
  pprPrec k (MV v) = pprPrec k v
  pprPrec k (SV v) = pprPrec k v 

toFormula :: [TyConstraint] -> SAT.Formula VV
toFormula [] = SAT.true
toFormula (MEqMax q1 q2 q3:cs) =
  (conv q1 .<=>. conv q2 .||. conv q3) .&&. toFormula cs
  where
    conv (TyMult Omega) = SAT.true
    conv (TyMult One)   = SAT.false
    conv (TyMetaV v)    = SAT.var (MV v)
    conv (TyVar v)      = SAT.var (SV v) 
    conv t              = error $ show $ hsep [ppr t, text " is not a multiplicity"]
  

{-
Removes constraints on unvisible variables by some heuristics. We adopt
two heuristics:

  (1) Remove a cosntraint if substitution for the variables that appear on in the constraint
      does not change the satisfiability of the whole constraints.
  (2) Remove an visible variable by replacing constraints. 

As a simplest example, the constraint (a => b) can be removed.

   forall a b. (a <= b) => Int -o Int

More concrete example, let us consider the following type; here the
unvisible variable is only a.
   
   forall a b c d e f g h i.
      (c <= d, a <= g, a ~ c * e)
      => (f # c -> i) # b
      -> (h # e -> f) # d
      -> h # g -> i

Here, Step 1 cannot remove any constraint, as for g = One and c = e =
Omega, no choise of a make the constraint satisfied.

But, we still have a room to apply Step 2. We can remove "a" by replacing

    (a <= g, a ~ c * e)

by

    (c <= g, a <= g).


-}
removeUnvisibleConstraint :: [MetaTyVar] -> QualTy -> ([MetaTyVar], QualTy)
removeUnvisibleConstraint mvs tq@(TyQual cs t) =
  let (mvs', tq'@(TyQual cs' t')) = curry step mvs (TyQual cs t)
  in if length cs' < length cs || length (metaTyVarsQ [tq]) < length (metaTyVarsQ [tq']) then
       removeUnvisibleConstraint mvs' tq'
     else
       (mvs', TyQual (nub cs') t')
  where
    step = uncurry removeUnvisibleHueristicStep . uncurry removeUnvisibleByConformanceStep


{-# INLINABLE removeUnvisibleByConformanceStep #-}
removeUnvisibleByConformanceStep :: [MetaTyVar] -> QualTy -> ([MetaTyVar], QualTy)
removeUnvisibleByConformanceStep mvs (TyQual cs0 t) =
  -- A constraint is removable if it can be eliminated by fixing non
  -- visible appropriately. That is, if there is some valuation of
  -- visible parts for which any valuation of non visible part can
  -- make cs => (c & cs) false, we can `c` is necessary and otherwise
  -- c is redundant.
  --
  -- Here, we just consider removing constraints one by one. 
  
  let (cs', xs) = checkRemovable [] [] cs0
  in (mvs \\ xs, TyQual cs' t)

  where
    generalizable = (`elem` mvs)
    visibleVars = metaTyVars [t] 
    checkRemovable xs cs' []     = (reverse cs', xs)
    checkRemovable xs cs' (c:cs) =
      let 
      in case cVars of
        [] -> checkRemovable xs (c:cs') cs
        _  ->          
          case SAT.sat prop of
            Nothing -> -- removing c does not change the satisfiability
              checkRemovable (cVars ++ xs) cs' cs
            Just _ ->
              checkRemovable xs (c:cs') cs 
      where
        cVars = (filter generalizable $ metaTyVarsC [c]) \\ (metaTyVarsC (cs'++cs) ++ visibleVars)
        cf  = toFormula cs .&&. toFormula cs'
        cf' = toFormula [c] .&&. cf 
        prop =
            foldr (\x p -> SAT.elim (MV x) True p
                           .&&.
                           SAT.elim (MV x) False p)
                  (cf .&&. SAT.neg cf') -- neg (cf .=>. cf')
                  cVars

{-
repeat
  u <= a, u ~ b * c --> (b <= a, a <= c)
if u does not appear other part until fix point. 
-}
{-# INLINABLE removeUnvisibleHueristicStep #-}
removeUnvisibleHueristicStep :: [MetaTyVar] -> QualTy -> ([MetaTyVar], QualTy)
removeUnvisibleHueristicStep mvs0 (TyQual cs0 t) =
  let (mvs', cs') = step mvs0 cs0
  in (mvs', TyQual cs' t)
  where
    pick []     = mzero
    pick (a:as) = return (a, as) `mplus`
                  (do (b,bs) <- pick as
                      return (b, a:bs))

    pick2 cs = do
      (a, as) <- pick cs
      (b, bs) <- pick as
      return (a, b, bs) 

    checkMSub (MEqMax m1 m2 m3)
      | m1 == m3  = return (m2, m1)
      | m1 == m2  = return (m3, m1)
      | otherwise = mzero 

    addMSub x m1 m2 = if m1 == TyMetaV x then id
                      else                    (msub m1 m2:)

    step mvs cs = 
      case work mvs cs of
        []         -> (mvs, cs)
        (a',cs'):_ -> (mvs \\ [a'], cs') 
    
    work mvs cs = do 
      let maybeEliminatable = mvs \\ metaTyVars [t]
      (c, MEqMax (TyMetaV v') m2 m3, rest) <- pick2 cs
      (TyMetaV v, m2') <- checkMSub c 
      let eliminatable = maybeEliminatable \\ metaTyVarsC rest
      guard (v == v') 
      guard (v `elem` eliminatable)
      -- found v <= m2' and v ~ m2 * m3 
      
      return $ (v, addMSub v m2 m2' $ addMSub v m3 m2' $ rest)
      

quantify :: MonadTypeCheck m => [MetaTyVar] -> QualTy -> m PolyTy
quantify mvs0 ty0 = do
  -- liftIO $ print $ red $ text "Simplification:" <+> align (group (ppr ty0) <> line <> text "is simplified to" <> line <> group (ppr ty))
  
  forM_ (zip mvs newBinders) $
    \(mv, tyv) -> writeTyVar mv (TyVar tyv) 
  ty' <- zonkTypeQ ty
  return $ TyForAll newBinders ty'   
  where
    (mvs, ty) = removeUnvisibleConstraint mvs0 ty0
    -- (mvs, ty) = (mvs0, ty0)
    
    binders (TyForAll bs t) = bs ++ bindersQ t
    binders (TyCon _ ts) = concatMap binders ts
    binders (TyVar _)    = []
    binders (TySyn t  _) = binders t 
    binders (TyMetaV _)  = []
    binders (TyMult _)   = []

    bindersQ (TyQual cs t) = concatMap bindersC cs ++ binders t

    bindersC (MEqMax t1 t2 t3) = binders t1 ++ binders t2 ++ binders t3 
    
    usedBinders = bindersQ ty
    newBinders = take (length mvs) $ allFancyBinders \\ usedBinders

allFancyBinders :: [TyVar]
allFancyBinders = map (BoundTv . Local . User) $
  [ [x] | x <- ['a'..'z'] ] ++
  [ x : show i | i <- [1::Integer ..], x <- ['a'..'z'] ] 

