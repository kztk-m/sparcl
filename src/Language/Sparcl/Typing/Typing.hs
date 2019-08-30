{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns      #-}
module Language.Sparcl.Typing.Typing (
  inferExp,
  inferTopDecls
  ) where

import           Control.Monad.Except
import           Data.Void
-- import Control.Monad.Writer

import qualified Data.Map                       as M

import           Control.Arrow                  (first)
import qualified Data.Graph                     as G

import           Language.Sparcl.Literal
import           Language.Sparcl.Multiplicity
import           Language.Sparcl.Name
import           Language.Sparcl.Pass
import           Language.Sparcl.SrcLoc
import           Language.Sparcl.Surface.Syntax hiding (TConstraint (..),
                                                 Ty (..))
import           Language.Sparcl.Typing.TCMonad
import           Language.Sparcl.Typing.Type

import           Language.Sparcl.Algorithm.SAT  as SAT

import qualified Language.Sparcl.Core.Syntax    as C (DDecl (..), TDecl (..))

import           Language.Sparcl.DebugPrint
import qualified Language.Sparcl.Surface.Syntax as S

import           Language.Sparcl.Pretty         as D hiding ((<$>))

-- import Data.Maybe (isNothing)
import           Data.List                      (partition, (\\))

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
                                        in (t', concatMap c2c cs ++ cs')
    gatherConstraints (S.TMult m)     = (TyMult m, [])

    c2c (S.MSub t1 t2)      = msub (map (go . unLoc) t1) (map (go . unLoc) t2)

msub :: [Ty] -> [Ty] -> [TyConstraint]
msub ts1 ts2 = [ MSub t1 ts2 | t1 <- ts1 ]

msubMult :: Multiplication -> Multiplication -> [TyConstraint]
msubMult m1 m2 = msub (m2ty m1) (m2ty m2)


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

instantiate :: MonadTypeCheck m => PolyTy -> m MonoTy
instantiate t = do
  TyQual cs' t' <- instantiateQ t
  addConstraint cs'
  return t'


instantiateQ :: MonadTypeCheck m => PolyTy -> m QualTy
instantiateQ (TyForAll ts qt) = do
  ms <- mapM (const newMetaTy) ts
  let subs = zip ts ms
  -- debugPrint 3 $ "Inst:" <+> align ((ppr $ TyForAll ts qt) <+> text "--->" <> line <> ppr (substTyQ subs qt) )
  return $ substTyQ subs qt
instantiateQ t = return $ TyQual [] t

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
  [LPat 'Renaming] -> [Multiplication] -> [MonoTy] ->
  m ([LPat 'TypeCheck], [(Name,MonoTy,Multiplication)])
checkPatsTy [] [] [] = return ([], [])
checkPatsTy (p:ps) (m:ms) (t:ts) = do
  (ps', bind)  <- checkPatsTy ps ms ts
  (p',  pbind) <- checkPatTy p m t
  return (p':ps', pbind ++ bind)
checkPatsTy _ _ _ = error "Cannot happen."

checkPatTy :: MonadTypeCheck m =>
              LPat 'Renaming -> Multiplication -> MonoTy ->
              m (LPat 'TypeCheck, [(Name, MonoTy, Multiplication)])
checkPatTy = checkPatTyWork False

checkPatTyWork ::
  MonadTypeCheck m =>
  Bool ->
  LPat 'Renaming -> Multiplication -> MonoTy ->
  m (LPat 'TypeCheck, [(Name, MonoTy, Multiplication)])
checkPatTyWork isUnderRev (Loc loc pat) pmult patTy = do
  (pat', bind) <- atLoc loc $ go pat
  return (Loc loc pat', bind)
  where
    go (PVar x) =
      return (PVar (x, patTy), [(x,patTy, pmult)])

    -- TODO: to be removed
    go (PBang p) = do
      -- unify pmult (TyMult Omega)
      (p', bind) <- checkPatTyWork isUnderRev p omega patTy
      addConstraint $ msubMult omega pmult
      return (PBang p', bind)

    go (PCon c ps) = do
      tyOfC <- instantiate =<< askType loc c
      (ps', retTy, bind) <- foldM inferApp ([], tyOfC, []) ps
      tryUnify retTy patTy
      retTy' <- zonkType retTy
      case retTy' of
        TyCon n [_,_,_] | n == nameTyArr ->
          reportError $ Other $ text "Constructor" <+> ppr n <+> text "must be fully applied."
        _ ->
          return ()
      return (PCon (c, tyOfC) (reverse ps'), bind)
        where
          inferApp (ps', ty, bind) p = do
            (argTy, mty, resTy) <- atLoc (location p) $ ensureFunTy ty
            m <- ty2mult mty
            -- (mm, cm) <- maxMult m pmult
            (p', bind') <- checkPatTyWork isUnderRev p (lub m pmult) argTy
            return (p':ps', resTy, bind'++bind)

          -- maxMult m1 m2 = do
          --   mm <- newMetaTy
          --   return (mm, [MEqMax mm m1 m2])




    go (PREV p) = do
      when isUnderRev $ atLoc (location p) $
        reportError $ Other $ text "rev patterns cannot be nested."

      ty <- ensureRevTy patTy
      (p', bind) <- checkPatTyWork True p pmult ty
      let bind' = map (\(x,t,m) -> (x, revTy t,m)) bind

      -- forM_ xqs $ \(_, q) ->
      --   -- TODO: Add good error messages.
      --   unify q (TyMult One)

      return (PREV p', bind')

    go (PWild x) = do -- this is only possible when pmult is omega
      -- tryUnify pmult (TyMult Omega)
      (Loc _ (PVar x'), _bind) <- checkPatTyWork isUnderRev (noLoc $ PVar x) omega patTy
      addConstraint $ msubMult omega pmult
      return (PWild x', [] )

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
simplifyConstraints constrs = whenChecking (CheckingConstraint constrs) $ go constrs >>= removeRedundantConstraint
  where
    go cs = do
      csZonked <- mapM zonkTypeC cs
      cs' <- propagateConstantsToFixedpoint csZonked
      isEffective <- loopToEquiv cs'
      if length cs' < length cs || isEffective
        then go cs'
        else return cs'


checkImplication :: [TyConstraint] -> [TyConstraint] -> Bool
checkImplication given wanted =
  let prop = toFormula given .&&. SAT.neg (toFormula wanted)
  in case SAT.sat prop of
       Just _  -> False
       Nothing -> True

-- | Removal of redundant predicate
removeRedundantConstraint :: MonadTypeCheck m => [TyConstraint] -> m [TyConstraint]
removeRedundantConstraint cs_ = do
  cs <- mapM zonkTypeC cs_
  return (go [] cs)
    where
      go proced [] = reverse proced
      go proced (c:cs) =
        if checkImplication (proced++cs) [c]
        then go proced     cs -- c is redundant
        else go (c:proced) cs -- c


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
  foldM procSCCs False sccs
  where
    procSCCs :: Bool -> G.SCC Ty -> m Bool
    procSCCs  isE (G.AcyclicSCC _)  = return isE
    procSCCs  isE (G.CyclicSCC [_]) = return isE
    procSCCs _isE (G.CyclicSCC xs)  =
      equate xs >> return True

    equate []       = error "Cannot happen."
    equate (ty:tys) = do
      debugPrint 2 $ text "Equating" <+> ppr (ty:tys)
      forM_ tys $ \ty' -> unify ty ty'

    makeSCC :: [TyConstraint] -> m [G.SCC Ty]
    makeSCC xs = G.stronglyConnComp . map (\(k,vs) -> (k,k,vs)) . M.toList <$> makeLeMap xs

    makeLeMap :: [TyConstraint] -> m (M.Map Ty [Ty])
    makeLeMap [] = return M.empty
    makeLeMap (c:cs) = do
      t <- makeLeMap cs
      MSub t1 ts2 <- zonkTypeC c
      case ts2 of
        []   -> do
          unify t1 (TyMult One)
          return t
        [t2] | all noTyVar [t1, t2] ->
          return $ M.insertWith (++) t1 [t2] t
        _    ->
          -- keep t
          return t

    noTyVar (TyVar _)   = False
    noTyVar (TyMult _)  = True
    noTyVar (TyMetaV _) = True
    noTyVar _           = error "Cannot happen."

      -- MEqMax t1' t2' t3' <- zonkTypeC c
      -- return $ M.insertWith (++) t2' [t1'] $ M.insertWith (++) t3' [t1'] t




propagateConstantsToFixedpoint :: MonadTypeCheck m => [TyConstraint] -> m [TyConstraint]
propagateConstantsToFixedpoint xs = do
  ys <- propagateConstants xs
  if length xs > length ys
    then propagateConstantsToFixedpoint ys
    else return ys

propagateConstants :: MonadTypeCheck m => [TyConstraint] -> m [TyConstraint]
propagateConstants [] = return []
propagateConstants (c:cs) = do
  MSub t1 ts2_ <- zonkTypeC c
  let ts2 = simplifyMultiplication ts2_
  case (t1, ts2) of
    (TyMult One, _) ->
      -- remove the constraint
      propagateConstants cs
    (TyMult Omega, [t2]) -> do
      unify t2 (TyMult Omega)
      propagateConstants cs
    (_, [TyMult Omega]) ->
      propagateConstants cs
    (_, []) -> do
      unify t1 (TyMult One)
      propagateConstants cs
    (_, _) | t1 `elem` ts2 ->
             propagateConstants cs
           | otherwise -> do
               (MSub t1 ts2 :) <$> propagateConstants cs
    where
      simplifyMultiplication = go
        where
          go [] = []
          go (TyMult Omega : _) = [TyMult Omega]
          go (TyMult One : ts)  = go ts
          go (t : ts) = case go ts of
            [TyMult Omega] -> [TyMult Omega]
            [TyMult One]   -> [t]
            ts'            -> t : ts'






constrainVars :: MonadTypeCheck m => [(Name, Multiplication)] -> UseMap -> m ()
constrainVars []          _ = return ()
constrainVars ((x,q):xqs) m = do
  -- let dx = hsep [ text "linearity of", dquotes (ppr x) <> text ", but it is used more than once" ]
  case lookupUseMap x m of
    Just mul -> do
      constrainVars xqs m
      addConstraint $ msubMult mul q
    Nothing -> do
      -- whenChecking (OtherContext dx) $ unify q (TyMult Omega)
      constrainVars xqs m
      addConstraint $ msubMult omega q


-- TODO: sig-expression is buggy.

inferTy :: MonadTypeCheck m => LExp 'Renaming -> m (LExp 'TypeCheck, BodyTy, UseMap)
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
      (e', umap) <- checkTy (Loc loc e) ty
      return (e', ty, umap)


checkTyM :: MonadTypeCheck m => LExp 'Renaming -> BodyTy -> Multiplication -> m (LExp 'TypeCheck, UseMap)
checkTyM lexp ty m = do
  (lexp', umap) <- checkTy lexp ty
  return (lexp', raiseUse m umap)

checkTy :: forall m. MonadTypeCheck m => LExp 'Renaming -> BodyTy -> m (LExp 'TypeCheck, UseMap)
checkTy lexp@(Loc loc expr) expectedTy = fmap (first $ Loc loc) $ atLoc loc $ atExp lexp $ go expr
  where
    -- first3 f (a,b,c) = (f a, b, c)

    go :: Exp 'Renaming -> m (Exp 'TypeCheck, UseMap)
    go (Var x) = do
      tyOfX <- askType loc x
      t <- instantiate tyOfX
      tryUnify t expectedTy
      return (Var (x, tyOfX), singletonUseMap x)

    go (Lit l) = do
      ty <- litTy l
      tryUnify ty expectedTy
      return (Lit l, M.empty)

    go (Abs pats e) = do
      -- multiplicity of arguments
      qs <- mapM (const newMetaTy) pats
      ts <- mapM (const newMetaTy) pats
      qs' <- mapM ty2mult qs

      (pats', bind) <- checkPatsTy pats qs' ts
      retTy <- newMetaTy
      (e', umap) <- -- withMultVars qs $ withVars bind $ checkTy e retTy
        withVars [ (n,t) | (n,t,_) <- bind ] $ checkTy e retTy

      let xqs = map (\(x,_,q) -> (x,q)) bind

      tryUnify (foldr (uncurry tyarr) retTy $ zip qs ts) expectedTy
      constrainVars xqs umap

      return (Abs pats' e', foldr (M.delete .  fst) umap xqs)

    go (App e1 e2) = do
      (e1', ty1, umap1) <- inferTy e1
      (argTy, m, resTy) <- atExp e1 $ atLoc (location e1) $ ensureFunTy ty1
      mul <- ty2mult m
      (e2', umap2) <- checkTyM e2 argTy mul

      tryUnify resTy expectedTy

      return (App e1' e2', mergeUseMap umap1 umap2)

    go (Con c) = do
      tyOfC <- askType loc c
      t <- instantiate tyOfC
      tryUnify t expectedTy
      return (Con (c, t), M.empty)

    -- TODO: to be removed
    go (Bang e) = do
      (e', umap) <- checkTy e expectedTy
      -- (umap', cs') <- raiseUse (TyMult Omega) umap
      -- return (Bang e', umap', cs' ++ cs)
      return (Bang e', raiseUse omega umap)

    go (Sig e tySyn) = do
      let sigTy = ty2ty tySyn
      (e', polyTy, umap) <- inferPolyTy False e
      tryCheckMoreGeneral loc polyTy sigTy
      monoTy <- instantiate sigTy

      -- liftIO $ print $ red $ text "CSI:" <+> ppr csI
      -- liftIO $ print $ red $ text "CSO:" <+> ppr csO

      tryUnify monoTy expectedTy
      return (unLoc e', umap)

      -- let ty = ty2ty tySyn
      -- (cs, ty') <- instantiate ty
      -- tryUnify ty' expectedTy
      -- (e', umap, cs') <- checkTy e ty'
      -- return (unLoc e', umap, cs ++ cs')

    go Lift = do
      tyA <- newMetaTy
      tyB <- newMetaTy
      tryUnify (liftTy tyA tyB) expectedTy
      return (Lift, M.empty)
      where
        liftTy tyA tyB =
          (tyA *-> tyB) *-> (tyB *-> tyA) *-> (revTy tyA -@ revTy tyB)

    go Unlift = do
      tyA <- newMetaTy
      tyB <- newMetaTy
      tryUnify (unliftTy tyA tyB) expectedTy
      return (Unlift, M.empty)
      where
        unliftTy tyA tyB =
          (revTy tyA -@ revTy tyB) *-> tupleTy [tyA *-> tyB, tyB *-> tyA]

    go RPin = do
      tyA <- newMetaTy
      tyB <- newMetaTy
      tryUnify (pinTy tyA tyB) expectedTy
      return (RPin, M.empty)
        where
          pinTy tyA tyB =
            revTy tyA *-@ (tyA *-> revTy tyB) *-@ revTy (tupleTy [tyA, tyB])

    go (Parens e) = do
      (e', umap) <- checkTy e expectedTy
      return (Parens e', umap)

    go (Op op e1 e2) = do
      tyOfOp <- instantiate =<< askType loc op
      ty1    <- newMetaTy
      ty2    <- newMetaTy
      m1     <- newMetaTy
      m2     <- newMetaTy

      mul1 <- ty2mult m1
      mul2 <- ty2mult m2

      tryUnify tyOfOp (TyCon nameTyArr [m1, ty1, TyCon nameTyArr [m2, ty2, expectedTy]])
      (e1', umap1) <- {- withMultVars [m1,m2] $ -} checkTyM e1 ty1 mul1
      (e2', umap2) <- {- withMultVars [m1,m2] $ -} checkTyM e2 ty2 mul2
      return (Op (op, tyOfOp) e1' e2', mergeUseMap umap1 umap2)

    go (RCon c) = do
      tyOfC_ <- instantiate =<< askType loc c
      let tyOfC = addRev tyOfC_
      tryUnify tyOfC expectedTy
      return (RCon (c, tyOfC), M.empty)
        where
          -- FIXME: m must be one
          addRev (TyCon t [m, t1,t2]) | t == nameTyArr = TyCon t [m, revTy t1, addRev t2]
          addRev t                                     = revTy t

    go (Let decls e) = do
      (decls', bind, umapLet) <- inferDecls decls
      (e', umap)              <- {- withUnrestrictedVars -} withVars bind $ checkTy e expectedTy
      return (Let decls' e', mergeUseMap umap umapLet)

    go (Case e0 alts) = do
      p <- newMetaTyVar -- multiplicity of `e`
      mul <- ty2mult (TyMetaV p)

      tyPat <- newMetaTy
      (e0', umap0)   <- {- withMultVar (TyMetaV p) $ -} checkTyM e0 tyPat mul
      (alts', umapA) <- {- withMultVar (TyMetaV p) $ -} checkAltsTy alts tyPat mul expectedTy

      return (Case e0' alts', mergeUseMap umap0 umapA)

    go (RDO as0 er) = do
      (as0', bind, umap) <- goAs as0
      let bind' = map (\(x,t,_) -> (x, revTy t)) bind
      let xs = map (\(x,_) -> x) bind'
      let xqs = [ (x, one) | x <- xs ]

      (er', umapr) <- withVars bind' $ checkTy er expectedTy
      constrainVars xqs umapr

      return (RDO as0' er', mergeUseMap umap (foldr M.delete umapr xs))
      where
        goAs [] = return ([], [], M.empty)
        goAs ((p,e):as) = do
          tyE <- newMetaTy
          (e', umapE) <- checkTy e (revTy tyE)
          (p', bind)  <- checkPatTy p omega tyE

          let xqs = map (\(x,_,q) -> (x,q)) bind

          (as', bindAs, umapAs) <- withVars [ (n,t) | (n,t,_) <- bind ] $ goAs as

          constrainVars xqs umapAs

          return ((p',e'):as', bindAs ++ bind,
                   mergeUseMap (foldr (M.delete . fst) umapAs xqs) umapE)



-- NB: @generalizeTy@ makes the current constraint empty
generalizeTy :: MonadTypeCheck m => MonoTy -> UseMap -> m PolyTy
generalizeTy ty_ um = do
  cs  <- readConstraint
  cs' <- simplifyConstraints cs

  ty <- zonkType ty_

  tcLevel <- askCurrentTcLevel
  umapVars <- metaTyVars <$> mapM zonkType [ t | m <- M.elems um, t <- m2ty m ]

  let qty = TyQual cs' ty

  generalizable <-
        filterM (\m -> do
                    lv <- readTcLevelMv m
                    return $ lv > tcLevel) (metaTyVarsQ [qty] \\ umapVars)

  -- We qualifiy constraints that refer to generalizable variables
  -- 6.1.4 Constant and locally-constant overloading
  let (csI, csO) = partition (`refersTo` generalizable) cs'
  let qty' = TyQual csI ty


  polyTy <- quantify generalizable qty'
  debugPrint 2 $ text "Gen" <> brackets (text $ show tcLevel) <> text ":" <+>
    align (vsep [ text "Generalizable" <+> ppr generalizable,
                  group (align (group (ppr qty) <> line <> text "-->" <> line <> group (ppr polyTy))) ])

  setConstraint csO

  return polyTy
  where
    refersTo :: TyConstraint -> [MetaTyVar] -> Bool
    refersTo (MSub m ms) vs = any (`elem` vs) $ metaTyVars (m:ms)


inferPolyTy :: MonadTypeCheck m => Bool -> LExp 'Renaming -> m (LExp 'TypeCheck, PolyTy, UseMap)
inferPolyTy isMultipleUse expr = do
  (expr', ty, umap) <- pushLevel $ inferTy expr

  -- (umapM, csM) <- if isMultipleUse then raiseUse (TyMult Omega) umap
  --                 else return (umap, [])
  let umapM = if isMultipleUse then raiseUse omega umap else umap

  polyTy <- generalizeTy ty umapM

  return (expr', polyTy, umapM)

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
  (expr', polyTy, _) <- inferPolyTy True expr
  return (expr', polyTy)


checkAltsTy ::
  MonadTypeCheck m => [ (LPat 'Renaming, Clause 'Renaming) ] ->
  MonoTy -> Multiplication -> BodyTy -> m ([ (LPat 'TypeCheck, Clause 'TypeCheck) ], UseMap)
checkAltsTy alts patTy q bodyTy =
  -- parallel $ map checkAltTy alts
  gatherAltUC =<< mapM checkAltTy alts
  where
    checkAltTy (pat, c) = do
      (pat', bind) <- checkPatTy pat q patTy
      (c', umap)   <- withVars [ (n,t) | (n,t,_) <- bind ] $ checkClauseTy c bodyTy

      let xqs = map (\(x,_,qq) -> (x,qq)) bind
      constrainVars xqs umap
      return ((pat', c'), foldr (M.delete . fst) umap xqs)
    -- checkAltTy (p, c) = do
    --   (p', ubind, lbind) <- checkPatTy p patTy
    --   c' <- withUVars ubind $ withLVars lbind $ checkClauseTy c bodyTy
    --   return (p', c')

gatherAltUC :: MonadTypeCheck m =>
               [(a,UseMap)] -> m ([a], UseMap)
gatherAltUC []                           = return ([], M.empty)
gatherAltUC ((obj,umap):triples) = go obj umap triples
  where
    go s um [] = return ([s], um)
    go s um ((s',um'):ts) = do
      (ss, umR) <- go s' um' ts
      -- (um2, cs2) <- maxUseMap um umR
      let um2 = multiplyUseMap um umR
      return (s:ss, um2)





inferDecls :: MonadTypeCheck m => Decls 'Renaming (LDecl 'Renaming) ->
              m (Decls 'TypeCheck (LDecl 'TypeCheck), [(Name, PolyTy)], UseMap)
inferDecls (Decls v _) = absurd v
inferDecls (HDecls _ dss) = do
  (dss', bind , umap) <- go [] dss
  return (HDecls () dss', bind, umap )
  where
    go bs [] = return ([], bs, M.empty)
    go bs (ds:rest) = do
      (ds', bind,  umap)  <- inferMutual ds
      (rest', bs', umap') <- withVars bind $ go (bind ++ bs) rest
      return (ds':rest', bs', mergeUseMap umap umap')


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
        [ (n, foldr ((-@) . const typeKi) typeKi ns) | Loc _ (n, ns, _) <- dataDecls ]
        ++
        [ (cn, TyForAll tvs $ TyQual [] (foldr ((-@) . ty2ty) (TyCon n $ map TyVar tvs) tys)) |
          Loc _ (n, ns, cdecls) <- dataDecls,
          let tvs = map BoundTv ns,
          Loc _ (CDecl cn tys) <- cdecls ]

  withVars (M.toList typeTable) $
   withSyns (M.toList synTable) $ do
     (decls', nts, _) <- inferDecls decls
     -- liftIO $ putStrLn $ show cs
     return (decls', nts, dataDecls', typeDecls', typeTable, synTable)



inferMutual :: MonadTypeCheck m =>
               [LDecl 'Renaming] -> m ([LDecl 'TypeCheck], [(Name, PolyTy)], UseMap)
inferMutual decls = do
--  let nes = [ (n,e) | Loc _ (DDef n _) <- decls ]
  let ns  = [ n | Loc _ (DDef n _) <- decls ]
  let defs = [ (loc, n, pcs) | Loc loc (DDef n pcs) <- decls ]
  let sigMap = M.fromList [ (n, ty2ty t) | Loc _ (DSig n t) <- decls ]

  -- save current constraint at the point
  csOrig <- readConstraint
  setConstraint []


  (nts0, umap) <- pushLevel $ do
    tys <- forM ns (\n -> case M.lookup n sigMap of
                            Just t  -> return t
                            Nothing -> newMetaTy)
    (nts0, umap) <- fmap gatherU $ withVars (zip ns tys) $ forM defs $ \(loc, n, pcs) -> do
      -- body's type
      ty <- newMetaTy
      -- argument's multiplicity
      qs <- mapM (const newMetaTy) [1..numPatterns pcs]

      (pcs', umap) <- gatherAltUC =<< mapM (flip (checkTyPC loc qs) ty) pcs

      -- type of n in the environment
      tyE <- askType loc n

      unless (M.member n sigMap) $
        -- unify the body type and returned type
        atLoc loc $ tryUnify ty tyE

      -- cut the current constraint
      cs <- readConstraint
      setConstraint []

      return ((n, loc, ty, cs, pcs'), raiseUse omega umap)

    return (nts0, umap)

  nts1 <- forM nts0 $ \(n, loc, ty, cs, pcs') -> do
    csO <- readConstraint
    -- Assuming that the current constraint is empty
    setConstraint cs

    -- NB: No type variables exacpe in the useMap so using emptyUseMap is OK.
    polyTy <- generalizeTy ty emptyUseMap

    res <- case M.lookup n sigMap of
      Nothing    ->
        return (n, loc, polyTy, pcs')
      Just sigTy -> do
        -- if a function comes with a signature, we check that its inferred type is more polymorphic than
        -- the signature
        tryCheckMoreGeneral loc polyTy sigTy
        return (n, loc, sigTy, pcs')

    do cs' <- readConstraint
       setConstraint (csO ++ cs')
    return res


  let decls' = [ Loc loc (DDef (n, ty) pcs') | (n, loc, ty, pcs') <- nts1 ]
  let binds' = [ (n, ty) | (n, _, ty, _) <- nts1 ]

  -- restore the original constraint
  do cs' <- readConstraint
     setConstraint (csOrig ++ cs')

  return (decls', binds', umap)
    where
      numPatterns ((ps,_):_) = length ps
      numPatterns _          = error "Cannot happen."

      gatherU [] = ([], M.empty)
      gatherU ((x,u):ts) =
        let (xs,u') = gatherU ts
        in (x:xs, mergeUseMap u u')

      -- gatherC [] = ([],[])
      -- gatherC ((x,c):ts) =
      --   let (xs, c') = gatherC ts
      --   in (x:xs, c++c')

      -- gatherUC :: [(a,UseMap,[b])] -> ([a], UseMap, [b])
      -- gatherUC [] = ([], M.empty, [])
      -- gatherUC ((x,u,c):ts) =
      --   let (xs, u',c') = gatherUC ts
      --   in  (x:xs, mergeUseMap u u', c ++ c')

      checkTyPC loc qs (ps, c) expectedTy = atLoc loc $ do
        muls <- mapM ty2mult qs
        tys <- mapM (const newMetaTy) ps
        (ps', bind) <- checkPatsTy ps muls tys
        retTy <- newMetaTy
        (c', umap) <- withVars [ (n,t) | (n,t,_) <- bind ] $ checkClauseTy c retTy
        tryUnify (foldr (uncurry tyarr) retTy $ zip qs tys) expectedTy

        let umap' = raiseUse omega umap

        let xqs = map (\(x,_,q) -> (x,q)) bind

        constrainVars xqs umap
        return ((ps', c'), foldr (M.delete . fst) umap' xqs)


checkClauseTy :: MonadTypeCheck m => Clause 'Renaming -> Ty -> m (Clause 'TypeCheck, UseMap)
checkClauseTy (Clause e ws wi) expectedTy = do
  (ws', bind, umap) <- inferDecls ws
  withVars bind $ do
    (e',  umapE) <- checkTy e expectedTy
    (wi', umapWi) <- case wi of
             Just ewi -> do
               ty   <- atLoc (location e) $ ensureRevTy expectedTy
               (ewi', umapWi) <- checkTyM ewi (ty *-> boolTy) omega
               return (Just ewi', umapWi)
             Nothing -> return (Nothing, M.empty)
    return (Clause e' ws' wi', umap `mergeUseMap` umapE `mergeUseMap` umapWi)



skolemize :: MonadTypeCheck m => PolyTy -> m ([TyVar], QualTy)
skolemize (TyForAll tvs ty) = do
  sks <- mapM newSkolemTyVar tvs
  return (sks, substTyQ (zip tvs $ map TyVar sks) ty)
skolemize ty = return ([], TyQual [] ty)

tryCheckMoreGeneral :: MonadTypeCheck m => SrcSpan -> Ty -> Ty -> m ()
tryCheckMoreGeneral loc ty1 ty2 = -- do
  -- cl <- currentLevel
  -- debugPrint 2 $ text "tryCheckMoreGeneral is called" <+> brackets (ppr cl) <+> text "to check" </>
  --                ppr ty1 <+> text "<=" <+> ppr ty2
  -- liftIO $ print $ red $ group $ text "Checking" <+> align (ppr ty1 <+>  text "is more general than" <> line <> ppr ty2)
  whenChecking (CheckingMoreGeneral ty1 ty2) $ pushLevel $ checkMoreGeneral loc ty1 ty2

-- todo: delay implication checking until

checkMoreGeneral :: MonadTypeCheck m => SrcSpan -> PolyTy -> PolyTy -> m ()
checkMoreGeneral loc polyTy1 polyTy2@(TyForAll _ _) = do
  -- liftIO $ print $ hsep [ text "Signature:", ppr polyTy2 ]
  -- liftIO $ print $ hsep [ text "Inferred: ", ppr polyTy1 ]
  (skolemTyVars, ty2) <- skolemize polyTy2

  -- cl <- currentLevel
  -- debugPrint 2 $ text "check starts" <+> brackets (ppr cl)

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

  -- -- it could be possible that the function is called
  -- -- polyTy that can contain meta type variables.
  let origVars = metaTyVars [polyTy1]

  TyQual cs ty1 <- instantiateQ polyTy1
  checkMoreGeneral3 loc origVars (TyQual cs ty1) ty2

checkMoreGeneral2 loc ty1 ty2 = checkMoreGeneral3 loc (metaTyVars [ty1]) (TyQual [] ty1) ty2

checkMoreGeneral3 :: MonadTypeCheck m => SrcSpan -> [MetaTyVar] -> QualTy -> QualTy -> m ()
checkMoreGeneral3 loc origVars (TyQual cs1 ty1) (TyQual cs2 ty2) = atLoc loc $ do
  atLoc loc $ unify ty1 ty2

  -- liftIO $ print $ red $ group $ text "Checking mono type" <+> align (ppr (TyQual cs1 ty1) <+>  text "is more general than" <> line <> ppr (TyQual cs2 ty2))
  checkImplicationD origVars cs2 cs1


--   cs1' <- simplifyConstraints =<< mapM zonkTypeC cs1
--   cs2' <- simplifyConstraints =<< mapM zonkTypeC cs2

--   let cs1'' = filter (not . (`elem` cs2')) cs1'

--   let undetermined = metaTyVarsC (cs1'' ++ cs2') \\ origVars
--   -- let props = foldr (\a rs ->
--   --                     [ ((a,True):xs, SAT.var (MV a) .&&. r) | (xs,r) <- rs ]
--   --                     ++ [ ((a, False):xs, neg (SAT.var (MV a)) .&&. r) | (xs,r) <- rs])
--   --                  [([], toFormula cs2' .&&. SAT.neg (toFormula cs1''))]
--   --                  undetermined

--   -- To check exists origVars. forall `undetermined`. neg (cs2 => cs1'') holds
--   -- i.e.,
--   let prop = foldr (\a cnf ->
--                       SAT.elim (MV a) True  cnf
--                       .&&. SAT.elim (MV a) False cnf)
--                    (toFormula cs2' .&&. SAT.neg (toFormula cs1''))
--                    undetermined

--   debugPrint 2 $ nest 2 $
--     text "Implicating Check:" <> line <>
--     vcat [text "Wanted:" <+> ppr cs1'',
--           text "Given: " <+> ppr cs2',
--           text "EVars: " <+> ppr undetermined,
--           text "Prop:  " <+> ppr prop]

--   case cs1'' of
--     [] -> return ()
--     _  ->
--       case SAT.sat prop of
--         Nothing -> return ()
--         Just bs ->
-- --          liftIO $ print $ red $ text "SAT."
--           reportError $ Other $ D.group $
--             vcat [ hsep [pprC cs2', text "does not imply", pprC cs1']
--                    <> (if null undetermined then empty
--                        else line <> text "with any choice of" <+> ppr undetermined),
--                    nest 2 (vcat [ text "a concrete counter example:",
--                                   vcat (map pprS bs) ]) ]
--       -- let results = map (\(xs,p) -> (xs, SAT.sat p)) props
--       -- if any (isNothing . snd) results
--       --   then return ()
--       --   else do
--       --   reportError $ Other $ D.group $
--       --        hsep [pprC cs2', text "does not imply", pprC cs1' ]
--       --        <> (if null undetermined then empty
--       --            else line <> text "with any choice of" <+> ppr undetermined)
--       --        <> vcat (map pprRes results)
--   where
--     -- pprRes (xs, ~(Just bs)) =
--     --   vcat [ text "for" <+> align (hsep (map pprS xs)),
--     --          text "we have a counter example:",
--     --          text "  " <> align (vcat (map pprS bs)) ]
--     pprS (x, b) = ppr x <+> text "=" <+> text (if b then "Omega" else "One")
--     pprC = parens . hsep . punctuate comma . map ppr
--       -- liftIO $ print $ hsep [ red (text "[TODO : Implement SAT-based check]"),
--       --                         parens $ hsep $ punctuate comma $ map ppr cs2', text  "||-" ,
--       --                         parens $ hsep $ punctuate comma $ map ppr cs1' ]


checkImplicationD :: MonadTypeCheck m => [MetaTyVar] -> [TyConstraint] -> [TyConstraint] -> m ()
checkImplicationD origVars csGiven csWanted = do
  cs1' <- simplifyConstraints =<< mapM zonkTypeC csWanted
  cs2' <- simplifyConstraints =<< mapM zonkTypeC csGiven

  let cs1'' = filter (not . (`elem` cs2')) cs1'

  let undetermined = metaTyVarsC (cs1'' ++ cs2') \\ origVars
  -- undetermined <- filterM (\mv -> readTcLevelMv mv >>= \i -> return (i >= cLevel)) $ metaTyVarsC (cs1''++cs2')

  let cs1''' = eliminateExistential undetermined cs1''

  check undetermined cs2' cs1'''
  where
    -- NB: The type signature matters here.
    check :: MonadTypeCheck m => [MetaTyVar] -> [TyConstraint] -> [TyConstraint] -> m ()
    check undetermined given wanted = do
      g <- simplifyConstraints =<< mapM zonkTypeC given
      w <- simplifyConstraints =<< mapM zonkTypeC wanted

      -- We skip the trivial case.
      unless (null w) $ do
        cLevel <- currentLevel
        lv <- lvToCheck g w

        if lv == cLevel
          then do -- We are ready for checking

          let prop = toFormula g .&&. SAT.neg (toFormula w)
          debugPrint 2 $ nest 2 $
            text "Implicating Check:" <> brackets (ppr cLevel) <> line <>
            vcat [text "Wanted:" <+> ppr w,
                  text "Given: " <+> ppr g,
                  text "EVars: " <+> ppr undetermined,
                  text "Prop:  " <+> ppr prop]

          case SAT.sat prop of
            Nothing -> return ()
            Just bs ->
              reportError $ Other $ D.group $
              vcat [ hsep [pprC csGiven, text "does not imply", pprC csWanted]
                     <> (if null undetermined then empty
                         else line <> text "with any choice of" <+> ppr undetermined),
                     nest 2 (vcat [ text "a concrete counter example:",
                                    vcat (map pprS bs) ]) ]
          else do -- We are not ready to check the implication as there are undetermined variables.
          defer $ SuspendedCheck (check undetermined g w)


    -- freeTyVarsC cs = concat <$> mapM (\(MSub m ms) -> freeTyVars (m:ms)) cs


    lvToCheck :: MonadTypeCheck m => [TyConstraint] -> [TyConstraint] -> m TcLevel
    lvToCheck cs1 cs2 = csTcLevel (cs1 ++ cs2)

    pprS (x, b) = ppr x <+> text "=" <+> text (if b then "Omega" else "One")
    pprC = parens . hsep . punctuate comma . map ppr


data VV = MV MetaTyVar | SV TyVar
  deriving (Eq, Ord)

instance Pretty VV where
  pprPrec k (MV v) = pprPrec k v
  pprPrec k (SV v) = pprPrec k v

toFormula :: [TyConstraint] -> SAT.Formula VV
toFormula [] = SAT.true
toFormula (c:cs) =
  toForm c .&&. toFormula cs
  where
    -- toForm (MEqMax q1 q2 q3)
    --   | q1 == q3  = conv q2 .=>. conv q1
    --   | q1 == q2  = conv q3 .=>. conv q1
    --   | otherwise = conv q1 .<=>. (conv q2 .||. conv q3)
    toForm (MSub q1 qs) =
      conv q1 .=>. foldr (.||.) SAT.false (map conv qs)
    conv (TyMult Omega) = SAT.true
    conv (TyMult One)   = SAT.false
    conv (TyMetaV v)    = SAT.var (MV v)
    conv (TyVar v)      = SAT.var (SV v)
    conv t              = error $ show $ hsep [ppr t, text " is not a multiplicity"]



{- |
The following function @eliminateExitential@ effectively eliminates existentials in contraints.

The elimination is based on the fact that disjunction of a definite
clause and a goal clause result in a definite clause. Notice that
contraint

@
MSub m [m1, ..., mn]
@

can be seen as a dual Horn clause @~m | m1 | m2 | ... | mn@.

Thus, take a dijunction of the above and
@
MSub Omega [n1,...,nk]
@

results in the following predicate.

@
MSub m [m1,...,mn,n1,...,nk]
@

Then, revisit the original problem of eliminating @r@ in @exists
r. C@. This can be done simplify by @C[r = One] \/ C[r = Omega]@.

Then, we do the elimination in three steps.

1. Split @C@ into the following.

@
C1 = [ MSub m [m1,..,mi-1,mi+1,...,mn] | MSub m ms in C, mi = r, m /= r ]
Co = [ ms | MSub m ms in C, m = r ]
Cr = [ c | c in C, not (r `elem` metaTyVarsC c) ]
@

2. Compute
@
C' = [ MSub m (ms ++ ns) | MSub m ms <- C1, MSub _ ms <- Co ]
@

3. Then, return @C', Cr@.
-}

-- Assumption: constraints are zonked.
eliminateExistential :: [MetaTyVar] -> [TyConstraint] -> [TyConstraint]
eliminateExistential []     cs = cs
eliminateExistential (r:rs) cs =
  let (csOne, qss, csRest) = splitCs cs
  in eliminateExistential rs ([ MSub m (ms ++ qs) | MSub m ms <- csOne, qs <- qss ] ++ csRest)
  where
    splitCs :: [TyConstraint] -> ([TyConstraint], [[Ty]], [TyConstraint])
    splitCs [] = ([], [], [])
    splitCs (MSub q qs:rest)
      | rInQ , rInQs = (r1, r2,    r3)
      | rInQ         = (r1, qs:r2, r3) -- but not rInQs
      | rInQs        = (MSub q (qs \\ [TyMetaV r]):r1, r2, r3)
      | otherwise    = (r1, r2, MSub q qs:r3)
      where
        (r1, r2, r3) = splitCs rest
        rInQ  = r `elem` metaTyVars [q]
        rInQs = r `elem` metaTyVars qs

eliminateInvisible :: [MetaTyVar] -> QualTy -> ([MetaTyVar],  QualTy)
eliminateInvisible mvs (TyQual cs t) =
  -- Assumption: @mvs@ is a set of variables to be generalized.
  let visibleVars = metaTyVars [t]
      invisibles  = mvs \\ visibleVars
      cs' = eliminateExistential invisibles cs
  in (mvs \\ invisibles, TyQual cs' t)



quantify :: MonadTypeCheck m => [MetaTyVar] -> QualTy -> m PolyTy
quantify mvs0 ty0 = do
  -- debugPrint 2 $ text "Simpl:" <+> align (group (ppr (mvs0, ty0)) <> line <> text "-->" <> line <> group (ppr (mvs, ty)))
  -- liftIO $ print $ red $ "Generalization:" <+> ppr (zip mvs newBinders)

  forM_ (zip mvs newBinders) $
    \(mv, tyv) -> writeTyVar mv (TyVar tyv)
  ty' <- zonkTypeQ ty
  return $ TyForAll newBinders ty'
  where
    (mvs, ty) = eliminateInvisible mvs0 ty0
    -- (mvs, ty) = (mvs0, ty0)

    binders (TyForAll bs t) = bs ++ bindersQ t
    binders (TyCon _ ts)    = concatMap binders ts
    binders (TyVar _)       = []
    binders (TySyn t  _)    = binders t
    binders (TyMetaV _)     = []
    binders (TyMult _)      = []

    bindersQ (TyQual cs t) = concatMap bindersC cs ++ binders t

    bindersC (MSub t1 ts2) = binders t1 ++ concatMap binders ts2

    usedBinders = bindersQ ty
    newBinders = take (length mvs) $ allFancyBinders \\ usedBinders

allFancyBinders :: [TyVar]
allFancyBinders = map (BoundTv . Local . User) $
  [ [x] | x <- ['a'..'z'] ] ++
  [ x : show i | i <- [1::Integer ..], x <- ['a'..'z'] ]

