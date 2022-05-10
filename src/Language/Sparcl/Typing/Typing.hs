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

import           Control.Arrow                  (first, (***))
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
import           Data.List                      (nub, (\\))

-- import Control.Exception (evaluate)
-- import           Debug.Trace


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

c2c :: S.TConstraint 'Renaming -> [TyConstraint]
c2c (S.MSub t1 t2) = msub (map ty2ty t1) (map ty2ty t2)
c2c (S.TyEq t1 t2) = [TyEq (ty2ty t1) (ty2ty t2)]

msub :: [Ty] -> [Ty] -> [TyConstraint]
msub ts1 ts2 = [ MSub t1 ts2 | t1 <- ts1 ]

msubMult :: Multiplication -> Multiplication -> [TyConstraint]
msubMult m1 m2 = msub (m2ty m1) (m2ty m2)


tryUnify :: MonadTypeCheck m => Ty -> Ty -> m ()
tryUnify t1 t2 = whenChecking (CheckingEquality t1 t2) $ unify t1 t2


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

ensureRevTy :: MonadTypeCheck m => MonoTy -> m MonoTy
ensureRevTy ty = do
  argTy <- newMetaTy
  tryUnify (revTy argTy) ty
  return argTy

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

hasPRev :: LPat 'Renaming -> Bool
hasPRev (Loc _ p) = go p
  where
    go :: Pat 'Renaming -> Bool
    go (PCon _ ps) = any hasPRev ps
    go (PREV _)    = True
    go _           = False

checkPatsTyK :: MonadTypeCheck m =>
  [LPat 'Renaming] -> [Multiplication] -> [MonoTy] -> m a ->
  m (a, [LPat 'TypeCheck], [(Name,MonoTy,Multiplication)])
checkPatsTyK ps ms ts comp = do
  (cs, ps', bind) <- checkPatsTy ps ms ts
  readConstraint >>= \r -> debugPrint 4 $ red $ "CC:" <+> ppr r
  res <- withVars [ (n,t) | (n,t,_) <- bind ] $
    if null cs then do
      comp
    else do
      (a, ics) <- gatherConstraint $ pushIcLevel comp
      addImpConstraint cs ics
      return a
  readConstraint >>= \r -> debugPrint 4 $ red $ "CC:" <+> ppr r
  return (res, ps', bind)




checkPatsTy :: MonadTypeCheck m =>
  [LPat 'Renaming] -> [Multiplication] -> [MonoTy] ->
  m ([TyConstraint], [LPat 'TypeCheck], [(Name,MonoTy,Multiplication)])
checkPatsTy [] [] [] = return ([], [], [])
checkPatsTy (p:ps) (m:ms) (t:ts) = do
  (cs_ps, ps', bind)  <- checkPatsTy ps ms ts
  (cs_p,  p',  pbind) <- checkPatTy p m t
  return (cs_p ++ cs_ps, p':ps', pbind ++ bind)
checkPatsTy _ _ _ = error "Cannot happen."

checkPatTy :: MonadTypeCheck m =>
              LPat 'Renaming -> Multiplication -> MonoTy ->
              m ([TyConstraint], LPat 'TypeCheck, [(Name, MonoTy, Multiplication)])
checkPatTy = checkPatTyWork False

checkPatTyWork ::
  MonadTypeCheck m =>
  Bool ->
  LPat 'Renaming -> Multiplication -> MonoTy ->
  m ([TyConstraint], LPat 'TypeCheck, [(Name, MonoTy, Multiplication)])
checkPatTyWork isUnderRev (Loc loc pat) pmult patTy = do
  (cs, pat', bind) <- atLoc loc $ go pat
  return (cs, Loc loc pat', bind)
  where
    go (PVar x) =
      return ([], PVar (x, patTy), [(x,patTy, pmult)])

    go (PCon c ps) = do
      ConTy xs ys q_ args_ ret_ <- askConType loc c
      uvars <- mapM (const newMetaTyVar) xs
      evars <- mapM newSkolemTyVar ys

      let tbl = zip xs (map TyMetaV uvars) ++ zip ys (map TyVar evars)
      let q     = map (substTyC tbl) q_
          args  = map (\(t,m) -> (substTy tbl t, substTy tbl m)) args_
          ret   = substTy tbl ret_

      unless (length ps == length args) $ do
        reportError $ Other $ hsep [ "Constructor", ppr c, "takes", ppr (length args), "arguments"
                                   , "but here passed is",  ppr (length ps)]
        abortTyping

      tryUnify ret patTy

      (cs, ps', bind) <-
        foldr (\(csj,pj',bindj) (cs, ps', bind) -> (csj++cs, pj':ps', bindj ++ bind)) ([],[],[]) <$>
        zipWithM (\pj (tj, mj) -> do
                    m <- ty2mult mj
                    checkPatTyWork isUnderRev pj (lub m pmult) tj)
                 ps
                 args

      let tyOfC = foldr (\(t,m) r -> TyCon nameTyArr [m,t,r]) ret args
      return (q++cs, PCon (c, tyOfC) ps', bind)




    go (PREV p) = do
      when isUnderRev $ atLoc (location p) $
        reportError $ Other $ text "rev patterns cannot be nested."

      ty <- ensureRevTy patTy
      (cs, p', bind) <- checkPatTyWork True p pmult ty
      let bind' = map (\(x,t,m) -> (x, revTy t,m)) bind

      forM_ bind' $ \(_, _, m) ->
        -- TODO: Add good error messages.
        addConstraint $ msubMult m one

      return (cs, PREV p', bind')

    go (PWild x) = do -- this is only possible when pmult is omega
      -- tryUnify pmult (TyMult Omega)
      ~(cs, Loc _ (PVar x'), _bind) <- checkPatTyWork isUnderRev (noLoc $ PVar x) omega patTy
      -- cs must be []
      addConstraint $ msubMult omega pmult
      return (cs, PWild x', [] )


solveInferredConstraint :: MonadTypeCheck m => Bool -> [MetaTyVar] -> [TyConstraint] -> [InferredConstraint] -> m [TyConstraint]
solveInferredConstraint raiseError ex given wanted =
  solveInferredConstraintWork raiseError ex [] given wanted

solveInferredConstraintWork :: MonadTypeCheck m => Bool -> [MetaTyVar] -> [TyConstraint] -> [TyConstraint] -> [InferredConstraint] -> m [TyConstraint]
solveInferredConstraintWork raiseError existentials givenSubP given_ wanted_ = do
  given  <- mapM zonkTypeC  given_
  wanted <- mapM zonkTypeIC wanted_

  let givenEq  = [ (t1, t2) | TyEq t1 t2 <- given ]
  let givenSub = [ c | c@(MSub _ _) <- given ]

  curLv <- currentIcLevel
  debugPrint 2 $ red $ brackets (ppr curLv) <+> text "Ex" <+> ppr existentials <> text "." <+> text "Solving" <+> ppr given <+> text "==>" <+> ppr wanted

  -- At this point, it is possible that given constraints have
  -- simplifiable constraints such as C a1 ... an ~ C b1 ... bn
  -- So we perform unify to simplify them.
  --
  -- We believe this process does not perform unification.
  givenEq' <- do
    corig <- readConstraint
    setConstraint []
    mapM_ (uncurry unify) givenEq
    givenEq' <- map (\(ICNormal (TyEq t1 t2)) -> (t1,t2)) <$> readConstraint
    setConstraint corig
    return givenEq'

  -- givenEq' must have the form of either
  --   TyVar   x = ???
  --   TyMetaV x = ??? where x's IC level is smaller than the current

  let (varSubsts, mvarSubsts) = (consec2simul *** consec2simulMeta) $ makeVarSubsts givenEq'

  -- Similarly, we simplify givenSub as possible
  (givenSub', newEq)  <- do
    corig <- readConstraint
    setConstraint []
    gs <- simplifyConstraintsNoRed $ map (substTyC varSubsts . substTyMetaC mvarSubsts) givenSub
    eq' <- map (\(ICNormal (TyEq t1 t2)) -> (t1, t2)) <$> readConstraint
    setConstraint corig
    return (gs, eq')

  let (varSubsts2, mvarSubsts2) = (consec2simul *** consec2simulMeta) $ makeVarSubsts newEq

  debugPrint 4 $ red $ text "Substs" <+> align (sep [ ppr varSubsts,
                                                      ppr mvarSubsts,
                                                      ppr varSubsts2,
                                                      ppr mvarSubsts2 ])


  let newWanted = map (substMetaI mvarSubsts2 . substI varSubsts2 .
                       substMetaI mvarSubsts  . substI varSubsts) wanted

  let givenSubP' = map (substTyMetaC mvarSubsts2 . substTyC varSubsts2 .
                        substTyMetaC mvarSubsts  . substTyC varSubsts) givenSubP


  let weq  = [ (t1,t2) | ICNormal (TyEq t1 t2) <- newWanted, t1 /= t2 ]
      wsub = [ c | ICNormal c@(MSub _ _) <- newWanted ]
      wimp = [ (cs, ics) | ICGuarded cs ics <- newWanted ]

  -- unless (null weq) $
  --   reportError $ ImplicationCheckFail (map (uncurry TyEq) givenEq) (map (uncurry TyEq) weq)

  -- We first solve wanted equality constraints
  eqRenaming <- do
    corig <- readConstraint
    mapM_ (uncurry unify) weq
    res <- map (\(ICNormal c) -> c) <$> readConstraint
    setConstraint corig
    return res

  wsub' <- eliminateExistentialL existentials =<< simplifyConstraints wsub
  subsRemaining <- filterM (\c -> not <$> checkImplication raiseError (givenSub' ++ givenSubP') [c]) wsub'

  let qRem = eqRenaming ++ subsRemaining

  -- We first check implication constraints.
  forM_ wimp $ \(cs', ics') -> do
    curIcLevel <- currentIcLevel
    let existentials' = filter (\x -> metaIcLevel x > curIcLevel) $ metaTyVars ics'
    res <- pushIcLevel $ solveInferredConstraintWork True existentials' (givenSub' ++ givenSubP' ++ qRem) cs' ics'

    unless (null res) $ do
      let normcs = [ c | ICNormal c <- ics' ]
      reportError $ ImplicationCheckFail (cs'++givenSub' ++ givenSubP') normcs
      abortTyping



  return $ qRem


  -- -- TODO : Substitute eq for all others
  -- --        Eliminate existential variables (the same or as equal as the current-level)


  -- debugPrint 2 $ red $ text "Solving" <+> ppr given <+> text "==>" <+> ppr wanted

  -- -- assuming that the current constraint is empty
  -- let eqc  = [ (t1,t2) | ICNormal (TyEq t1 t2) <- wanted ]
  --     subc = [ c | ICNormal c@(MSub _ _) <- wanted ]
  --     impc = [ (cs', ics') | ICGuarded cs' ics' <- wanted ]

  -- -- unify all equality constraints
  -- -- mapM_ (uncurry unify) eqc
  -- -- eqRemaining <- map (\(ICNormal c) -> c) <$> readConstraint
  -- -- setConstraint []
  -- subcSimplified <- simplifyConstraintsNoRed subc
  -- let subsRemaining = filter (\c -> not $ checkImplication given [c]) subcSimplified

  -- forM_ impc $ \(cs', ics') -> do
  --   res <- solveInferredConstraint (cs' ++ given) ics'
  --   unless (null res) $ do
  --     let normcs = [ c | ICNormal c <- ics' ]
  --     reportError $ ImplicationCheckFail (cs'++given) normcs
  --     abortTyping

  -- return $ map (uncurry TyEq) eqc ++ subsRemaining

  where
    substI m (ICNormal c) = ICNormal $ substTyC m c
    substI m (ICGuarded cs ics) = ICGuarded (map (substTyC m) cs) (map (substI m) ics)

    substMetaI m (ICNormal c) = ICNormal $ substTyMetaC m c
    substMetaI m (ICGuarded cs ics) = ICGuarded (map (substTyMetaC m) cs) (map (substMetaI m) ics)

    makeVarSubsts :: [ (Ty, Ty) ] -> ([ (TyVar, Ty) ], [ (MetaTyVar, Ty) ])
    makeVarSubsts [] = ([], [])
    makeVarSubsts ((t1,t2):eqs) =
      let (r1, r2) = makeVarSubsts eqs
      in case (t1, t2) of
           (TyVar x, _)   -> ((x,t2):r1, r2)
           (_, TyVar y)   -> ((y,t1):r1, r2)
           (TyMetaV x, _) -> (r1, (x, t2):r2)
           (_, TyMetaV y) -> (r1, (y, t1):r2)
           (_, _)         -> error "Cannot happen."

  -- rem <- pushIcLevel $ mapM (\(cs',ics') -> simplifyInferredConstraint (given++cs') ics) impc

  -- unless (null rem) $
  --   reportError


simplifyConstraintsNoRed :: MonadTypeCheck m => [TyConstraint] -> m [TyConstraint]
simplifyConstraintsNoRed cs = removeRedundantConstraint =<< simplifyConstraints cs

simplifyConstraints :: MonadTypeCheck m => [TyConstraint] -> m [TyConstraint]
simplifyConstraints constrs = whenChecking (CheckingConstraint constrs) $ go constrs
  where
    go cs = do
      csZonked <- mapM zonkTypeC cs
      cs' <- propagateConstantsToFixedpoint csZonked
      isEffective <- loopToEquiv cs'
      if length cs' < length cs || isEffective
        then go cs'
        else return cs'


checkImplication :: MonadTypeCheck m => Bool -> [TyConstraint] -> [TyConstraint] -> m Bool
checkImplication doesRaiseError given wanted = logBench "imp" $ do
  let prop = toFormula given .&&. SAT.neg (toFormula wanted)
  debugPrint 4 $ red $ vcat [ text "Checking" <+>
                                   align (ppr given </>
                                           "=>" <+> ppr wanted),
                                   "by solving" <+> align (ppr prop)]
  case SAT.sat prop of
       Just _  -> do
         when doesRaiseError $ reportError $ ImplicationCheckFail given wanted
         return False
       Nothing -> return True

-- | Removal of redundant predicate
removeRedundantConstraint :: MonadTypeCheck m => [TyConstraint] -> m [TyConstraint]
removeRedundantConstraint cs_ = do
  cs <- mapM zonkTypeC cs_
  go [] cs
    where
      go proced [] = return (reverse proced)
      go proced (c:cs) = do
        b <- checkImplication False (proced++cs) [c]
        if b
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
      c' <- zonkTypeC c
      case c' of
        MSub t1 ts2 ->
          case ts2 of
            []   -> do
              unify t1 (TyMult One)
              return t
            [t2] | all noTyVar [t1, t2] ->
                   return $ M.insertWith (++) t1 [t2] t
            _    ->
              -- keep t
              return t
        _ ->
          error "makeLeMake: assumes multiplicity constraints."

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
  c' <- zonkTypeC c
  case c' of
    MSub t1 ts2_ -> do
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
    _ ->
      error "propagateConstraints: expects multiplicity contraints."
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

      retTy <- newMetaTy

      ((e', umap), pats', bind) <- checkPatsTyK pats qs' ts $ do
        when (any hasPRev pats) $ void $ ensureRevTy retTy
        checkTy e retTy

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

    go (Let1 p e1 e2) = do
      qPat  <- newMetaTy
      qPat' <- ty2mult qPat

      ty1 <- newMetaTy

      (e1', umap1) <- checkTyM e1 ty1 qPat'

      ((e2', umap2), ~[p'], bind) <- checkPatsTyK [p] [qPat'] [ty1] $ do
        when (hasPRev p) $ void $ ensureRevTy expectedTy
        checkTy e2 expectedTy

      let xqs = map (\(x,_,q) -> (x,q)) bind

      constrainVars xqs umap2
      let umap2' = foldr (M.delete . fst) umap2 xqs

      return (Let1 p' e1' e2', mergeUseMap umap1 umap2')




    go (Con c) = do
      tyOfC <- askType loc c
      t <- instantiate tyOfC
      tryUnify t expectedTy
      return (Con (c, t), M.empty)

    go (Sig e tySyn) = do
      let sigTy = ty2ty tySyn

      -- (e', polyTy, umap) <- inferPolyTy False e
      -- tryCheckMoreGeneral loc polyTy sigTy

      (e', eTy, umap) <- pushLevel $ do
        eTy <- newMetaTy
        (e', umap) <- checkTy e eTy
        return (e', eTy, umap)

      checkGeneralizeTy loc False eTy umap sigTy

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
      (decls', bind, umapLet) <- inferDecls False decls
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

          -- (p', bind)  <- checkPatTy p omega tyE

          -- let xqs = map (\(x,_,q) -> (x,q)) bind

          -- (as', bindAs, umapAs) <- withVars [ (n,t) | (n,t,_) <- bind ] $ goAs as

          ((as', bindAs, umapAs), ~[p'], bind) <- checkPatsTyK [p] [omega] [tyE] $ do
            goAs as
          let xqs = map (\(x,_,q) -> (x,q)) bind


          constrainVars xqs umapAs

          return ((p',e'):as', bindAs ++ bind,
                   mergeUseMap (foldr (M.delete . fst) umapAs xqs) umapE)

checkGeneralizeTy :: MonadTypeCheck m => SrcSpan -> Bool -> MonoTy -> UseMap -> PolyTy -> m ()
checkGeneralizeTy loc isTopLevel ty um polyTy2
  | not isTopLevel, Just monoTy2 <- testMonoTy polyTy2 =
      atLoc loc $ unify ty monoTy2
  | otherwise =
      checkPolyTy loc ty um polyTy2



checkPolyTy :: MonadTypeCheck m => SrcSpan -> MonoTy -> UseMap -> PolyTy -> m ()
checkPolyTy loc ty1_ um polyTy2 = atLoc loc $ do
      debugPrint 4 $ "PolyTy" <+> text (show polyTy2)
      ty1 <- zonkType ty1_
      cs <- mapM zonkTypeIC =<< readConstraint
      setConstraint []

      currentTcLevel <- askCurrentTcLevel
      umapVars <- metaTyVars <$> mapM zonkType [ t | m <- M.elems um, t <- m2ty m ]

      generalizable <-
        filterM (\m -> do
                    lv <- readTcLevelMv m
                    return $ lv > currentTcLevel) ((nub $ metaTyVars ty1 ++ metaTyVars cs) \\ umapVars)



      -- if unification
      let escapedMetaVars = metaTyVars ty1 \\ generalizable

      (skolemTyVars, TyQual given ty2) <- skolemize polyTy2

      readConstraint >>= \r -> debugPrint 4 $ red $ "CC:" <+> ppr r
      unify ty1 ty2
      readConstraint >>= \r -> debugPrint 4 $ red $ "CC:" <+> ppr r

      escapedVars <- freeTyVars <$> mapM zonkMetaTyVar escapedMetaVars

      when (any (`elem` skolemTyVars) escapedVars) $ do
        reportError $ GeneralizeFail ty1 ty2 $ filter (`elem` skolemTyVars) escapedVars

      invisible <- metaTyVars <$> mapM zonkMetaTyVar generalizable

      q <- solveInferredConstraint True invisible given cs

      unless (null q) $ do
        reportError $ ImplicationCheckFail given q






tryGeneralizeTy :: MonadTypeCheck m => Bool -> MonoTy -> UseMap -> m PolyTy
tryGeneralizeTy isTopLevel ty_ u = do
  if isTopLevel
    then generalizeTy ty_ u
    else do
    ty <- zonkType ty_
    debugPrint 3 $ "Generalization of" <+> ppr ty <+> "is suppressed."
    return ty

-- NB: @generalizeTy@ makes the current constraint empty
generalizeTy :: MonadTypeCheck m => MonoTy -> UseMap -> m PolyTy
generalizeTy ty_ um = do
  cs  <- readConstraint
  setConstraint []

  q <- solveInferredConstraint False [] [] cs

  ty <- zonkType ty_

  currentTcLevel <- askCurrentTcLevel
  umapVars <- metaTyVars <$> mapM zonkType [ t | m <- M.elems um, t <- m2ty m ]

  let qty = TyQual q ty

  generalizable <-
        filterM (\m -> do
                    lv <- readTcLevelMv m
                    return $ lv > currentTcLevel) (metaTyVars qty \\ umapVars)

  -- Generalization captures all the constraints
  let qty' = TyQual q ty


  polyTy <- quantify generalizable qty'
  debugPrint 2 $ text "Gen" <> brackets (text $ show currentTcLevel) <> text ":" <+>
    align (vsep [ text "Generalizable" <+> ppr generalizable,
                  group (align (group (ppr qty) <> line <> text "-->" <> line <> group (ppr polyTy))) ])

  setConstraint []

  return polyTy
  -- where
  --   refersTo :: TyConstraint -> [MetaTyVar] -> Bool
  --   refersTo (MSub m ms)  vs = any (`elem` vs) $ metaTyVars (m:ms)
  --   refersTo (TyEq t1 t2) vs = any (`elem` vs) $ metaTyVars [t1,t2]


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
      -- (pat', bind) <- checkPatTy pat q patTy
      -- (c', umap)   <- withVars [ (n,t) | (n,t,_) <- bind ] $ checkClauseTy c bodyTy

      ~((c', umap), [pat'], bind) <- checkPatsTyK [pat] [q] [patTy] $ do
          when (hasPRev pat) $ void $ ensureRevTy bodyTy
          checkClauseTy c bodyTy

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





inferDecls :: MonadTypeCheck m =>
  Bool -> -- is top level
  Decls 'Renaming (LDecl 'Renaming) ->
  m (Decls 'TypeCheck (LDecl 'TypeCheck), [(Name, PolyTy)], UseMap)
inferDecls _ (Decls v _) = absurd v
inferDecls isTopLevel (HDecls _ dss) = do
  (dss', bind , umap) <- go [] dss
  return (HDecls () dss', bind, umap )
  where
    go bs [] = return ([], bs, M.empty)
    go bs (ds:rest) = do
      (ds', bind,  umap)  <- inferMutual isTopLevel ds
      (rest', bs', umap') <- withVars bind $ go (bind ++ bs) rest
      return (ds':rest', bs', mergeUseMap umap umap')


inferTopDecls ::
  MonadTypeCheck m =>
  Decls 'Renaming (LDecl 'Renaming) ->
  [Loc (Name, [Name], [Loc (CDecl 'Renaming)])] ->
  [Loc (Name, [Name], LTy 'Renaming)] ->
  m ( Decls 'TypeCheck (LDecl 'TypeCheck), [(Name, PolyTy)],
      [C.DDecl Name],
      [C.TDecl Name],
      CTypeTable, SynTable)
inferTopDecls decls dataDecls typeDecls = do
  let dataDecls' = [ C.DDecl n (map BoundTv ns) [ convConDecl cd | Loc _ cd <- cdecls ]
                   | Loc _ (n,ns,cdecls) <- dataDecls ]

  let typeDecls' = [ C.TDecl n (map BoundTv ns) (ty2ty lty) | Loc _ (n, ns, lty) <- typeDecls ]

  let synTable = M.fromList $
        flip map typeDecls $ \(Loc _ (n, ns, lty)) ->
                               let ty = ty2ty lty
                               in (n, (map BoundTv ns, ty))


  let ctypeTable = M.fromList $ concat [ mkConTable (n, ns, cdecls) | Loc _ (n, ns, cdecls) <- dataDecls ]
        -- [ (n, foldr ((-@) . const typeKi) typeKi ns) | Loc _ (n, ns, _) <- dataDecls ]
        -- ++
        -- [ (cn, TyForAll tvs $ TyQual [] (foldr ((-@) . ty2ty) (TyCon n $ map TyVar tvs) tys)) |
        --   Loc _ (n, ns, cdecls) <- dataDecls,
        --   let tvs = map BoundTv ns,
        --   Loc _ (CDecl cn tys) <- cdecls ]

  withCons (M.toList ctypeTable) $
   withSyns (M.toList synTable) $ do
     (decls', nts, _) <- inferDecls True decls
     -- liftIO $ putStrLn $ show cs
     return (decls', nts, dataDecls', typeDecls', ctypeTable, synTable)
  where
    convConDecl (NormalC  cn      tys) = (cn, [], [], map ty2ty tys)
    convConDecl (GeneralC cn xs q tys) = (cn, xs, concatMap c2c q, map (ty2ty . fst) tys)

    mkConTable (n, ns, cdecls) =
      let tvs = map BoundTv ns
          retTy = TyCon n $ map TyVar tvs
      in flip map cdecls $ \case (Loc _ (NormalC cn tys)) ->
                                   (cn, ConTy tvs [] [] [(ty2ty ty, TyMult one) | ty <- tys] retTy)
                                 (Loc _ (GeneralC cn xs q tyms)) ->
                                   let xs'   = map BoundTv xs
                                       q'    = concatMap c2c q
                                       tyms' = map (\(t,m) -> (ty2ty t, ty2ty m)) tyms
                                   in (cn, ConTy tvs xs' q' tyms' retTy)



inferMutual :: MonadTypeCheck m =>
               Bool -> --
               [LDecl 'Renaming] -> m ([LDecl 'TypeCheck], [(Name, PolyTy)], UseMap)
inferMutual isTopLevel decls = do
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

    res <- case M.lookup n sigMap of
      Nothing    -> do
        -- NB: No type variables exacpe in the useMap so using emptyUseMap is OK.
        polyTy <- tryGeneralizeTy isTopLevel ty emptyUseMap
        return (n, loc, polyTy, pcs')
      Just sigTy -> do
        -- if a function comes with a signature, we check that its inferred type is more polymorphic than
        -- the signature
        checkGeneralizeTy loc isTopLevel ty emptyUseMap sigTy
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
        retTy <- newMetaTy

        -- (ps', bind) <- checkPatsTy ps muls tys
        -- (c', umap) <- withVars [ (n,t) | (n,t,_) <- bind ] $ checkClauseTy c retTy

        ((c', umap), ps', bind) <- checkPatsTyK ps muls tys $ do
            when (any hasPRev ps) $ void $ ensureRevTy retTy
            checkClauseTy c retTy

        tryUnify (foldr (uncurry tyarr) retTy $ zip qs tys) expectedTy

        let umap' = raiseUse omega umap

        let xqs = map (\(x,_,q) -> (x,q)) bind

        constrainVars xqs umap
        return ((ps', c'), foldr (M.delete . fst) umap' xqs)


checkClauseTy :: MonadTypeCheck m => Clause 'Renaming -> Ty -> m (Clause 'TypeCheck, UseMap)
checkClauseTy (Clause e ws wi) expectedTy = do
  (ws', bind, umap) <- inferDecls False ws
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
  sks <- localIcLevel (const $ (-1)) $ mapM newSkolemTyVar tvs
  return (sks, substTyQ (zip tvs $ map TyVar sks) ty)
skolemize ty = return ([], TyQual [] ty)

-- tryCheckMoreGeneral :: MonadTypeCheck m => SrcSpan -> Ty -> Ty -> m ()
-- tryCheckMoreGeneral loc ty1 ty2 = -- do
--   -- cl <- currentLevel
--   -- debugPrint 2 $ text "tryCheckMoreGeneral is called" <+> brackets (ppr cl) <+> text "to check" </>
--   --                ppr ty1 <+> text "<=" <+> ppr ty2
--   -- liftIO $ print $ red $ group $ text "Checking" <+> align (ppr ty1 <+>  text "is more general than" <> line <> ppr ty2)
--   whenChecking (CheckingMoreGeneral ty1 ty2) $ pushLevel $ checkMoreGeneral loc ty1 ty2

-- -- todo: delay implication checking until

-- checkMoreGeneral :: MonadTypeCheck m => SrcSpan -> PolyTy -> PolyTy -> m ()
-- checkMoreGeneral loc polyTy1 polyTy2@(TyForAll _ _) = do
--   -- liftIO $ print $ hsep [ text "Signature:", ppr polyTy2 ]
--   -- liftIO $ print $ hsep [ text "Inferred: ", ppr polyTy1 ]
--   (skolemTyVars, ty2) <- skolemize polyTy2

--   -- cl <- currentLevel
--   -- debugPrint 2 $ text "check starts" <+> brackets (ppr cl)

--   -- liftIO $ print $ hsep [ text "Skolemized sig:", ppr ty2 ]

--   checkMoreGeneral2 loc polyTy1 ty2
--   escapedTyVars <- freeTyVars <$> zonkType polyTy1

--   let badTyVars = filter (`elem` escapedTyVars) skolemTyVars
--   unless (null badTyVars) $
--     reportError $ Other $ D.group $
--       D.hcat [ D.text "The inferred type",
--                D.nest 2 (D.line D.<> D.dquotes (D.align $ ppr polyTy1)),
--                D.line <> D.text "is not polymorphic enough for:",
--                D.nest 2 (D.line D.<> D.dquotes (D.align $ ppr polyTy2)) ]

-- checkMoreGeneral loc polyTy1 ty = checkMoreGeneral2 loc polyTy1 (TyQual [] ty)

-- checkMoreGeneral2 :: MonadTypeCheck m => SrcSpan -> Ty -> QualTy -> m ()
-- checkMoreGeneral2 loc polyTy1@(TyForAll _ _) ty2 = do

--   -- -- it could be possible that the function is called
--   -- -- polyTy that can contain meta type variables.
--   let origVars = metaTyVars [polyTy1]

--   TyQual cs ty1 <- instantiateQ polyTy1
--   checkMoreGeneral3 loc origVars (TyQual cs ty1) ty2

-- checkMoreGeneral2 loc ty1 ty2 = checkMoreGeneral3 loc (metaTyVars [ty1]) (TyQual [] ty1) ty2

-- checkMoreGeneral3 :: MonadTypeCheck m => SrcSpan -> [MetaTyVar] -> QualTy -> QualTy -> m ()
-- checkMoreGeneral3 loc origVars (TyQual cs1 ty1) (TyQual cs2 ty2) = atLoc loc $ do
--   atLoc loc $ unify ty1 ty2

--   -- liftIO $ print $ red $ group $ text "Checking mono type" <+> align (ppr (TyQual cs1 ty1) <+>  text "is more general than" <> line <> ppr (TyQual cs2 ty2))
--   checkImplicationD origVars cs2 cs1


-- checkImplicationD :: MonadTypeCheck m => [MetaTyVar] -> [TyConstraint] -> [TyConstraint] -> m ()
-- checkImplicationD origVars csGiven csWanted = do
--   cs1' <- simplifyConstraints =<< mapM zonkTypeC csWanted
--   cs2' <- simplifyConstraints =<< mapM zonkTypeC csGiven

--   let cs1'' = filter (not . (`elem` cs2')) cs1'

--   let undetermined = metaTyVars (cs1'' ++ cs2') \\ origVars
--   -- undetermined <- filterM (\mv -> readTcLevelMv mv >>= \i -> return (i >= cLevel)) $ metaTyVarsC (cs1''++cs2')

--   let cs1''' = eliminateExistential undetermined cs1''

--   check undetermined cs2' cs1'''
--   where
--     -- NB: The type signature matters here.
--     check :: MonadTypeCheck m => [MetaTyVar] -> [TyConstraint] -> [TyConstraint] -> m ()
--     check undetermined given wanted = do
--       -- g <- simplifyConstraints =<< mapM zonkTypeC given
--       -- w <- simplifyConstraints =<< mapM zonkTypeC wanted

--       g0 <- mapM zonkTypeC given
--       w0 <- mapM zonkTypeC wanted

--       -- We skip the trivial case.
--       unless (null w0) $ do
--         cLevel <- currentLevel
--         lv <- lvToCheck g0 w0

--         if lv == cLevel || lv == maxBound
--           then do -- We are ready for checking
--           g <- simplifyConstraints g0
--           w <- simplifyConstraints w0

--           let prop = toFormula g .&&. SAT.neg (toFormula w)
--           debugPrint 2 $ nest 2 $
--             text "Implicating Check:" <> brackets (ppr cLevel) <> line <>
--             vcat [text "Wanted:" <+> ppr w,
--                   text "Given: " <+> ppr g,
--                   text "EVars: " <+> ppr undetermined,
--                   text "Prop:  " <+> ppr prop]

--           case SAT.sat prop of
--             Nothing -> return ()
--             Just bs ->
--               reportError $ Other $ D.group $
--               vcat [ hsep [pprC csGiven, text "does not imply", pprC csWanted]
--                      <> (if null undetermined then empty
--                          else line <> text "with any choice of" <+> ppr undetermined),
--                      nest 2 (vcat [ text "a concrete counter example:",
--                                     vcat (map pprS bs) ]) ]
--           else do -- We are not ready to check the implication as there are undetermined variables.
--           debugPrint 4 $ red $ text "Check:" <+> ppr g0 <+> text "=>" <+> ppr w0 <+> text "is deferred" <+> ppr cLevel <+> text "-->" <+> ppr lv
--           defer $ SuspendedCheck (check undetermined g0 w0)


--     -- freeTyVarsC cs = concat <$> mapM (\(MSub m ms) -> freeTyVars (m:ms)) cs


--     lvToCheck :: MonadTypeCheck m => [TyConstraint] -> [TyConstraint] -> m TcLevel
--     lvToCheck cs1 cs2 = tcLevel (cs1 ++ cs2)

--     pprS (x, b) = ppr x <+> text "=" <+> text (if b then "Omega" else "One")
--     pprC = parens . hsep . punctuate comma . map ppr


data VV = MV !MetaTyVar | SV !TyVar
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
    toForm (TyEq t1 t2) =
      -- This is OK. t1 and t2 are assumed to be type variables.
      (conv t1 .<=>. conv t2)
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
eliminateExistentialM :: [MetaTyVar] -> [(Ty, [Ty])] -> [(Ty,[Ty])]
eliminateExistentialM []     cs = cs
eliminateExistentialM (r:rs) cs =
  let (csOne, qss, csRest) = splitCs cs
  in eliminateExistentialM rs ([ (m, ms ++ qs) | (m, ms) <- csOne, qs <- qss ] ++ csRest)
  where
    splitCs :: [(Ty,[Ty])] -> ([(Ty,[Ty])], [[Ty]], [(Ty,[Ty])])
    splitCs [] = ([], [], [])
    splitCs ((q, qs):rest)
      | rInQ , rInQs = (r1, r2,    r3)
      | rInQ         = (r1, qs:r2, r3) -- but not rInQs
      | rInQs        = ((q, qs \\ [TyMetaV r]):r1, r2, r3)
      | otherwise    = (r1, r2, (q, qs):r3)
      where
        (r1, r2, r3) = splitCs rest
        rInQ  = r `elem` metaTyVars [q]
        rInQs = r `elem` metaTyVars qs

eliminateExistential :: [MetaTyVar] -> [TyConstraint] -> [TyConstraint]
eliminateExistential vars cs =
  let subs = [ (q,qs) | MSub q qs <- cs ]
      eqs  = [ c | c@(TyEq _ _) <- cs ]
      subs' = eliminateExistentialM vars subs
  in map (uncurry MSub) subs' ++ eqs

-- eliminateInvisible :: [MetaTyVar] -> QualTy -> ([MetaTyVar],  QualTy)
-- eliminateInvisible mvs (TyQual cs t) =
--   -- Assumption: @mvs@ is a set of variables to be generalized.
--   let visibleVars = nub $ metaTyVars [t] ++ concatMap gatherMvInTyEq cs
--       invisibles  = mvs \\ visibleVars
--       cs' = eliminateExistential invisibles cs
--   in (mvs \\ invisibles, TyQual cs' t)
--   where
--     gatherMvInTyEq (TyEq t1 t2) = metaTyVars [t1,t2]
--     gatherMvInTyEq _            = []

eliminateExistentialL :: MonadTypeCheck m => [MetaTyVar] -> [TyConstraint] -> m [TyConstraint]
eliminateExistentialL vars cs =
  logBenchN "qe" (length vars) $ do
    let cs' = eliminateExistential vars cs
    seq cs' (return cs')


quantify :: MonadTypeCheck m => [MetaTyVar] -> QualTy -> m PolyTy
quantify mvs0 ty0 = do
  -- debugPrint 2 $ red $ text "Simpl:" <+> align (group (ppr (mvs0, ty0)) <> line <> text "-->" <> line <> group (ppr (mvs, ty)))
  -- liftIO $ print $ red $ "Generalization:" <+> ppr (zip mvs newBinders)

  (mvs, ty) <- do
    let TyQual cs0 t0 = ty0
        visibleVars = nub $ metaTyVars [t0] ++ concatMap gatherMvInTyEq cs0
        invisibles  = mvs0 \\ visibleVars
    cs <-  eliminateExistentialL invisibles cs0
    return (mvs0 \\ invisibles, TyQual cs t0)

  let usedBinders = bindersQ ty
      newBinders  = take (length mvs) $ allFancyBinders \\ usedBinders


  forM_ (zip mvs newBinders) $
    \(mv, tyv) -> writeTyVar mv (TyVar tyv)
  ty' <- zonkTypeQ ty
  return $ TyForAll newBinders ty'
  where
    gatherMvInTyEq (TyEq t1 t2) = metaTyVars [t1,t2]
    gatherMvInTyEq _            = []

    binders (TyForAll bs t) = bs ++ bindersQ t
    binders (TyCon _ ts)    = concatMap binders ts
    binders (TyVar _)       = []
    binders (TySyn t  _)    = binders t
    binders (TyMetaV _)     = []
    binders (TyMult _)      = []

    bindersQ (TyQual cs t) = concatMap bindersC cs ++ binders t

    bindersC (MSub t1 ts2) = binders t1 ++ concatMap binders ts2
    bindersC (TyEq t1 t2)  = binders t1 ++ binders t2

allFancyBinders :: [TyVar]
allFancyBinders = map (BoundTv . Local . User) $
  [ [x] | x <- ['a'..'z'] ] ++
  [ x : show i | i <- [1::Integer ..], x <- ['a'..'z'] ]

