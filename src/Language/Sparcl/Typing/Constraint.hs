{-# LANGUAGE OverloadedStrings #-}

module Language.Sparcl.Typing.Constraint where

import Control.Arrow ((***))

import qualified Data.Graph as G
import qualified Data.Map as M

import Language.Sparcl.DebugPrint
import Language.Sparcl.Multiplicity
import Language.Sparcl.Pretty as D hiding ((<$>))
import Language.Sparcl.Typing.TCMonad
import Language.Sparcl.Typing.Type

import Control.Monad (filterM, foldM, forM_, unless, when)
import Data.List ((\\))
import Language.Sparcl.Algorithm.SAT as SAT

solveInferredConstraint :: Bool -> [MetaTyVar] -> [TyConstraint] -> [InferredConstraint] -> TC [TyConstraint]
solveInferredConstraint raiseError ex given wanted =
  solveInferredConstraintWork raiseError ex [] given wanted

solveInferredConstraintWork :: Bool -> [MetaTyVar] -> [TyConstraint] -> [TyConstraint] -> [InferredConstraint] -> TC [TyConstraint]
solveInferredConstraintWork raiseError existentials givenSubP given_ wanted_ = do
  given <- mapM zonkTypeC given_
  wanted <- mapM zonkTypeIC wanted_

  let givenEq = [(t1, t2) | TyEq t1 t2 <- given]
  let givenSub = [c | c@(MSub _ _) <- given]

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
    givenEq' <- map (\(ICNormal (TyEq t1 t2)) -> (t1, t2)) <$> readConstraint
    setConstraint corig
    return givenEq'

  -- givenEq' must have the form of either
  --   TyVar   x = ???
  --   TyMetaV x = ??? where x's IC level is smaller than the current

  let (varSubsts, mvarSubsts) = (consec2simul *** consec2simulMeta) $ makeVarSubsts givenEq'

  -- Similarly, we simplify givenSub as possible
  (givenSub', newEq) <- do
    corig <- readConstraint
    setConstraint []
    gs <- simplifyConstraintsNoRed $ map (substTyC varSubsts . substTyMetaC mvarSubsts) givenSub
    eq' <- map (\(ICNormal (TyEq t1 t2)) -> (t1, t2)) <$> readConstraint
    setConstraint corig
    return (gs, eq')

  let (varSubsts2, mvarSubsts2) = (consec2simul *** consec2simulMeta) $ makeVarSubsts newEq

  debugPrint 4 $
    red $
      text "Substs"
        <+> align
          ( sep
              [ ppr varSubsts
              , ppr mvarSubsts
              , ppr varSubsts2
              , ppr mvarSubsts2
              ]
          )

  let newWanted =
        map
          ( substMetaI mvarSubsts2
              . substI varSubsts2
              . substMetaI mvarSubsts
              . substI varSubsts
          )
          wanted

  let givenSubP' =
        map
          ( substTyMetaC mvarSubsts2
              . substTyC varSubsts2
              . substTyMetaC mvarSubsts
              . substTyC varSubsts
          )
          givenSubP

  let weq = [(t1, t2) | ICNormal (TyEq t1 t2) <- newWanted, t1 /= t2]
      wsub = [c | ICNormal c@(MSub _ _) <- newWanted]
      wimp = [(cs, ics) | ICGuarded cs ics <- newWanted]

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
      let normcs = [c | ICNormal c <- ics']
      reportError $ ImplicationCheckFail (cs' ++ givenSub' ++ givenSubP') normcs
      abortTyping

  return $ qRem
  where
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

    substI m (ICNormal c) = ICNormal $ substTyC m c
    substI m (ICGuarded cs ics) = ICGuarded (map (substTyC m) cs) (map (substI m) ics)

    substMetaI m (ICNormal c) = ICNormal $ substTyMetaC m c
    substMetaI m (ICGuarded cs ics) = ICGuarded (map (substTyMetaC m) cs) (map (substMetaI m) ics)

    makeVarSubsts :: [(Ty, Ty)] -> ([(TyVar, Ty)], [(MetaTyVar, Ty)])
    makeVarSubsts [] = ([], [])
    makeVarSubsts ((t1, t2) : eqs) =
      let (r1, r2) = makeVarSubsts eqs
      in  case (t1, t2) of
            (TyVar x, _) -> ((x, t2) : r1, r2)
            (_, TyVar y) -> ((y, t1) : r1, r2)
            (TyMetaV x, _) -> (r1, (x, t2) : r2)
            (_, TyMetaV y) -> (r1, (y, t1) : r2)
            (_, _) -> error "Cannot happen."

-- rem <- pushIcLevel $ mapM (\(cs',ics') -> simplifyInferredConstraint (given++cs') ics) impc

-- unless (null rem) $
--   reportError

simplifyConstraintsNoRed :: [TyConstraint] -> TC [TyConstraint]
simplifyConstraintsNoRed cs = removeRedundantConstraint =<< simplifyConstraints cs

simplifyConstraints :: [TyConstraint] -> TC [TyConstraint]
simplifyConstraints constrs = whenChecking (CheckingConstraint constrs) $ go constrs
  where
    go cs = do
      csZonked <- mapM zonkTypeC cs
      cs' <- propagateConstantsToFixedpoint csZonked
      isEffective <- loopToEquiv cs'
      if length cs' < length cs || isEffective
        then go cs'
        else return cs'

checkImplication :: Bool -> [TyConstraint] -> [TyConstraint] -> TC Bool
checkImplication doesRaiseError given wanted = logBench "imp" $ do
  let prop = toFormula given .&&. SAT.neg (toFormula wanted)
  debugPrint 4 $
    red $
      vcat
        [ text "Checking"
            <+> align
              ( ppr given
                  </> "=>"
                  <+> ppr wanted
              )
        , "by solving" <+> align (ppr prop)
        ]
  case SAT.sat prop of
    Just _ -> do
      when doesRaiseError $ reportError $ ImplicationCheckFail given wanted
      return False
    Nothing -> return True

-- | Removal of redundant predicate
removeRedundantConstraint :: [TyConstraint] -> TC [TyConstraint]
removeRedundantConstraint cs_ = do
  cs <- mapM zonkTypeC cs_
  go [] cs
  where
    go proced [] = return (reverse proced)
    go proced (c : cs) = do
      b <- checkImplication False (proced ++ cs) [c]
      if b
        then go proced cs -- c is redundant
        else go (c : proced) cs -- c

-- | The function yield equality constraints by detecting loops in the dependency.
--   For example, from the constraint a = max b c and b = max a d, we can conclude
--   a = b as we have b <= a, c <= a, a <= b, d <= b from the constraint.
--
--   The function returns true if it yields at least one equality constraint.
loopToEquiv :: [TyConstraint] -> TC Bool
loopToEquiv constraints = do
  sccs <- makeSCC constraints
  -- liftIO $ print $ red $ text "CS:" <+> ppr constraints
  -- liftIO $ print $ red $ text "SCC" <+> (align $ vcat $ map (\case G.AcyclicSCC x -> text "Acyc" <+> ppr x
  --                                                                  G.CyclicSCC x  -> text "Cyc " <+> ppr x) sccs)
  foldM procSCCs False sccs
  where
    procSCCs :: Bool -> G.SCC Ty -> TC Bool
    procSCCs isE (G.AcyclicSCC _) = return isE
    procSCCs isE (G.CyclicSCC [_]) = return isE
    procSCCs _isE (G.CyclicSCC xs) =
      equate xs >> return True

    equate [] = error "Cannot happen."
    equate (ty : tys) = do
      debugPrint 2 $ text "Equating" <+> ppr (ty : tys)
      forM_ tys $ \ty' -> unify ty ty'

    makeSCC :: [TyConstraint] -> TC [G.SCC Ty]
    makeSCC xs = G.stronglyConnComp . map (\(k, vs) -> (k, k, vs)) . M.toList <$> makeLeMap xs

    makeLeMap :: [TyConstraint] -> TC (M.Map Ty [Ty])
    makeLeMap [] = return M.empty
    makeLeMap (c : cs) = do
      t <- makeLeMap cs
      c' <- zonkTypeC c
      case c' of
        MSub t1 ts2 ->
          case ts2 of
            [] -> do
              unify t1 (TyMult One)
              return t
            [t2]
              | all noTyVar [t1, t2] ->
                  return $ M.insertWith (++) t1 [t2] t
            _ ->
              -- keep t
              return t
        _ ->
          error "makeLeMake: assumes multiplicity constraints."

    noTyVar (TyVar _) = False
    noTyVar (TyMult _) = True
    noTyVar (TyMetaV _) = True
    noTyVar _ = error "Cannot happen."

-- MEqMax t1' t2' t3' <- zonkTypeC c
-- return $ M.insertWith (++) t2' [t1'] $ M.insertWith (++) t3' [t1'] t

propagateConstantsToFixedpoint :: [TyConstraint] -> TC [TyConstraint]
propagateConstantsToFixedpoint xs = do
  ys <- propagateConstants xs
  if length xs > length ys
    then propagateConstantsToFixedpoint ys
    else return ys

propagateConstants :: [TyConstraint] -> TC [TyConstraint]
propagateConstants [] = return []
propagateConstants (c : cs) = do
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
        (_, _)
          | t1 `elem` ts2 ->
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
        go (TyMult One : ts) = go ts
        go (t : ts) = case go ts of
          [TyMult Omega] -> [TyMult Omega]
          [TyMult One] -> [t]
          ts' -> t : ts'

-- |
-- The following function @eliminateExitential@ effectively eliminates existentials in contraints.
--
-- The elimination is based on the fact that disjunction of a definite
-- clause and a goal clause result in a definite clause. Notice that
-- contraint
--
-- @
-- MSub m [m1, ..., mn]
-- @
--
-- can be seen as a dual Horn clause @~m | m1 | m2 | ... | mn@.
--
-- Thus, take a dijunction of the above and
-- @
-- MSub Omega [n1,...,nk]
-- @
--
-- results in the following predicate.
--
-- @
-- MSub m [m1,...,mn,n1,...,nk]
-- @
--
-- Then, revisit the original problem of eliminating @r@ in @exists
-- r. C@. This can be done simplify by @C[r = One] \/ C[r = Omega]@.
--
-- Then, we do the elimination in three steps.
--
-- 1. Split @C@ into the following.
--
-- @
-- C1 = [ MSub m [m1,..,mi-1,mi+1,...,mn] | MSub m ms in C, mi = r, m /= r ]
-- Co = [ ms | MSub m ms in C, m = r ]
-- Cr = [ c | c in C, not (r `elem` metaTyVarsC c) ]
-- @
--
-- 2. Compute
-- @
-- C' = [ MSub m (ms ++ ns) | MSub m ms <- C1, MSub _ ms <- Co ]
-- @
--
-- 3. Then, return @C', Cr@.

-- Assumption: constraints are zonked.
eliminateExistentialM :: [MetaTyVar] -> [(Ty, [Ty])] -> [(Ty, [Ty])]
eliminateExistentialM [] cs = cs
eliminateExistentialM (r : rs) cs =
  let (csOne, qss, csRest) = splitCs cs
  in  eliminateExistentialM rs ([(m, ms ++ qs) | (m, ms) <- csOne, qs <- qss] ++ csRest)
  where
    splitCs :: [(Ty, [Ty])] -> ([(Ty, [Ty])], [[Ty]], [(Ty, [Ty])])
    splitCs [] = ([], [], [])
    splitCs ((q, qs) : rest)
      | rInQ, rInQs = (r1, r2, r3)
      | rInQ = (r1, qs : r2, r3) -- but not rInQs
      | rInQs = ((q, qs \\ [TyMetaV r]) : r1, r2, r3)
      | otherwise = (r1, r2, (q, qs) : r3)
      where
        (r1, r2, r3) = splitCs rest
        rInQ = r `elem` metaTyVars [q]
        rInQs = r `elem` metaTyVars qs

eliminateExistential :: [MetaTyVar] -> [TyConstraint] -> [TyConstraint]
eliminateExistential vars cs =
  let subs = [(q, qs) | MSub q qs <- cs]
      eqs = [c | c@(TyEq _ _) <- cs]
      subs' = eliminateExistentialM vars subs
  in  map (uncurry MSub) subs' ++ eqs

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

eliminateExistentialL :: [MetaTyVar] -> [TyConstraint] -> TC [TyConstraint]
eliminateExistentialL vars cs =
  logBenchN "qe" (length vars) $ do
    let cs' = eliminateExistential vars cs
    seq cs' (return cs')

data VV = MV !MetaTyVar | SV !TyVar
  deriving (Eq, Ord)

instance Pretty VV where
  pprPrec k (MV v) = pprPrec k v
  pprPrec k (SV v) = pprPrec k v

toFormula :: [TyConstraint] -> SAT.Formula VV
toFormula [] = SAT.true
toFormula (c : cs) =
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
    conv (TyMult One) = SAT.false
    conv (TyMetaV v) = SAT.var (MV v)
    conv (TyVar v) = SAT.var (SV v)
    conv t = error $ show $ hsep [ppr t, text " is not a multiplicity"]
