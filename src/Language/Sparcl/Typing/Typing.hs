{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns #-}

module Language.Sparcl.Typing.Typing (
  inferExp,
  inferTopDecls,
) where

import Control.Monad
import Control.Monad.Except
import Control.Monad.IO.Class (liftIO)
import Control.Monad.Reader (asks)
import Data.IORef (newIORef, readIORef)
import Data.Maybe (catMaybes, fromMaybe)
import Data.Void

-- import Control.Monad.Writer

import qualified Data.Map as M

import Control.Arrow (first)

import Language.Sparcl.Literal
import Language.Sparcl.Multiplicity
import Language.Sparcl.Name
import Language.Sparcl.Pass
import Language.Sparcl.SrcLoc
import Language.Sparcl.Surface.Syntax hiding (
  TConstraint (..),
  Ty (..),
 )
import Language.Sparcl.Typing.Constraint
import Language.Sparcl.Typing.Instance
import Language.Sparcl.Typing.TCMonad
import Language.Sparcl.Typing.Type

import qualified Language.Sparcl.Core.Syntax as C (DDecl (..), TDecl (..))

import Language.Sparcl.DebugPrint
import Language.Sparcl.Exception (cannotHappen)
import qualified Language.Sparcl.Surface.Syntax as S

import Language.Sparcl.Pretty as D hiding ((<$>))

-- import Data.Maybe (isNothing)

import Data.List (foldl', nub, (\\))

-- import Control.Exception (evaluate)
-- import           Debug.Trace

-- TODO: Implement kind checking
ty2ty :: S.LTy 'Renaming -> Ty
ty2ty (Loc _ ty) = go ty
  where
    go (S.TVar x) = TyVar (BoundTv x)
    go (S.TCon c ts) = TyCon c $ map ty2ty ts
    go (S.TForall x t) = gatherBoundTv [BoundTv x] t
    go (S.TMult m) = TyMult m
    go t@(S.TQual _ _) =
      let (t', cs') = gatherConstraints t
      in  TyForAll [] $ TyQual cs' t'

    gatherBoundTv xs (unLoc -> S.TForall y t) = gatherBoundTv (BoundTv y : xs) t
    gatherBoundTv xs t =
      let (t', cs) = gatherConstraintsL t
      in  TyForAll (reverse xs) $ TyQual cs t'

    gatherConstraintsL = gatherConstraints . unLoc

    gatherConstraints (S.TVar x) = (TyVar (BoundTv x), [])
    gatherConstraints (S.TCon c ts) =
      let tcs = map gatherConstraintsL ts
      in  (TyCon c (map fst tcs), concatMap snd tcs)
    gatherConstraints (S.TForall x t) = (gatherBoundTv [BoundTv x] t, [])
    gatherConstraints (S.TQual cs t) =
      let (t', cs') = gatherConstraintsL t
      in  (t', concatMap c2c cs ++ cs')
    gatherConstraints (S.TMult m) = (TyMult m, [])

c2c :: S.TConstraint 'Renaming -> [TyConstraint]
c2c (S.MSub t1 t2) = msub (map ty2ty t1) (map ty2ty t2)
c2c (S.TyEq t1 t2) = [TyEq (ty2ty t1) (ty2ty t2)]

msub :: [Ty] -> [Ty] -> [TyConstraint]
msub ts1 ts2 = [MSub t1 ts2 | t1 <- ts1]

msubMult :: Multiplication -> Multiplication -> [TyConstraint]
msubMult m1 m2 = msub (m2ty m1) (m2ty m2)

tryUnify :: Ty -> Ty -> TC ()
tryUnify t1 t2 = whenChecking (CheckingEquality t1 t2) $ unify t1 t2

-- See subsCheckSigma in S. Peyton Jones+: Practical type inference for arbitrary-rank types, JFP 2007
subsumptionCheckPoly :: Bool -> PolyTy -> PolyTy -> TC ()
subsumptionCheckPoly isRightGiven ty1 polyTy2 = do
  debugPrint 2 $ text "subsumptionCheckPoly: checking" <+> ppr ty1 <+> "is at least as polymorphic as" <+> ppr polyTy2

  -- save the current constraints, as checking discharges constraints in ty1
  (skolTyVars, TyQual given ty2) <- skolemize polyTy2

  (_, cs) <- gatherConstraint $ subsumptionCheckBody isRightGiven ty1 ty2

  debugPrint 2 $ text "subsumptionCheckPoly: " <> ppr given <+> "==>" <+> ppr cs

  currentTcLevel <- askCurrentTcLevel
  invisibleMetaVars <-
    filterM
      ( \m -> do
          lv <- readTcLevelMv m
          return $ lv > currentTcLevel
      )
      (nub $ metaTyVars cs ++ metaTyVars ty1)

  -- Constrain given => cs holds.
  if null given
    then do csOrig <- readConstraint; setConstraint (cs ++ csOrig)
    else addImpConstraint invisibleMetaVars given cs

  -- q <- solveInferredConstraint True [] given cs

  -- unless (null q) $ do
  --   debugPrint 2 $ text "implication failure at subsumptionCheckPoly"
  --   reportError $ ImplicationCheckFail given q

  ftyVars <- freeTyVars <$> mapM zonkType [ty1, polyTy2]

  let escaped = filter (`elem` ftyVars) skolTyVars

  unless (null escaped) $
    reportError $
      LessPolymorphic ty1 polyTy2 escaped

-- See subsCheckRho in S. Peyton Jones+: Practical type inference for arbitrary-rank types, JFP 2007
subsumptionCheckBody :: Bool -> PolyTy -> BodyTy -> TC ()
subsumptionCheckBody isRightGiven ty1_ ty2_ = do
  ty1 <- zonkType ty1_
  ty2 <- zonkType ty2_
  case (ty1, ty2) of
    (TyForAll _ _, _) -> do
      bodyTy1 <- instantiate ty1 -- discharge constraint
      subsumptionCheckBody isRightGiven bodyTy1 ty2
    -- A-3: the classes are compared by equality (they are monotypes), the
    -- results covariantly. An instance arrow against an ordinary arrow is
    -- an error (via ensureFunTy below).
    (InstFunTy c1 r1, InstFunTy c2 r2) -> do
      if isRightGiven then tryUnify c1 c2 else tryUnify c2 c1
      subsumptionCheckBody isRightGiven r1 r2
    (FunTy m1 a1 r1, _) -> do
      (a2, m2, r2) <- ensureFunTy ty2
      subsumptionCheckFun isRightGiven a1 m1 r1 a2 m2 r2
    (_, FunTy m2 a2 r2) -> do
      (a1, m1, r1) <- ensureFunTy ty1
      subsumptionCheckFun isRightGiven a1 m1 r1 a2 m2 r2
    _ ->
      if isRightGiven then tryUnify ty1 ty2 else tryUnify ty2 ty1

subsumptionCheckFun :: Bool -> MonoTy -> MultTy -> MonoTy -> MonoTy -> MultTy -> MonoTy -> TC ()
subsumptionCheckFun isRightGiven a1 m1 r1 a2 m2 r2 = do
  -- To use a1 # m1 -> r1 as a2 # m2 -> r1, the following condition must hold
  --  * a2 can be used as a1
  --  * r1 can be used as r2
  --  * m2 is more than m1 (it is safe to use a linear function as an unrestricted one)
  addConstraint [MSub m1 [m2]] -- FIXME: shortcut the case where either one is constant
  subsumptionCheckPoly (not isRightGiven) a2 a1
  subsumptionCheckBody isRightGiven r1 r2

instantiatePatPoly :: PolyTy -> Expected PolyTy -> TC ()
instantiatePatPoly t (Infer ref) = writeTCRef ref t
instantiatePatPoly t (Check t') = subsumptionCheckPoly True t t'

instantiatePoly :: PolyTy -> Expected BodyTy -> TC ()
instantiatePoly t (Infer ref) = do
  t' <- instantiate t -- discharge constraints
  writeTCRef ref t'
instantiatePoly t (Check t') = do
  debugPrint 3 $ text "Checking:" <+> ppr t <+> "is an instance of" <+> ppr t'
  subsumptionCheckBody True t t' -- discharge constraints of t

instantiate :: PolyTy -> TC MonoTy
instantiate t = do
  TyQual cs' t' <- instantiateQ t
  addConstraint cs'
  return t'

instantiateQ :: PolyTy -> TC QualTy
instantiateQ (TyForAll ts qt) = do
  ms <- mapM (const newMetaTy) ts
  let subs = zip ts ms
  -- debugPrint 3 $ "Inst:" <+> align ((ppr $ TyForAll ts qt) <+> text "--->" <> line <> ppr (substTyQ subs qt) )
  return $ substTyQ subs qt
instantiateQ t = return $ TyQual [] t

expectRevTy :: Expected BodyTy -> TC BodyTy
expectRevTy expectedTy = do
  dummy <- newMetaTy
  instantiatePoly (revTy dummy) expectedTy
  pure dummy

ensureRevTy :: BodyTy -> TC BodyTy
ensureRevTy ty = do
  argTy <- newMetaTy
  tryUnify (revTy argTy) ty
  return argTy

ensureFunTy :: BodyTy -> TC (PolyTy, MultTy, BodyTy)
ensureFunTy (FunTy m argTy resTy) = pure (argTy, m, resTy)
ensureFunTy ty = do
  argTy <- newMetaTy
  m <- newMetaTy
  resTy <- newMetaTy
  tryUnify (FunTy m argTy resTy) ty
  return (argTy, m, resTy)

-- | The shape of a type for deciding insertions: zonked, with type synonyms
--   at the top expanded (a signature may hide @{{C}} -> t@ in a synonym).
shapeOf :: Ty -> TC Ty
shapeOf ty = stripSyn <$> (resolveSyn =<< zonkType ty)

-- | A position of the argument patterns aligned with the arrows of a type
--   (C-2): an ordinary argument, an instance argument bound by a written
--   instance pattern, or an instance argument for which a pattern binding
--   the given variable is inserted.
data Slot
  = Explicit PolyTy MultTy
  | Inst Ty
  | Inserted Name Ty

isInstPat :: LPat p -> Bool
isInstPat (Loc _ (PInst _)) = True
isInstPat _ = False

-- | Aligns the argument patterns of a definition or an abstraction with the
--   arrows of its type, one pattern at a time (C-2). Each step consumes at
--   most one pattern; an instance arrow without a written instance pattern
--   gets an inserted one. A trailing instance arrow after the patterns is
--   left to the abstraction insertion of the body (C-1).
--
--   The variable of an inserted pattern is generated here, once per
--   definition, and shared by all its clauses (C-2), as variables written at
--   the same position are (by renaming, they are 'Alpha' names compared by
--   position). Otherwise clauses with invertible patterns could not be
--   grouped into one invertible case by desugaring, which groups clauses
--   whose other patterns are equal.
alignPatsTy :: [LPat 'Renaming] -> BodyTy -> TC ([Slot], BodyTy)
alignPatsTy [] ty = pure ([], ty)
alignPatsTy ps@(p : rest) ty = do
  shape <- shapeOf ty
  case shape of
    InstFunTy c t
      | isInstPat p -> first (Inst c :) <$> alignPatsTy rest t
      | otherwise -> do
          d <- newGenName
          first (Inserted d c :) <$> alignPatsTy ps t
    TyMetaV _ | isInstPat p -> atLoc (location p) $ do
      reportError InstPatNeedsAnnotation
      abortTyping
    _ | isInstPat p -> atLoc (location p) $ do
      reportError NotInstArgPosition
      abortTyping
    _ -> do
      ty' <- zonkType ty
      (argTy, m, resTy) <- ensureFunTy ty'
      first (Explicit argTy m :) <$> alignPatsTy rest resTy

-- | The patterns of a clause (or an abstraction) according to the slots:
--   instance arguments without written patterns get instance patterns
--   binding the variables of the slots (shared by the clauses, C-2).
--   Returns the patterns, their multiplicities and types, and the local
--   instances they bind (B-3).
expandSlots :: [Slot] -> [LPat 'Renaming] -> TC ([LPat 'Renaming], [Multiplication], [PolyTy], [(Name, Ty)])
expandSlots [] [] = pure ([], [], [], [])
expandSlots (Explicit t m : ss) (p : ps) = do
  q <- ty2mult m
  (ps', qs, ts, ls) <- expandSlots ss ps
  pure (p : ps', q : qs, t : ts, ls)
expandSlots (Inst c : ss) (p : ps) = do
  (ps', qs, ts, ls) <- expandSlots ss ps
  pure (p : ps', omega : qs, c : ts, (instPatVar p, c) : ls)
  where
    -- By renaming, the contents is a variable or `_` (which has a name).
    instPatVar (Loc _ (PInst (Loc _ (PVar x)))) = x
    instPatVar (Loc _ (PInst (Loc _ (PWild x)))) = x
    instPatVar _ = cannotHappen $ text "expandSlots: an instance pattern must bind a variable"
expandSlots (Inserted d c : ss) ps = do
  (ps', qs, ts, ls) <- expandSlots ss ps
  pure (noLoc (PInst (noLoc (PVar d))) : ps', omega : qs, c : ts, (d, c) : ls)
expandSlots _ _ = cannotHappen $ text "expandSlots: patterns and slots do not match"

litTy :: Literal -> TC MonoTy
litTy (LitInt _) = return $ TyCon nameTyInt []
litTy (LitChar _) = return $ TyCon nameTyChar []
litTy (LitDouble _) = return $ TyCon nameTyDouble []
litTy (LitRational _) = return $ TyCon nameTyRational []

hasPRev :: LPat 'Renaming -> Bool
hasPRev (Loc _ p) = go p
  where
    go :: Pat 'Renaming -> Bool
    go (PCon _ ps) = any hasPRev ps
    go (PREV _) = True
    go _ = False

checkPatsTyK ::
  [LPat 'Renaming]
  -> [Multiplication]
  -> [Expected PolyTy]
  -> TC a
  -> TC (a, [LPat 'TypeCheck], [(Name, PolyTy, Multiplication)])
checkPatsTyK ps ms ts comp = do
  (req, cs, ps', bind) <- checkPatsTy ps ms ts
  readConstraint >>= \r -> debugPrint 4 $ red $ "CC:" <+> ppr r
  res <-
    withVars [(n, t) | (n, t, _) <- bind] $
      if req
        then do
          -- GADT constructor is used so we need to increase IC-level to check the body.
          (a, ics) <- gatherConstraint $ pushIcLevel comp
          addImpConstraint [] cs ics
          return a
        else do
          comp
  readConstraint >>= \r -> debugPrint 4 $ red $ "CC:" <+> ppr r
  return (res, ps', bind)

checkPatsTy ::
  [LPat 'Renaming]
  -> [Multiplication]
  -> [Expected PolyTy]
  -> TC (Bool, [TyConstraint], [LPat 'TypeCheck], [(Name, PolyTy, Multiplication)])
checkPatsTy [] [] [] = return (False, [], [], [])
checkPatsTy (p : ps) (m : ms) (t : ts) = do
  (req_ps, cs_ps, ps', bind) <- checkPatsTy ps ms ts
  (req_p, cs_p, p', pbind) <- checkPatTy p m t
  return (req_p || req_ps, cs_p ++ cs_ps, p' : ps', pbind ++ bind)
checkPatsTy _ _ _ = error "Cannot happen."

checkPatTy ::
  LPat 'Renaming
  -> Multiplication
  -> Expected PolyTy
  -> TC (Bool, [TyConstraint], LPat 'TypeCheck, [(Name, PolyTy, Multiplication)])
checkPatTy = checkPatTyWork False

checkGADTConstructorInRev :: SrcSpan -> Name -> TC ()
checkGADTConstructorInRev loc c = do
  ConTy _ ys constr args _ <- askConType loc c
  unless (null ys && null constr && all (isMultiplicityOne . snd) args) $
    -- FIXME: is it too conservative? Can we allow constructors that comes with existential quantifications?
    reportError $
      Other $
        hsep ["A GADT-style constructor", hcat [text "'", ppr c, text "'"], "is not allowed in the reversible context."]
  where
    isMultiplicityOne (TyMult One) = True
    isMultiplicityOne _ = False

checkPatTyWork ::
  Bool
  -> LPat 'Renaming
  -> Multiplication
  -> Expected PolyTy
  -> TC (Bool, [TyConstraint], LPat 'TypeCheck, [(Name, PolyTy, Multiplication)])
checkPatTyWork isUnderRev (Loc loc pat) pmult expected = do
  (req, cs, pat', bind) <- atLoc loc $ go pat
  return (req, cs, Loc loc pat', bind)
  where
    go (PVar x)
      | Infer ref <- expected = do
          ty <- newMetaTy
          writeTCRef ref ty
          pure (False, [], PVar (x, ty), [(x, ty, pmult)])
      | Check pTy <- expected =
          return (False, [], PVar (x, pTy), [(x, pTy, pmult)])
    go (PCon c ps) = do
      ConTy xs ys q_ args_ ret_ <- askConType loc c

      -- Reject GADT-style constructors in rev.
      when isUnderRev $ checkGADTConstructorInRev loc c

      uvars <- mapM (const newMetaTyVar) xs
      evars <- mapM newSkolemTyVar ys

      let tbl = zip xs (map TyMetaV uvars) ++ zip ys (map TyVar evars)
      let q = map (substTyC tbl) q_
          args = map (\(t, m) -> (substTy tbl t, substTy tbl m)) args_
          ret = substTy tbl ret_

      unless (length ps == length args) $ do
        reportError $
          Other $
            hsep
              [ "Constructor"
              , ppr c
              , "takes"
              , ppr (length args)
              , "arguments"
              , "but here passed is"
              , ppr (length ps)
              ]
        abortTyping

      instantiatePatPoly ret expected

      (req, cs, ps', bind) <-
        foldr (\(reqj, csj, pj', bindj) (req, cs, ps', bind) -> (reqj || req, csj ++ cs, pj' : ps', bindj ++ bind)) (False, [], [], [])
          <$> zipWithM
            ( \pj (tj, mj) -> do
                m <- ty2mult mj
                checkPatTyWork isUnderRev pj (lub m pmult) (Check tj)
            )
            ps
            args

      let tyOfC = foldr (\(t, m) r -> TyCon nameTyArr [m, t, r]) ret args
      return (not (null q) || not (null ys) || req, q ++ cs, PCon (c, tyOfC) ps', bind)
    go (PREV p) = do
      when isUnderRev $
        atLoc (location p) $
          reportError $
            Other $
              text "rev patterns cannot be nested."

      ty <- newMetaTy
      instantiatePatPoly (revTy ty) expected
      (req, cs, p', bind) <- checkPatTyWork True p pmult (Check ty)
      let bind' = map (\(x, t, m) -> (x, revTy t, m)) bind

      forM_ bind' $ \(x, _, m) ->
        -- TODO: Add good error messages.
        --- addConstraint $ msubMult m one
        whenChecking (CheckingMultiplicities x MCLinearity (m2ty m) [one]) $ constrainLessThan m one

      return (req, cs, PREV p', bind')
    go (PWild x) = do
      -- this is only possible when pmult is omega
      -- tryUnify pmult (TyMult Omega)
      (req, cs, Loc _ (PVar x'), _bind) <- checkPatTyWork isUnderRev (noLoc $ PVar x) omega expected
      -- cs must be []
      addConstraint $ msubMult omega pmult
      return (req, cs, PWild x', [])
    -- C-3: an instance pattern is checked only at an instance slot of the
    -- alignment (C-2), against its class type; by renaming its contents is
    -- a variable or `_` (which has a name). It binds the variable (with the
    -- multiplicity given by the caller, Omega).
    go (PInst (Loc l p))
      | Check c <- expected =
          let x = case p of
                PVar y -> y
                PWild y -> y
                _ -> cannotHappen $ text "checkPatTyWork: an instance pattern must bind a variable"
          in  pure (False, [], PInst (Loc l (PVar (x, c))), [(x, c, pmult)])
      | otherwise = cannotHappen $ text "checkPatTyWork: an instance pattern in Infer mode"

constrainLessThan :: Multiplication -> Multiplication -> TC ()
constrainLessThan m1 (m2ty -> []) =
  forM_ (m2ty m1) $ \q -> unify q (TyMult One)
constrainLessThan (m2ty -> [TyMult Omega]) m2 =
  forM_ (m2ty m2) $ \q -> unify (TyMult Omega) q
constrainLessThan m1 m2 = addConstraint (msubMult m1 m2)

locPS :: [LPat 'Renaming] -> Maybe SrcSpan
locPS [] = Nothing
locPS ps = Just $ mconcat $ map location ps

atLocMaybe :: Maybe SrcSpan -> TC a -> TC a
atLocMaybe Nothing = id
atLocMaybe (Just x) = atLoc x

constrainVars :: [(Name, Multiplication)] -> UseMap -> TC ()
constrainVars [] _ = return ()
constrainVars ((x, q) : xqs) m = do
  -- let dx = hsep [ text "linearity of", dquotes (ppr x) <> text ", but it is used more than once" ]
  case lookupUseMap x m of
    Just mul -> do
      constrainVars xqs m
      -- addConstraint $ msubMult mul q
      whenChecking (CheckingMultiplicities x MCUnknown (m2ty mul) (m2ty q)) $ constrainLessThan mul q
    Nothing -> do
      -- whenChecking (OtherContext dx) $ unify q (TyMult Omega)
      constrainVars xqs m
      -- addConstraint $ msubMult omega q
      whenChecking (CheckingMultiplicities x MCUnrestrictedness [omega] (m2ty q)) $ constrainLessThan omega q

-- TODO: sig-expression is buggy.

-- | Infers the type of an expression; trailing instance arguments of its
--   value are not inserted (as Agda's inferExpr, DontExpandLast).
inferTy :: LExp 'Renaming -> TC (LExp 'TypeCheck, BodyTy, UseMap)
inferTy = withExpandLast DontExpandLast . inferTyWork

-- | Infers the type of an expression whose value is matched against
--   patterns (the bound expression of @let p <- e1 in e2@ and the scrutinee
--   of @case@), inserting trailing instance arguments (as Agda's
--   inferExpr' ExpandLast for pattern lets).
inferTyExpandM :: LExp 'Renaming -> Multiplication -> TC (LExp 'TypeCheck, BodyTy, UseMap)
inferTyExpandM lexp m = do
  (lexp', ty, umap) <- withExpandLast ExpandLast $ inferTyWork lexp
  pure (lexp', ty, raiseUse m umap)

-- | Inference under the current expand-last flag (set by the callers).
inferTyWork :: LExp 'Renaming -> TC (LExp 'TypeCheck, BodyTy, UseMap)
inferTyWork (Loc loc expr) = go expr
  where
    -- go (Sig e tySyn) = do
    --   let sigTy = ty2ty tySyn
    --   (e', polyTy, umap, cs) <- inferPolyTy e
    --   tryCheckMoreGeneral loc polyTy sigTy
    --   (cs', ty') <- instantiate sigTy
    --   -- (e', umap, cs) <- checkTy e ty'
    --   return (e', ty', umap, cs'++cs)
    go e = do
      ref <- newTCRef (error "inferTy: empty result")
      (e', umap) <- checkTy (Loc loc e) (Infer ref)
      ty <- readTCRef ref
      return (e', ty, umap)

-- | Splits an application into its head and its arguments (D-1).
--   Parentheses around the head are crossed (D-6).
flattenSpine :: LExp 'Renaming -> (LExp 'Renaming, [Arg 'Renaming])
flattenSpine = go []
  where
    go as (Loc _ (App f a)) = go (a : as) f
    go as@(_ : _) (Loc _ (Parens e)) = go as e
    go as e = (e, as)

-- | Checks an application as a spine (D-1): the head's type is used as is
--   for a variable and inferred otherwise; the arguments are processed from
--   the left, instantiating @forall@s on the way; finally the rest of the
--   type is compared with the expected type.
--
--   The applications are rebuilt with locations recomputed from their parts
--   (the head's parentheses are dropped, D-6), and the partial applications
--   give the error contexts of the arguments.
--
--   An instance arrow takes a written instance argument @{{e}}@, or else an
--   application to a hole for a new goal is inserted (D-1); after the
--   arguments, trailing instance arrows get insertions when the expand-last
--   flag is set (D-2).
checkSpine :: LExp 'Renaming -> [Arg 'Renaming] -> Expected BodyTy -> TC (Exp 'TypeCheck, UseMap)
checkSpine hd args expectedTy = do
  (hd', hdTy, hdUmap) <- case hd of
    Loc l (Var x) -> do
      tyOfX <- askType l x
      pure (Loc l (Var (x, tyOfX)), tyOfX, singletonUseMap x)
    _ -> inferTy hd
  (res, resTy, argsUmap) <- goArgs hd hd' hdTy args
  expand <- asks tcExpandLast
  (res', resTy') <- case expand of
    ExpandLast -> insertTrailing res resTy
    DontExpandLast -> pure (res, resTy)
  instantiatePoly resTy' expectedTy
  pure (unLoc res', mergeUseMap hdUmap argsUmap)
  where
    -- f: the partial application so far (for error contexts); f': its typed version
    goArgs ::
      LExp 'Renaming
      -> LExp 'TypeCheck
      -> PolyTy
      -> [Arg 'Renaming]
      -> TC (LExp 'TypeCheck, PolyTy, UseMap)
    goArgs _ f' ty [] = pure (f', ty, M.empty)
    goArgs f f' ty (a : as) = do
      shape <- shapeOf ty
      case (shape, a) of
        (TyForAll _ _, _) -> do
          ty' <- instantiate shape
          goArgs f f' ty' (a : as)
        (InstFunTy c t, InstArg e) -> do
          -- an explicitly passed instance (instance arrows are Omega)
          (e', umapE) <- checkTyM e (Check c) omega
          let l = location f <> location e
          (res, rTy, umapR) <-
            goArgs (Loc l (App f a)) (Loc l (App f' (InstArg e'))) t as
          pure (res, rTy, mergeUseMap umapE umapR)
        (InstFunTy c t, ExplicitArg _) -> do
          -- insertion; the argument is not consumed
          hole <- atExp f $ atLoc (location f) $ newGoal c
          goArgs f (Loc (location f) (App f' (InstArg hole))) t (a : as)
        (TyMetaV _, InstArg e) -> atExp f $ atLoc (location e) $ do
          reportError InstArgUnknownFun
          abortTyping
        (_, InstArg e) -> atExp f $ atLoc (location e) $ do
          reportError NotInstArgPosition
          abortTyping
        (_, ExplicitArg e) -> do
          ty' <- zonkType ty
          (argTy, m, resTy) <- atExp f $ atLoc (location f) $ ensureFunTy ty'
          mul <- ty2mult m
          (e', umapE) <- checkPolyTyM e argTy mul
          let l = location f <> location e
          (res, rTy, umapR) <-
            goArgs (Loc l (App f a)) (Loc l (App f' (ExplicitArg e'))) resTy as
          pure (res, rTy, mergeUseMap umapE umapR)

    -- D-2: leading foralls and instance arrows of the rest are instantiated
    -- / get insertions until neither remains. The type is returned as is if
    -- nothing is done (keeping synonyms for messages).
    insertTrailing :: LExp 'TypeCheck -> PolyTy -> TC (LExp 'TypeCheck, PolyTy)
    insertTrailing f' ty = do
      shape <- shapeOf ty
      case shape of
        TyForAll _ _ -> do
          ty' <- instantiate shape
          insertTrailing f' ty'
        InstFunTy c t -> do
          hole <- atLoc (location f') $ newGoal c
          insertTrailing (Loc (location f') (App f' (InstArg hole))) t
        _ -> pure (f', ty)

-- | Makes a goal for an instance argument of class type @c@ (E-1) in the
--   current scope (local instances, level, location, error context) and
--   returns the hole for its dictionary (F-3).
newGoal :: Ty -> TC (LExp 'TypeCheck)
newGoal c = do
  g <- newGenName
  ref <- liftIO $ newIORef Nothing
  locals <- asks tcLocalInsts
  lv <- askCurrentTcLevel
  l <- asks tcLoc
  ctx <- currentTypeErrorContext
  addGoals
    [ Goal
        { goalId = g
        , goalRef = ref
        , goalTy = c
        , goalLocals = locals
        , goalLevel = lv
        , goalLoc = l
        , goalCtx = ctx
        }
    ]
  pure $ Loc (fromMaybe NoLoc l) (InstHole () (g, c) ref)

checkTyM :: LExp 'Renaming -> Expected BodyTy -> Multiplication -> TC (LExp 'TypeCheck, UseMap)
checkTyM lexp ty m = do
  (lexp', umap) <- checkTy lexp ty
  return (lexp', raiseUse m umap)

-- | In Check mode, the expand-last flag is set (as Agda's doExpandLast in
--   checkExpr); in Infer mode, the flag set by the caller is used.
checkTy :: LExp 'Renaming -> Expected BodyTy -> TC (LExp 'TypeCheck, UseMap)
checkTy lexp@(Loc loc expr) expectedTy = do
  -- C-1: when an instance argument is expected, an abstraction binding it
  -- (a local instance, B-3) is inserted and the same expression is checked
  -- against the rest of the type (recursively, for several instance
  -- arguments). Not for an abstraction binding it explicitly, parentheses
  -- (the expected type is passed inside) and annotations (the annotation
  -- gives the type).
  inserted <- case expectedTy of
    Check t | not (bindsItself expr) -> do
      shape <- shapeOf t
      pure $ case shape of
        InstFunTy c t' -> Just (c, t')
        _ -> Nothing
    _ -> pure Nothing
  case inserted of
    Just (c, t') -> atLoc loc $ do
      d <- newGenName
      (e', umap) <- withVars [(d, c)] $ withLocalInsts [(d, c)] $ checkTy lexp (Check t')
      pure (Loc loc (Abs [Loc loc (PInst (Loc loc (PVar (d, c))))] e'), M.delete d umap)
    Nothing ->
      fmap (first $ Loc loc) $ atLoc loc $ atExp lexp $ setFlag $ go expr
  where
    bindsItself (Abs (p : _) _) = isInstPat p
    bindsItself (Parens _) = True
    bindsItself (Sig _ _) = True
    bindsItself _ = False

    setFlag = case expectedTy of
      Check _ -> withExpandLast ExpandLast
      Infer _ -> id

    -- first3 f (a,b,c) = (f a, b, c)

    go :: Exp 'Renaming -> TC (Exp 'TypeCheck, UseMap)
    go (WTup es) = do
      let n = length es
      tys <- mapM (const newMetaTy) [1 .. n]
      instantiatePoly (TyCon (nameTyWTuple n) tys) expectedTy
      (es', ms) <- unzip <$> zipWithM checkTy es (map Check tys)
      let m = if null ms then M.empty else foldr1 multiplyUseMap ms
      pure (WTup es', m)
    go (WProj i n) = do
      -- it has type &(a_1,...,a_n) # p -> a_i
      tys <- mapM (const newMetaTy) [1 .. n]
      let ti = tys !! i
      let wTupleTy = TyCon (nameTyWTuple n) tys

      instantiatePoly (FunTy (TyMult One) wTupleTy ti) expectedTy
      pure (WProj i n, emptyUseMap)
    -- A variable is a spine without arguments (D-1 7).
    go (Var x) = checkSpine (Loc loc (Var x)) [] expectedTy
    go (Lit l) = do
      ty <- litTy l
      instantiatePoly ty expectedTy
      return (Lit l, M.empty)
    go (Abs pats e) | Check eTy <- expectedTy = do
      (slots, resTy) <- alignPatsTy pats eTy
      (pats1, qs, ts, locals) <- expandSlots slots pats

      ((e', umap), pats', bind) <- checkPatsTyK pats1 qs (map Check ts) $ withLocalInsts locals $ do
        when (any hasPRev pats) $ void $ ensureRevTy resTy
        checkTy e (Check resTy)

      let xqs = map (\(x, _, q) -> (x, q)) bind
      atLocMaybe (locPS pats) $ constrainVars xqs umap

      pure (Abs pats' e', foldr (M.delete . fst) umap xqs)
    go (Abs pats e) | Infer ref <- expectedTy = do
      -- An instance pattern needs a known type (C-4).
      forM_ (filter isInstPat pats) $ \p -> atLoc (location p) $ do
        reportError InstPatNeedsAnnotation
        abortTyping
      -- multiplicity of arguments
      ts <- mapM (const newMetaTy) pats
      qs <- mapM (const newMetaTy) pats
      qs' <- mapM ty2mult qs

      ((e', retTy, umap), pats', bind) <- checkPatsTyK pats qs' (map Check ts) $ do
        res@(_, retTy, _) <- inferTy e
        when (any hasPRev pats) $ void $ ensureRevTy retTy
        pure res

      let xqs = map (\(x, _, q) -> (x, q)) bind

      atLocMaybe (locPS pats) $ constrainVars xqs umap
      writeTCRef ref (foldr (uncurry tyarr) retTy $ zip qs ts)

      return (Abs pats' e', foldr (M.delete . fst) umap xqs)
    go e@(App _ _) =
      let (hd, args) = flattenSpine (Loc loc e)
      in  checkSpine hd args expectedTy
    go (InstHole v _ _) = absurd v
    go (Let1 p e1 e2) = do
      patMult <- ty2mult =<< newMetaTy
      (e1', ty1, umap1) <- inferTyExpandM e1 patMult

      ((e2', umap2), [p'], bind) <- checkPatsTyK [p] [patMult] [Check ty1] $ do
        when (hasPRev p) $ do
          -- When p contains rev, we ensure that expectedTy must the form of rev _
          dummy <- newMetaTy
          instantiatePoly (revTy dummy) expectedTy
        checkTy e2 expectedTy

      let xqs = map (\(x, _, q) -> (x, q)) bind

      atLoc (location p) $ constrainVars xqs umap2
      let umap2' = foldr (M.delete . fst) umap2 xqs

      return (Let1 p' e1' e2', mergeUseMap umap1 umap2')
    go (Con c) = do
      tyOfC <- askType loc c
      instantiatePoly tyOfC expectedTy
      return (Con (c, tyOfC), M.empty)
    go (Sig e ty_) = do
      let annTy = ty2ty ty_
      checkClassTypesL ty_ -- G-4
      (e', umap) <- checkPolyTy e annTy
      instantiatePoly annTy expectedTy
      pure (unLoc e', umap)
    go Lift = do
      tyA <- newMetaTy
      tyB <- newMetaTy
      instantiatePoly (liftTy tyA tyB) expectedTy
      return (Lift, M.empty)
      where
        liftTy tyA tyB =
          (tyA *-> tyB) *-> (tyB *-> tyA) *-> (revTy tyA -@ revTy tyB)
    go Unlift = do
      tyA <- newMetaTy
      tyB <- newMetaTy
      instantiatePoly (unliftTy tyA tyB) expectedTy
      return (Unlift, M.empty)
      where
        unliftTy tyA tyB =
          (revTy tyA -@ revTy tyB) *-> tupleTy [tyA *-> tyB, tyB *-> tyA]
    go RPin = do
      tyA <- newMetaTy
      tyB <- newMetaTy
      instantiatePoly (pinTy tyA tyB) expectedTy
      return (RPin, M.empty)
      where
        pinTy tyA tyB =
          revTy tyA *-@ (tyA *-> revTy tyB) *-@ revTy (tupleTy [tyA, tyB])
    go (Parens e) = do
      (e', umap) <- checkTy e expectedTy
      return (Parens e', umap)
    -- An operator application is checked as a spine and output as
    -- applications (D-3); `Op` cannot appear after type checking
    -- (XOp 'TypeCheck = Void).
    go (Op () op e1 e2) =
      checkSpine (Loc loc (Var op)) [ExplicitArg e1, ExplicitArg e2] expectedTy
    go (RCon c) = do
      tyOfC_ <- askType loc c

      -- Reject GADT-style constructors
      checkGADTConstructorInRev loc c

      let tyOfC = addRev tyOfC_
      instantiatePoly tyOfC expectedTy
      return (RCon (c, tyOfC), M.empty)
      where
        addRev (TyForAll xs (TyQual cs t)) = TyForAll xs (TyQual cs $ addRev t)
        -- FIXME: m must be one
        addRev (TyCon t [m, t1, t2]) | t == nameTyArr = TyCon t [m, revTy t1, addRev t2]
        addRev t = revTy t
    go (Let decls e) = do
      (decls', bind, umapLet) <- inferDecls False decls
      (e', umap) <- withVars bind $ checkTy e expectedTy
      return (Let decls' e', mergeUseMap umap umapLet)
    go (Case e0 alts) = do
      p <- newMetaTyVar -- multiplicity of e0
      mul <- ty2mult (TyMetaV p)

      (e0', tyPat, umap0) <- inferTyExpandM e0 mul
      (alts', umapA) <- checkAltsTy alts tyPat mul expectedTy

      return (Case e0' alts', mergeUseMap umap0 umapA)

    -- NB: This constructor will be removed in near future.
    go (RDO as0 er) = do
      (as0', bind, umap) <- goAs as0
      let bind' = map (\(x, t, _) -> (x, revTy t)) bind
      let xs = map (\(x, _) -> x) bind'
      let xqs = [(x, one) | x <- xs]

      (er', umapr) <- withVars bind' $ checkTy er expectedTy
      constrainVars xqs umapr

      return (RDO as0' er', mergeUseMap umap (foldr M.delete umapr xs))
      where
        goAs [] = return ([], [], M.empty)
        goAs ((p, e) : as) = do
          tyE <- newMetaTy
          (e', umapE) <- checkTy e (Check $ revTy tyE)

          -- (p', bind)  <- checkPatTy p omega tyE

          -- let xqs = map (\(x,_,q) -> (x,q)) bind

          -- (as', bindAs, umapAs) <- withVars [ (n,t) | (n,t,_) <- bind ] $ goAs as

          ((as', bindAs, umapAs), [p'], bind) <- checkPatsTyK [p] [omega] [Check tyE] $ do
            goAs as
          let xqs = map (\(x, _, q) -> (x, q)) bind

          atLoc (location p) $ constrainVars xqs umapAs

          return
            ( (p', e') : as'
            , bindAs ++ bind
            , mergeUseMap (foldr (M.delete . fst) umapAs xqs) umapE
            )

checkGeneralizeTy :: SrcSpan -> Bool -> MonoTy -> UseMap -> PolyTy -> TC ()
checkGeneralizeTy loc isTopLevel ty um polyTy2
  | not isTopLevel
  , Just monoTy2 <- testMonoTy polyTy2 =
      atLoc loc $ unify ty monoTy2
  | otherwise =
      checkPolymorphicEnough loc ty um polyTy2

checkPolyTyM :: LExp 'Renaming -> PolyTy -> Multiplication -> TC (LExp 'TypeCheck, UseMap)
checkPolyTyM lexp ty m = do
  (lexp', umap) <- checkPolyTy lexp ty
  return (lexp', raiseUse m umap)

checkPolyTy :: LExp 'Renaming -> PolyTy -> TC (LExp 'TypeCheck, UseMap)
checkPolyTy lexp ty = do
  (skolemTyVars, TyQual given bodyTy) <- skolemize ty

  ((res, umap), csExp) <- gatherConstraint $ pushLevel $ checkTy lexp (Check bodyTy)

  currentTcLevel <- askCurrentTcLevel
  invisibleMetaVars <-
    filterM
      ( \m -> do
          lv <- readTcLevelMv m
          return $ lv > currentTcLevel
      )
      (nub $ metaTyVars csExp)

  -- FIXME: is the following really ok?
  if null given
    then do csOrig <- readConstraint; setConstraint (csExp ++ csOrig)
    else addImpConstraint invisibleMetaVars given csExp

  umapVars <- freeTyVars <$> mapM zonkType [t | m <- M.elems umap, t <- m2ty m]
  tyVars <- freeTyVars <$> zonkType ty

  let escaped = filter (`elem` (tyVars ++ umapVars)) skolemTyVars

  unless (null escaped) $
    reportError $
      CannotHavePolyTy ty escaped

  pure (res, umap)

checkPolymorphicEnough :: SrcSpan -> MonoTy -> UseMap -> PolyTy -> TC ()
checkPolymorphicEnough loc ty1_ um polyTy2 = atLoc loc $ do
  debugPrint 4 $ "PolyTy" <+> text (show polyTy2)
  ty1 <- zonkType ty1_
  cs <- mapM zonkTypeIC =<< readConstraint
  setConstraint []

  currentTcLevel <- askCurrentTcLevel
  umapVars <- metaTyVars <$> mapM zonkType [t | m <- M.elems um, t <- m2ty m]

  generalizable <-
    filterM
      ( \m -> do
          lv <- readTcLevelMv m
          return $ lv > currentTcLevel
      )
      ((nub $ metaTyVars ty1 ++ metaTyVars cs) \\ umapVars)

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
    reportError $ ImplicationCheckFail invisible given q

tryGeneralizeTy :: Bool -> MonoTy -> UseMap -> TC PolyTy
tryGeneralizeTy isTopLevel ty_ u = do
  if isTopLevel
    then generalizeTy ty_ u
    else do
      ty <- zonkType ty_
      debugPrint 3 $ "Generalization of" <+> ppr ty <+> "is suppressed."
      return ty

-- NB: @generalizeTy@ makes the current constraint empty
generalizeTy :: MonoTy -> UseMap -> TC PolyTy
generalizeTy ty_ um = do
  cs <- readConstraint
  setConstraint []

  q <- solveInferredConstraint False [] [] cs

  ty <- zonkType ty_

  currentTcLevel <- askCurrentTcLevel
  umapVars <- metaTyVars <$> mapM zonkType [t | m <- M.elems um, t <- m2ty m]

  let qty = TyQual q ty

  generalizable <-
    filterM
      ( \m -> do
          lv <- readTcLevelMv m
          return $ lv > currentTcLevel
      )
      (metaTyVars qty \\ umapVars)

  -- Generalization captures all the constraints
  let qty' = TyQual q ty

  polyTy <- quantify generalizable qty'
  debugPrint 2 $
    text "Gen"
      <> brackets (text $ show currentTcLevel)
      <> text ":"
        <+> align
          ( vsep
              [ text "Generalizable" <+> ppr generalizable
              , group (align (group (ppr qty) <> line <> text "-->" <> line <> group (ppr polyTy)))
              ]
          )

  setConstraint []

  return polyTy

-- where
--   refersTo :: TyConstraint -> [MetaTyVar] -> Bool
--   refersTo (MSub m ms)  vs = any (`elem` vs) $ metaTyVars (m:ms)
--   refersTo (TyEq t1 t2) vs = any (`elem` vs) $ metaTyVars [t1,t2]

inferPolyTy :: Bool -> LExp 'Renaming -> TC (LExp 'TypeCheck, PolyTy, UseMap)
inferPolyTy isMultipleUse expr = do
  ((expr', ty, umap), goals) <- gatherGoals $ pushLevel $ inferTy expr

  -- H-2: goals are solved before generalization, as for a top-level
  -- definition without a signature (E-2).
  solveGoals (ReportAtTopLevel False) goals

  -- (umapM, csM) <- if isMultipleUse then raiseUse (TyMult Omega) umap
  --                 else return (umap, [])
  let umapM = if isMultipleUse then raiseUse omega umap else umap

  polyTy <- generalizeTy ty umapM

  return (expr', polyTy, umapM)

inferExp :: LExp 'Renaming -> TC (LExp 'TypeCheck, PolyTy)
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
  reportLeftoverGoals
  return (expr', polyTy)

checkAltsTy ::
  [(LPat 'Renaming, Clause 'Renaming)]
  -> BodyTy
  -> Multiplication
  -> Expected BodyTy
  -> TC ([(LPat 'TypeCheck, Clause 'TypeCheck)], UseMap)
checkAltsTy alts patTy q bodyTy =
  -- parallel $ map checkAltTy alts
  gatherAltUC =<< mapM checkAltTy alts
  where
    checkAltTy (pat, c) = do
      -- (pat', bind) <- checkPatTy pat q patTy
      -- (c', umap)   <- withVars [ (n,t) | (n,t,_) <- bind ] $ checkClauseTy c bodyTy

      ((c', umap), [pat'], bind) <- checkPatsTyK [pat] [q] [Check patTy] $ do
        when (hasPRev pat) $ do
          dummy <- newMetaTy
          instantiatePoly (revTy dummy) bodyTy
        checkClauseTy c bodyTy

      let xqs = map (\(x, _, qq) -> (x, qq)) bind
      atLoc (location pat) $ constrainVars xqs umap
      return ((pat', c'), foldr (M.delete . fst) umap xqs)

-- checkAltTy (p, c) = do
--   (p', ubind, lbind) <- checkPatTy p patTy
--   c' <- withUVars ubind $ withLVars lbind $ checkClauseTy c bodyTy
--   return (p', c')

gatherAltUC ::
  [(a, UseMap)]
  -> TC ([a], UseMap)
gatherAltUC [] = return ([], M.empty)
gatherAltUC ((obj, umap) : triples) = go obj umap triples
  where
    go s um [] = return ([s], um)
    go s um ((s', um') : ts) = do
      (ss, umR) <- go s' um' ts
      -- (um2, cs2) <- maxUseMap um umR
      let um2 = multiplyUseMap um umR
      return (s : ss, um2)

inferDecls ::
  Bool -- is top level
  -> Decls 'Renaming (LDecl 'Renaming)
  -> TC (Decls 'TypeCheck (LDecl 'TypeCheck), [(Name, PolyTy)], UseMap)
inferDecls _ (Decls v _) = absurd v
inferDecls isTopLevel (HDecls _ dss) = do
  (dss', bind, umap) <- go [] dss
  return (HDecls () dss', bind, umap)
  where
    go bs [] = return ([], bs, M.empty)
    go bs (ds : rest) = do
      (ds', bind, umap) <- inferMutual isTopLevel ds
      (rest', bs', umap') <- withVars bind $ go (bind ++ bs) rest
      return (ds' : rest', bs', mergeUseMap umap umap')

-- | Checks the class types in a user-written type (G-4): the contents of
--   @{{ }}@ must be a class applied to arguments (Q2), and every class must
--   be applied to as many arguments as it has parameters, inside or outside
--   @{{ }}@ (classes are ordinary types, Q1, but there is no kind for
--   unapplied classes, I1). Synonyms are expanded first, so this is done
--   where a type is used, not at synonym definitions. Errors are reported
--   and checking continues.
checkClassTypes :: Ty -> TC ()
checkClassTypes ty = resolveSyn ty >>= go
  where
    go (TySyn _ t) = go t
    go (TyForAll _ (TyQual _ t)) = go t
    go (InstFunTy c t) = do
      checkClassApp c
      go c
      go t
    go (TyCon n ts) = do
      cenv <- asks tcClassEnv
      case M.lookup n cenv of
        Just ci
          | length (ciParams ci) /= length ts ->
              reportError $ ClassArityMismatch n (length (ciParams ci)) (length ts)
        _ -> pure ()
      mapM_ go ts
    go _ = pure ()

-- | 'checkClassTypes' for a written type, located at it.
checkClassTypesL :: LTy 'Renaming -> TC ()
checkClassTypesL lty = atLoc (location lty) $ checkClassTypes (ty2ty lty)

-- | Checks that a type is an application of a class (where a class is
--   required: inside @{{ }}@, superclasses, instance heads). The number of
--   arguments is checked by 'checkClassTypes'.
checkClassApp :: Ty -> TC ()
checkClassApp ty = do
  ty' <- stripSyn <$> resolveSyn ty
  cenv <- asks tcClassEnv
  case ty' of
    TyCon n _ | M.member n cenv -> pure ()
    _ -> reportError $ NotAClass ty

stripSyn :: Ty -> Ty
stripSyn (TySyn _ t) = stripSyn t
stripSyn t = t

inferTopDecls ::
  Decls 'Renaming (LDecl 'Renaming)
  -> [Loc (Name, [Name], [Loc (CDecl 'Renaming)])]
  -> [Loc (Name, [Name], LTy 'Renaming)]
  -> [Loc (Name, [Name], [LTy 'Renaming], [Loc (Name, LTy 'Renaming)], [LDecl 'Renaming])] -- classes
  -> [Loc (Name, LTy 'Renaming, [LDecl 'Renaming])] -- instances
  -> TC
      ( Decls 'TypeCheck (LDecl 'TypeCheck)
      , [(Name, PolyTy)]
      , [C.DDecl Name]
      , [C.TDecl Name]
      , CTypeTable
      , SynTable
      , ClassTable -- classes declared in this module
      , InstTable -- instances declared in this module
      , [TypedDefault] -- default methods of the classes declared in this module (G-5 2)
      , [TypedInstance] -- instances declared in this module (G-3 3, G-5 3, 4)
      )
inferTopDecls decls dataDecls typeDecls classDecls instDecls = do
  let dataDecls' =
        [ C.DDecl n (map BoundTv ns) [convConDecl cd | Loc _ cd <- cdecls]
        | Loc _ (n, ns, cdecls) <- dataDecls
        ]

  let typeDecls' = [C.TDecl n (map BoundTv ns) (ty2ty lty) | Loc _ (n, ns, lty) <- typeDecls]

  let synTable = M.fromList $
        flip map typeDecls $ \(Loc _ (n, ns, lty)) ->
          let ty = ty2ty lty
          in  (n, (map BoundTv ns, ty))

  let ctypeTable = M.fromList $ concat [mkConTable (n, ns, cdecls) | Loc _ (n, ns, cdecls) <- dataDecls]
  -- [ (n, foldr ((-@) . const typeKi) typeKi ns) | Loc _ (n, ns, _) <- dataDecls ]
  -- ++
  -- [ (cn, TyForAll tvs $ TyQual [] (foldr ((-@) . ty2ty) (TyCon n $ map TyVar tvs) tys)) |
  --   Loc _ (n, ns, cdecls) <- dataDecls,
  --   let tvs = map BoundTv ns,
  --   Loc _ (CDecl cn tys) <- cdecls ]

  -- The order of registration and checks follows G-1 in the notes: type
  -- information first (data types and synonyms, classes, instances), then
  -- expressions.

  -- G-1 stage 1: data types and type synonyms.
  withCons (M.toList ctypeTable) $
    withSyns (M.toList synTable) $ do
      -- G-1 stage 2: classes (G-2).
      let classTable = M.fromList [(c, mkClassInfo ps sups sigs defs) | Loc _ (c, ps, sups, sigs, defs) <- classDecls]
      withClassesAndInstances classTable M.empty $ do
        -- G-4: fields of data constructors (they may contain class types,
        -- so this is done once the class table exists).
        forM_ dataDecls $ \(Loc _ (_, _, cdecls)) ->
          forM_ cdecls $ \(Loc _ cd) -> mapM_ checkClassTypesL (fieldTys cd)

        -- G-2 2 and 4: superclasses and method signatures. Cycles in the
        -- superclass hierarchy are allowed (G-2 3).
        forM_ classDecls $ \(Loc _ (_, _, sups, sigs, _)) -> do
          forM_ sups $ \s -> atLoc (location s) $ do
            checkClassTypes (ty2ty s)
            checkClassApp (ty2ty s)
          forM_ sigs $ \(Loc _ (_, t)) -> checkClassTypesL t

        let methodTys =
              [ (m, methodType c (map BoundTv ps) (ty2ty t))
              | Loc _ (c, ps, _, sigs, _) <- classDecls
              , Loc _ (m, t) <- sigs
              ]

        -- G-1 stage 3-a: instances (G-3 1, 4); registered even when a
        -- check fails, to avoid cascades of errors at their uses.
        instTys <- forM instDecls $ \(Loc _ (x, lty, _)) -> do
          let ty = ty2ty lty
          atLoc (location lty) $ do
            checkClassTypes ty
            checkClassApp =<< instHead ty
          pure (x, ty)
        instTable <-
          M.fromListWith M.union
            <$> sequence
              [ do
                  hd <- instHead ty
                  pure (headName hd, M.singleton x ty)
              | (x, ty) <- instTys
              ]

        withClassesAndInstances M.empty instTable $
          withVars (methodTys ++ instTys) $ do
            -- G-1 stage 3-b: the superclass instances of each instance are
            -- solvable (G-3 3), once all instances are registered.
            superDicts <- forM (zip instDecls instTys) $ \(Loc l (x, _, _), (_, ty)) ->
              atLoc l $ whenChecking (CheckingSuperclasses x) $ checkSuperInstances ty

            -- G-1 stage 4: definitions.
            (decls', nts, _) <- inferDecls True decls

            -- G-1 stage 5: default methods and instance bodies (G-5), with
            -- the types of the definitions visible (a body may use a
            -- definition without a signature). Errors are accumulated per
            -- body (G-5 5).
            (typedDefaults, typedInsts) <- withVars nts $ do
              typedDefaults <- fmap concat $
                forM classDecls $ \(Loc _ (c, _, _, _, defs)) ->
                  forM [(l, m, pcs) | Loc l (DDef m pcs) <- defs] $ \(l, m, pcs) -> do
                    -- renaming ensures that m is a method of c
                    let polyTy = fromMaybe (cannotHappen $ text "No method type for" <+> ppr m) (lookup m methodTys)
                    pcs' <- checkSigDef l m polyTy pcs
                    pure $ TypedDefault{tdMethod = m, tdClass = c, tdType = polyTy, tdClauses = pcs'}

              typedInsts <- forM (zip3 instDecls instTys superDicts) $
                \(Loc l (x, _, ids), (_, ty), (locals, sups)) -> do
                  (ms, defaulted) <- checkInstBodies l x ty ids
                  c <- headName <$> instHead ty
                  pure $
                    TypedInstance
                      { tiName = x
                      , tiType = ty
                      , tiClass = c
                      , tiLocals = locals
                      , tiSupers = sups
                      , tiMethods = ms
                      , tiDefaulted = defaulted
                      }
              pure (typedDefaults, typedInsts)

            reportLeftoverGoals
            return
              ( decls'
              , -- H-4-5 2: also the values made by desugaring (projections,
                -- defaults); dictionary constructors are not values
                nts
                  ++ methodTys
                  ++ instTys
                  ++ [ (superProjName c i, superProjType c ci i)
                     | (c, ci) <- M.toList classTable
                     , i <- [0 .. length (ciSupers ci) - 1]
                     ]
                  ++ [(defaultName (tdMethod td), tdType td) | td <- typedDefaults]
              , dataDecls'
              , typeDecls'
              , ctypeTable
              , synTable
              , classTable
              , instTable
              , typedDefaults
              , typedInsts
              )
  where
    -- G-5 3, 4: the bodies of instance x of type ty. Skipped when the head
    -- is not a class (reported at registration).
    checkInstBodies l x ty ids = do
      cenv <- asks tcClassEnv
      hd <- instHead ty
      case hd of
        TyCon c _ | Just ci <- M.lookup c cenv -> do
          let defined = [(l', m, pcs) | Loc l' (DDef m pcs) <- ids]
          ms <- fmap catMaybes $
            forM defined $ \(l', m, pcs) ->
              case lookup m (ciMethods ci) of
                Nothing -> do
                  -- renaming resolves m but does not check that it is a
                  -- method of c
                  atLoc l' $ reportError $ NotAMethod x m
                  pure Nothing
                Just sigTy -> do
                  let polyTy =
                        fromMaybe
                          (cannotHappen $ text "Instance type not of the form {{H1}} -> ... -> C ts:" <+> ppr ty)
                          (instMethodType ty (ciParams ci) sigTy)
                  pcs' <- checkSigDef l' m polyTy pcs
                  pure $ Just (m, polyTy, pcs')
          let omitted = [m | (m, _) <- ciMethods ci, m `notElem` [m' | (_, m', _) <- defined]]
          forM_ omitted $ \m ->
            unless (m `elem` ciDefaults ci) $
              atLoc l $
                reportError $
                  MissingMethod x m
          pure (ms, filter (`elem` ciDefaults ci) omitted)
        _ -> pure ([], [])

    -- G-3 3: for @forall as. {{H1}} -> ... -> {{Hk}} -> C ts@, with the
    -- @as@ skolemized and @H1 ... Hk@ as local instances @d1 ... dk@, each
    -- superclass of @C ts@ must be solvable. Returns the local instances
    -- and the dictionaries of the superclasses (used by desugaring, H-4-4).
    checkSuperInstances ty = do
      (_, TyQual _ instBody) <- skolemize ty
      instBody' <- normTy instBody
      let (hs, hd) = splitInstArrows instBody'
      ds <- mapM (const newGenName) hs
      let locals = zip ds hs
      cenv <- asks tcClassEnv
      dicts <- case hd of
        TyCon c ts | Just ci <- M.lookup c cenv ->
          forM (ciSupers ci) $ \s -> do
            g <- makeGoal locals (substTy (zip (ciParams ci) ts) s)
            solveGoals (ReportAtTopLevel True) [g]
            liftIO $ readIORef (goalRef g)
        _ -> pure [] -- not a class: reported at registration
      pure (locals, catMaybes dicts)

    mkClassInfo ps sups sigs defs =
      ClassInfo
        { ciParams = map BoundTv ps
        , ciSupers = map ty2ty sups
        , ciMethods = [(m, ty2ty t) | Loc _ (m, t) <- sigs]
        , ciDefaults = [n | Loc _ (DDef n _) <- defs]
        }

    fieldTys (NormalC _ tys) = tys
    fieldTys (GeneralC _ _ _ tyms) = map fst tyms

    -- The head of an instance type, forall as. {{H1}} -> ... -> C ts
    instHead ty = stripSyn . go <$> resolveSyn ty
      where
        go (TySyn _ t) = go t
        go (TyForAll _ (TyQual _ t)) = go t
        go (InstFunTy _ t) = go t
        go t = t

    -- Renaming ensures that an instance head is a type constructor applied
    -- to types; the name is used as a key even if it is not a class (the
    -- error has been reported).
    headName (TyCon n _) = n
    headName _ = error "Cannot happen: the head of an instance must be C t1 ... tn."

    convConDecl (NormalC cn tys) = (cn, [], [], map ty2ty tys)
    convConDecl (GeneralC cn xs q tys) = (cn, xs, concatMap c2c q, map (ty2ty . fst) tys)

    mkConTable (n, ns, cdecls) =
      let tvs = map BoundTv ns
          retTy = TyCon n $ map TyVar tvs
      in  flip map cdecls $ \case
            (Loc _ (NormalC cn tys)) ->
              (cn, ConTy tvs [] [] [(ty2ty ty, TyMult one) | ty <- tys] retTy)
            (Loc _ (GeneralC cn xs q tyms)) ->
              let xs' = map BoundTv xs
                  q' = concatMap c2c q
                  tyms' = map (\(t, m) -> (ty2ty t, ty2ty m)) tyms
              in  (cn, ConTy tvs xs' q' tyms' retTy)

inferMutual ::
  Bool --
  -> [LDecl 'Renaming]
  -> TC ([LDecl 'TypeCheck], [(Name, PolyTy)], UseMap)
inferMutual isTopLevel decls = do
  let names = [n | Loc _ (DDef n _) <- decls]
  let defs = [(loc, n, pcs) | Loc loc (DDef n pcs) <- decls]
  let sigMap = M.fromList [(n, ty2ty t) | Loc _ (DSig n t) <- decls]
  mapM_ checkClassTypesL [t | Loc _ (DSig _ t) <- decls] -- G-4

  (nts0g, umap) <- pushLevel $ do
    tys <- forM names $ \n -> case M.lookup n sigMap of
      Just t -> pure t
      Nothing -> newMetaTy

    fmap gatherU $ withVars (zip names tys) $ forM defs $ \(loc, n, pcs) -> atLoc loc $ do
      -- the goals of each definition are collected (E-2)
      ((entry, umap), goals) <- gatherGoals $
        case M.lookup n sigMap of
          Nothing -> do
            bodyTy <- newMetaTy
            (args, resTy) <- alignPatsTy (firstPats pcs) bodyTy
            ((pcs', umap), cs) <- gatherConstraint $ gatherAltUC =<< mapM (checkTyPC loc args resTy) pcs
            pure ((n, loc, Left (cs, bodyTy), pcs'), raiseUse omega umap)
          Just polyTy -> do
            -- defer escape check
            (pcs', umap, (skVars, given, cs)) <- checkSigDefBody loc polyTy pcs
            pure ((n, loc, Right (skVars, polyTy, given, cs), pcs'), raiseUse omega umap)
      pure ((entry, goals), umap)

  let (nts0, goalss) = unzip nts0g

  -- E-2: the goals of the group are solved after all of its bodies, before
  -- generalization and the multiplicity constraints. Undecidable ones are
  -- postponed outward from a local group, and errors at the top level.
  forM_ (zip nts0 goalss) $ \((_, _, tt, _), goals) ->
    solveGoals
      ( if isTopLevel
          then ReportAtTopLevel (either (const False) (const True) tt)
          else PostponeOutward
      )
      goals

  let skVarss = [(n, loc, sks, polyTy) | (n, loc, Right (sks, polyTy, _, _), _) <- nts0]

  nts1 <- forM nts0 $ \(n, loc, tt, pcs') -> atLoc loc $ case tt of
    Left (cs, bodyTy) -> do
      csOrig <- readConstraint
      setConstraint cs

      -- NB: No type variables exacpe in the useMap so using emptyUseMap is OK.
      polyTy <- tryGeneralizeTy isTopLevel bodyTy emptyUseMap

      do csCurr <- readConstraint; setConstraint (csCurr ++ csOrig)
      pure (n, loc, polyTy, pcs')
    Right (_, polyTy, given, cs) -> do
      finishSigDef isTopLevel n polyTy given cs
      pure (n, loc, polyTy, pcs')

  tyVars <- freeTyVars <$> mapM (\(_, _, ty, _) -> zonkType ty) nts1

  forM_ skVarss $ \(n, loc, skVars, polyTy) -> do
    let escaped = filter (`elem` tyVars) skVars
    unless (null escaped) $
      atLoc loc $
        reportError $
          CannotHavePolyTy polyTy escaped

  let decls' = [Loc loc (DDef (n, ty) pcs') | (n, loc, ty, pcs') <- nts1]
  let binds' = [(n, ty) | (n, _, ty, _) <- nts1]

  pure (decls', binds', umap)
  where
    -- --  let nes = [ (n,e) | Loc _ (DDef n _) <- decls ]
    -- let ns = [n | Loc _ (DDef n _) <- decls]
    -- let defs = [(loc, n, pcs) | Loc loc (DDef n pcs) <- decls]
    -- let sigMap = M.fromList [(n, ty2ty t) | Loc _ (DSig n t) <- decls]

    -- -- save current constraint at the point
    -- csOrig <- readConstraint
    -- setConstraint []

    -- (nts0, umap) <- pushLevel $ do
    --   tys <-
    --     forM
    --       ns
    --       ( \n -> case M.lookup n sigMap of
    --           Just t -> return t
    --           Nothing -> newMetaTy
    --       )
    --   (nts0, umap) <- fmap gatherU $ withVars (zip ns tys) $ forM defs $ \(loc, n, pcs) -> do
    --     -- body's type
    --     ty <- newMetaTy
    --     -- argument's multiplicity
    --     qs <- mapM (const newMetaTy) [1 .. numPatterns pcs]

    --     (pcs', umap) <- gatherAltUC =<< mapM (flip (checkTyPC loc qs) ty) pcs

    --     -- type of n in the environment
    --     tyE <- askType loc n

    --     unless (M.member n sigMap) $
    --       -- unify the body type and returned type
    --       atLoc loc $
    --         tryUnify ty tyE

    --     -- cut the current constraint
    --     cs <- readConstraint
    --     setConstraint []

    --     return ((n, loc, ty, cs, pcs'), raiseUse omega umap)

    --   return (nts0, umap)

    -- nts1 <- forM nts0 $ \(n, loc, ty, cs, pcs') -> do
    --   csO <- readConstraint
    --   -- Assuming that the current constraint is empty
    --   setConstraint cs

    --   res <- case M.lookup n sigMap of
    --     Nothing -> do
    --       -- NB: No type variables exacpe in the useMap so using emptyUseMap is OK.
    --       polyTy <- tryGeneralizeTy isTopLevel ty emptyUseMap
    --       return (n, loc, polyTy, pcs')
    --     Just sigTy -> do
    --       -- if a function comes with a signature, we check that its inferred type is more polymorphic than
    --       -- the signature
    --       checkGeneralizeTy loc isTopLevel ty emptyUseMap sigTy
    --       return (n, loc, sigTy, pcs')

    --   do
    --     cs' <- readConstraint
    --     setConstraint (csO ++ cs')
    --   return res

    -- let decls' = [Loc loc (DDef (n, ty) pcs') | (n, loc, ty, pcs') <- nts1]
    -- let binds' = [(n, ty) | (n, _, ty, _) <- nts1]

    -- -- restore the original constraint
    -- do
    --   cs' <- readConstraint
    --   setConstraint (csOrig ++ cs')

    -- return (decls', binds', umap)

    gatherU [] = ([], M.empty)
    gatherU ((x, u) : ts) =
      let (xs, u') = gatherU ts
      in  (x : xs, mergeUseMap u u')

    -- gatherC [] = ([],[])
    -- gatherC ((x,c):ts) =
    --   let (xs, c') = gatherC ts
    --   in (x:xs, c++c')

    -- gatherUC :: [(a,UseMap,[b])] -> ([a], UseMap, [b])
    -- gatherUC [] = ([], M.empty, [])
    -- gatherUC ((x,u,c):ts) =
    --   let (xs, u',c') = gatherUC ts
    --   in  (x:xs, mergeUseMap u u', c ++ c')


-- | The argument patterns of the first clause; by renaming, all clauses
--   have the same number of patterns (and instance patterns at the same
--   positions).
firstPats :: [([LPat p], Clause p)] -> [LPat p]
firstPats ((ps, _) : _) = ps
firstPats _ = error "Cannot happen."

-- | Checks a clause of a definition against the aligned argument types and
--   the result type.
checkTyPC ::
  SrcSpan
  -> [Slot]
  -> BodyTy
  -> ([LPat 'Renaming], Clause 'Renaming)
  -> TC (([LPat 'TypeCheck], Clause 'TypeCheck), UseMap)
checkTyPC loc slots resTy (ps0, c) = atLoc loc $ do
  -- inserted instance patterns bind the variables of the slots, shared by
  -- all clauses of the definition (C-2)
  (ps, muls, tys, locals) <- expandSlots slots ps0

  ((c', umap), ps', bind) <- checkPatsTyK ps muls (map Check tys) $ withLocalInsts locals $ do
    when (any hasPRev ps) $ void $ ensureRevTy resTy
    checkClauseTy c (Check resTy)

  let umap' = raiseUse omega umap

  let xqs = map (\(x, _, q) -> (x, q)) bind

  atLocMaybe (locPS ps) $ constrainVars xqs umap
  return ((ps', c'), foldr (M.delete . fst) umap' xqs)

-- | The part of checking a definition with a signature that is done inside
--   its group (G-5 1): skolemization, alignment of the patterns and checking
--   of the clauses. Returns the skolems, the given constraints and the
--   wanted constraints, for 'finishSigDef' and the escape check.
checkSigDefBody ::
  SrcSpan
  -> PolyTy
  -> [([LPat 'Renaming], Clause 'Renaming)]
  -> TC ([([LPat 'TypeCheck], Clause 'TypeCheck)], UseMap, ([TyVar], [TyConstraint], [InferredConstraint]))
checkSigDefBody loc polyTy pcs = do
  (skVars, TyQual given bodyTy) <- skolemize polyTy

  (args, resTy) <- alignPatsTy (firstPats pcs) bodyTy
  ((pcs', umap), cs) <- gatherConstraint $ gatherAltUC =<< mapM (checkTyPC loc args resTy) pcs

  pure (pcs', umap, (skVars, given, cs))

-- | Checks a top-level definition with a signature on its own, without
--   binding its name (G-5 1): default methods and instance bodies, in
--   which a method name refers to the global method. As for a top-level
--   definition with a signature in 'inferMutual', the goals are solved
--   right after the body (E-2) and the constraints must be solved here.
checkSigDef ::
  SrcSpan
  -> Name
  -> PolyTy
  -> [([LPat 'Renaming], Clause 'Renaming)]
  -> TC TypedClauses
checkSigDef loc n polyTy pcs = atLoc loc $ do
  ((pcs', _, (_, given, cs)), goals) <- pushLevel $ gatherGoals $ checkSigDefBody loc polyTy pcs
  solveGoals (ReportAtTopLevel True) goals
  finishSigDef True n polyTy given cs
  pure pcs'

-- | The type against which the body of method @m@ in an instance is
--   checked (G-5 3). For the instance type
--   @forall as. cs0 => {{H1}} -> ... -> {{Hk}} -> C ts@ and the signature
--   @forall bs. cs => t@ of @m@ in @class C params@, it is
--   @forall as bs. cs0, cs[ts/params] => {{H1}} -> ... -> {{Hk}} -> t[ts/params]@.
--   Both types name their variables by 'Alpha' indices, so every variable
--   of the signature other than the parameters (the @bs@ and those bound
--   inside @t@) is first shifted above the indices of the instance type;
--   otherwise a variable of @ts@ could be captured by them.
instMethodType :: Ty -> [TyVar] -> Ty -> Maybe PolyTy
instMethodType instTy params sigTy =
  case splitInstArrows instBody of
    (hs, TyCon _ ts) ->
      let tbl = zip params ts
      in  Just $
            TyForAll
              (as ++ bs)
              (TyQual (cs0 ++ map (substTyC tbl) cs) (foldr InstFunTy (substTy tbl t) hs))
    _ -> Nothing -- not of the form C ts: rejected by renaming
  where
    (as, cs0, instBody) = splitPoly instTy
    (bs, cs, t) = splitPoly (mapBoundTv shift sigTy)

    splitPoly (TyForAll vs (TyQual qs ty)) = (vs, qs, ty)
    splitPoly ty = ([], [], ty)

    offset = maximum (-1 : alphaIndices instTy) + 1
    shift v@(BoundTv (Alpha i nb)) | v `notElem` params = BoundTv (Alpha (i + offset) nb)
    shift v = v

-- | Splits @{{H1}} -> ... -> {{Hk}} -> t@ into @[H1, ..., Hk]@ and @t@.
splitInstArrows :: Ty -> ([Ty], Ty)
splitInstArrows (InstFunTy h t) = first (h :) (splitInstArrows t)
splitInstArrows t = ([], t)

-- | Renames every bound type variable, including binders.
mapBoundTv :: (TyVar -> TyVar) -> Ty -> Ty
mapBoundTv f = go
  where
    go (TyVar v) = TyVar (f v)
    go (TyCon c ts) = TyCon c (map go ts)
    go (TyMetaV m) = TyMetaV m
    go (TyForAll vs (TyQual qs ty)) = TyForAll (map f vs) (TyQual (map goC qs) (go ty))
    go (TySyn o u) = TySyn (go o) (go u)
    go (TyMult m) = TyMult m
    goC (MSub t1 ts) = MSub (go t1) (map go ts)
    goC (TyEq t1 t2) = TyEq (go t1) (go t2)

-- | The 'Alpha' indices of the type variables in a type, including binders.
alphaIndices :: Ty -> [Int]
alphaIndices = go
  where
    go (TyVar v) = tv v
    go (TyCon _ ts) = concatMap go ts
    go (TyMetaV _) = []
    go (TyForAll vs (TyQual qs ty)) = concatMap tv vs ++ concatMap goC qs ++ go ty
    go (TySyn o u) = go o ++ go u
    go (TyMult _) = []
    goC (MSub t1 ts) = concatMap go (t1 : ts)
    goC (TyEq t1 t2) = go t1 ++ go t2
    tv (BoundTv (Alpha i _)) = [i]
    tv _ = []

-- | The part of checking a definition with a signature that is done after
--   its group (G-5 1): the wanted constraints are solved under the given
--   ones (at the top level they must be solved here).
finishSigDef :: Bool -> Name -> PolyTy -> [TyConstraint] -> [InferredConstraint] -> TC ()
finishSigDef isTopLevel n polyTy given cs = do
  do
    cs' <- mapM zonkTypeIC cs
    debugPrint 3 $ text "inferMutual:" <+> align (vsep [text "Given: " <> ppr given, text "Wanted: " <> ppr cs'])

  currentTcLevel <- askCurrentTcLevel
  invisibleMetaVars <-
    filterM
      ( \m -> do
          lv <- readTcLevelMv m
          return $ lv > currentTcLevel
      )
      (nub $ metaTyVars cs)

  whenChecking (CheckingType n polyTy) $
    if isTopLevel
      then do
        -- if this is called in the top level cs must be solved at this point
        csRes <- solveInferredConstraint True invisibleMetaVars given cs
        unless (null csRes) $
          reportError $
            ImplicationCheckFail invisibleMetaVars given csRes
      else
        if null given
          then do csCurr <- readConstraint; setConstraint (cs ++ csCurr)
          else addImpConstraint invisibleMetaVars given cs

-- checkTyPC loc qs (ps, c) expectedTy = atLoc loc $ do
--   muls <- mapM ty2mult qs
--   tys <- mapM (const newMetaTy) ps
--   retTy <- newMetaTy

--   -- (ps', bind) <- checkPatsTy ps muls tys
--   -- (c', umap) <- withVars [ (n,t) | (n,t,_) <- bind ] $ checkClauseTy c retTy

--   ((c', umap), ps', bind) <- checkPatsTyK ps muls tys $ do
--     when (any hasPRev ps) $ void $ ensureRevTy retTy
--     checkClauseTy c retTy

--   tryUnify (foldr (uncurry tyarr) retTy $ zip qs tys) expectedTy

--   let umap' = raiseUse omega umap

--   let xqs = map (\(x, _, q) -> (x, q)) bind

--   atLocMaybe (locPS ps) $ constrainVars xqs umap
--   return ((ps', c'), foldr (M.delete . fst) umap' xqs)

checkClauseTy :: Clause 'Renaming -> Expected BodyTy -> TC (Clause 'TypeCheck, UseMap)
checkClauseTy (Clause e ws wi) expectedTy = do
  (ws', bind, umap) <- inferDecls False ws
  withVars bind $ do
    (e', umapE) <- checkTy e expectedTy
    (wi', umapWi) <- case wi of
      Just ewi -> do
        ty <- atLoc (location e) $ expectRevTy expectedTy
        (ewi', umapWi) <- checkTyM ewi (Check (ty *-> boolTy)) omega
        return (Just ewi', umapWi)
      Nothing -> return (Nothing, M.empty)
    return (Clause e' ws' wi', umap `mergeUseMap` umapE `mergeUseMap` umapWi)

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

quantify :: [MetaTyVar] -> QualTy -> TC PolyTy
quantify mvs0 ty0 = do
  -- debugPrint 2 $ red $ text "Simpl:" <+> align (group (ppr (mvs0, ty0)) <> line <> text "-->" <> line <> group (ppr (mvs, ty)))
  -- liftIO $ print $ red $ "Generalization:" <+> ppr (zip mvs newBinders)

  (mvs, ty) <- do
    let TyQual cs0 t0 = ty0
        visibleVars = nub $ metaTyVars [t0] ++ concatMap gatherMvInTyEq cs0
        invisibles = mvs0 \\ visibleVars
    cs <- eliminateExistentialL invisibles cs0
    return (mvs0 \\ invisibles, TyQual cs t0)

  let usedBinders = bindersQ ty
      newBinders = take (length mvs) $ allFancyBinders \\ usedBinders

  forM_ (zip mvs newBinders) $
    \(mv, tyv) -> writeTyVar mv (TyVar tyv)
  ty' <- zonkTypeQ ty
  return $ TyForAll newBinders ty'
  where
    gatherMvInTyEq (TyEq t1 t2) = metaTyVars [t1, t2]
    gatherMvInTyEq _ = []

    binders (TyForAll bs t) = bs ++ bindersQ t
    binders (TyCon _ ts) = concatMap binders ts
    binders (TyVar _) = []
    binders (TySyn t _) = binders t
    binders (TyMetaV _) = []
    binders (TyMult _) = []

    bindersQ (TyQual cs t) = concatMap bindersC cs ++ binders t

    bindersC (MSub t1 ts2) = binders t1 ++ concatMap binders ts2
    bindersC (TyEq t1 t2) = binders t1 ++ binders t2

allFancyBinders :: [TyVar]
allFancyBinders =
  map (BoundTv . Local . User) $
    [[x] | x <- ['a' .. 'z']]
      ++ [x : show i | i <- [1 :: Integer ..], x <- ['a' .. 'z']]
