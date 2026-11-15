{-# LANGUAGE OverloadedStrings #-}

-- | Instance search and the solving of instance goals (see notes/TypeClasses.md).
module Language.Sparcl.Typing.Instance (
  SearchResult (..),
  searchGoal,
  Unsolved (..),
  solveGoals,
  reportLeftoverGoals,
  makeGoal,
  normTy,
  maxSearchDepth,
  -- exported for the unit tests of unification (test/Spec.hs)
  V (..),
  Sub,
  unifyPure,
) where

import Control.Monad (foldM, forM, unless)
import Control.Monad.IO.Class (liftIO)
import Control.Monad.Reader (asks)
import Data.IORef (newIORef, readIORef, writeIORef)
import Data.List (nub)
import qualified Data.Map as M
import Data.Maybe (fromMaybe, isJust)

import Language.Sparcl.Name
import Language.Sparcl.Pass
import Language.Sparcl.SrcLoc
import Language.Sparcl.Surface.Syntax (Arg (..), Exp (..), LExp)
import Language.Sparcl.Typing.TCMonad
import Language.Sparcl.Typing.Type

maxSearchDepth :: Int
maxSearchDepth = 32

data SearchResult
  = -- | the dictionary and the postponed subgoals
    SFound !(LExp 'TypeCheck) ![Goal]
  | -- | undecided because of metas
    SStuck
  | SNoInstance !Ty
  | SAmbiguous !Ty ![Name]
  | STooDeep !Ty

-- | Zonks a type, expands synonyms and drops their records.
normTy :: Ty -> TC Ty
normTy ty = dropSyn <$> (resolveSyn =<< zonkType ty)
  where
    dropSyn (TySyn _ t) = dropSyn t
    dropSyn (TyApp t1 t2) = TyApp (dropSyn t1) (dropSyn t2)
    dropSyn (TyFun m t1 t2) = TyFun (dropSyn m) (dropSyn t1) (dropSyn t2)
    dropSyn (TyInstFun c t) = TyInstFun (dropSyn c) (dropSyn t)
    dropSyn (TyForAll vs (TyQual cs t)) = TyForAll vs (TyQual cs (dropSyn t))
    dropSyn t = t

-- * Unification and matching without side effects

data V = VB TyVar | VM MetaTyVar
  deriving (Eq)

type Sub = [(V, Ty)]

-- | Unification over the given variables (and metas if @metasFlexible@) that writes no metas.
unifyPure :: [TyVar] -> Bool -> Ty -> Ty -> Maybe Sub
unifyPure vs metasFlexible = go []
  where
    varOf (TyVar v) | v `elem` vs = Just (VB v)
    varOf (TyMetaV m) | metasFlexible = Just (VM m)
    varOf _ = Nothing

    walk s t = case varOf t of
      Just v | Just t' <- lookup v s -> walk s t'
      _ -> t

    go s t1 t2 =
      let t1' = walk s t1
          t2' = walk s t2
      in  case (varOf t1', varOf t2') of
            (Just v1, Just v2) | v1 == v2 -> Just s
            (Just v, _) -> bind s v t2'
            (_, Just v) -> bind s v t1'
            _ -> case (t1', t2') of
              (TyConst c, TyConst d) | c == d -> Just s
              (TyApp a1 a2, TyApp b1 b2) -> goPairs s [(a1, b1), (a2, b2)]
              (TyFun m a1 a2, TyFun n b1 b2) -> goPairs s [(m, n), (a1, b1), (a2, b2)]
              (TyInstFun a1 a2, TyInstFun b1 b2) -> goPairs s [(a1, b1), (a2, b2)]
              (TyVar a, TyVar b) | a == b -> Just s
              (TyMetaV a, TyMetaV b) | a == b -> Just s
              (TyMult m, TyMult n) | m == n -> Just s
              _ -> Nothing

    goPairs = foldM (\s' (a, b) -> go s' a b)

    bind s v t
      | occurs s v t = Nothing
      | otherwise = Just ((v, t) : s)

    occurs s v t =
      let t' = walk s t
      in  case varOf t' of
            Just v' -> v == v'
            Nothing -> case t' of
              TyApp t1 t2 -> any (occurs s v) [t1, t2]
              TyFun m t1 t2 -> any (occurs s v) [m, t1, t2]
              TyInstFun c t2 -> any (occurs s v) [c, t2]
              _ -> False

applySub :: Sub -> Ty -> Ty
applySub s = substTy [(v, resolve t) | (VB v, t) <- s]
  where
    resolve t@(TyVar v) = maybe t resolve (lookup (VB v) s)
    resolve (TyApp t1 t2) = TyApp (resolve t1) (resolve t2)
    resolve (TyFun m t1 t2) = TyFun (resolve m) (resolve t1) (resolve t2)
    resolve (TyInstFun c t) = TyInstFun (resolve c) (resolve t)
    resolve t = t

hasMetas :: Ty -> Bool
hasMetas = not . null . metaTyVars

-- * Candidates

-- | The local instances and their superclasses, in order of preference.
localCandidates :: Int -> [(Name, Ty)] -> TC ([(Ty, LExp 'TypeCheck)], Bool)
localCandidates budget locals = do
  direct <- forM locals $ \(d, c) -> do
    c' <- normTy c
    pure (c', noLoc (Var (d, c)))
  loop (dedupe [] direct) (dedupe [] direct) budget
  where
    loop acc frontier steps
      | null frontier = pure (acc, False)
      | otherwise = do
          next <- concat <$> mapM supersOf frontier
          let new = dedupe acc next
          if
            | null new -> pure (acc, False)
            | steps <= 0 -> pure (acc, True)
            | otherwise -> loop (acc ++ new) new (steps - 1)

    dedupe seen = foldl (\ys x -> if fst x `elem` map fst (seen ++ ys) then ys else ys ++ [x]) []

    supersOf (TyCon c ts, e) = do
      cenv <- asks tcClassEnv
      case M.lookup c cenv of
        Nothing -> pure []
        Just ci ->
          forM (zip [0 ..] (ciSupers ci)) $ \(i, s) -> do
            s' <- normTy (substTy (zip (ciParams ci) ts) s)
            pure (s', projApp c ci i e)
    supersOf _ = pure []

    projApp c ci i e =
      let l = location e
      in  Loc l (App (Loc l (Var (superProjName c i, superProjType c ci i))) (ExplicitArg e))

-- | Splits an instance type @forall as. {{H1}} -> ... -> {{Hk}} -> C us@.
splitInstTy :: Ty -> ([TyVar], [Ty], Ty)
splitInstTy (TyForAll vs (TyQual _ t)) =
  let (vs', hs, hd) = splitInstTy t in (vs ++ vs', hs, hd)
splitInstTy (TyInstFun h t) =
  let (vs, hs, hd) = splitInstTy t in (vs, h : hs, hd)
splitInstTy t = ([], [], t)

-- * Search

searchGoal :: Goal -> TC SearchResult
searchGoal g = normTy (goalTy g) >>= searchTy g 0

searchTy :: Goal -> Int -> Ty -> TC SearchResult
searchTy _ depth ty
  | depth > maxSearchDepth = pure (STooDeep ty)
searchTy g depth ty@(TyCon c _) = do
  (locals, cut) <- localCandidates (maxSearchDepth - depth) (goalLocals g)
  let matching = [e | (lt, e) <- locals, isJust (unifyPure [] False lt ty)]
      unifiable = [() | (lt, _) <- locals, isJust (unifyPure [] True lt ty)]
  case matching of
    e : _ -> pure (SFound e [])
    []
      | not (null unifiable) -> pure SStuck
      | otherwise -> globals cut
  where
    globals cut = do
      ienv <- asks tcInstEnv
      cands <- forM (maybe [] M.toList (M.lookup c ienv)) $ \(x, ity) -> do
        ity' <- normTy ity
        pure (x, ity, splitInstTy ity')
      let us = [cand | cand@(_, _, (vs, _, hd)) <- cands, isJust (unifyPure vs True hd ty)]
      case us of
        [] -> pure (if cut then STooDeep ty else SNoInstance ty)
        [(x, ity, (vs, hs, hd))] -> case unifyPure vs False hd ty of
          Nothing -> pure SStuck
          Just s -> commit x ity (map (applySub s) hs)
        _
          | hasMetas ty -> pure SStuck
          | otherwise -> pure (SAmbiguous ty [x | (x, _, _) <- us])

    commit x ity hs = do
      rs <- forM hs $ \h -> do
        h' <- normTy h
        r <- searchTy g (depth + 1) h'
        case r of
          SStuck -> do
            sub <- makeGoalLike g h'
            pure (Right (goalHole sub, [sub]))
          SFound e gs -> pure (Right (e, gs))
          err -> pure (Left err)
      case [err | Left err <- rs] of
        err : _ -> pure err
        [] -> do
          let l = fromMaybe NoLoc (goalLoc g)
              args = [e | Right (e, _) <- rs]
              dict = foldl (\f a -> Loc l (App f (InstArg a))) (Loc l (Var (x, ity))) args
          pure (SFound dict (concat [gs | Right (_, gs) <- rs]))
searchTy _ _ _ = pure SStuck

-- * Goals

-- | Makes a goal without adding it to the list of goals.
makeGoal :: [(Name, Ty)] -> Ty -> TC Goal
makeGoal locals c = do
  g <- newGenName
  ref <- liftIO $ newIORef Nothing
  lv <- askCurrentTcLevel
  l <- asks tcLoc
  ctx <- currentTypeErrorContext
  pure
    Goal
      { goalId = g
      , goalRef = ref
      , goalTy = c
      , goalLocals = locals
      , goalLevel = lv
      , goalLoc = l
      , goalCtx = ctx
      }

-- | A goal for a subgoal, in the scope of the given goal.
makeGoalLike :: Goal -> Ty -> TC Goal
makeGoalLike g c = do
  n <- newGenName
  ref <- liftIO $ newIORef Nothing
  pure g{goalId = n, goalRef = ref, goalTy = c}

goalHole :: Goal -> LExp 'TypeCheck
goalHole g = Loc (fromMaybe NoLoc (goalLoc g)) (InstHole () (goalId g, goalTy g) (goalRef g))

-- | What to do with goals that cannot be decided.
data Unsolved
  = -- | put back into the outer list of goals
    PostponeOutward
  | -- | report as errors (the flag: the definition has a signature)
    ReportAtTopLevel Bool

solveGoals :: Unsolved -> [Goal] -> TC ()
solveGoals policy = mapM_ solveOne
  where
    solveOne g = do
      r <- searchGoal g
      case r of
        SFound e gs -> do
          liftIO $ writeIORef (goalRef g) (Just e)
          mapM_ unsolved gs
        SStuck -> unsolved g
        SNoInstance ty -> do
          gen <- wouldBeGeneralized ty
          atGoal g $
            reportError $
              case policy of
                ReportAtTopLevel False | gen -> CannotInferInstArg ty
                _ -> NoInstance ty
        SAmbiguous ty ns -> atGoal g $ reportError (AmbiguousInstances ty ns)
        STooDeep ty -> atGoal g $ reportError (InstSearchTooDeep ty)

    unsolved g = case policy of
      PostponeOutward -> addGoals [g]
      ReportAtTopLevel hasSig -> do
        ty <- normTy (goalTy g)
        generalizable <- wouldBeGeneralized ty
        atGoal g $
          reportError $
            if not hasSig && generalizable
              then CannotInferInstArg ty
              else AmbiguousGoal ty

    wouldBeGeneralized ty = do
      lv <- askCurrentTcLevel
      lvs <- mapM readTcLevelMv (nub (metaTyVars ty))
      pure (any (> lv) lvs)

reportLeftoverGoals :: TC ()
reportLeftoverGoals = do
  ref <- asks tcGoals
  gs <- liftIO $ readIORef ref
  liftIO $ writeIORef ref []
  unless (null gs) $
    mapM_ (\g -> normTy (goalTy g) >>= atGoal g . reportError . AmbiguousGoal) gs
