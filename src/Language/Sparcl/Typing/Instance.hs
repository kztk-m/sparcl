{-# LANGUAGE OverloadedStrings #-}

-- | Instance search and the solving of instance goals (E-2, E-3 and the
--   revised E-4 in notes/extend-type-class_2026.txt).
--
--   A goal @C ts@ is searched among
--
--   * local instances (variables bound by @{{x}}@ or by inserted
--     abstractions) and their superclasses, by projections;
--   * global instances (instance declarations).
--
--   The metas of a goal are never instantiated by search: a goal that
--   cannot be decided because of its metas is "stuck" and is postponed.
module Language.Sparcl.Typing.Instance (
  SearchResult (..),
  searchGoal,
  Unsolved (..),
  solveGoals,
  reportLeftoverGoals,
  makeGoal,
  normTy,
  maxSearchDepth,
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

-- | The depth limit of instance search (E-3 3), shared by the recursion on
--   subgoals of global instances and the projection steps to superclasses
--   of local instances.
maxSearchDepth :: Int
maxSearchDepth = 32

data SearchResult
  = -- | the dictionary, and goals postponed for its subgoals
    SFound !(LExp 'TypeCheck) ![Goal]
  | -- | cannot be decided because of metas; to be postponed
    SStuck
  | SNoInstance !Ty
  | SAmbiguous !Ty ![Name]
  | STooDeep !Ty

-- | Zonks a type, expands synonyms and drops their records.
normTy :: Ty -> TC Ty
normTy ty = dropSyn <$> (resolveSyn =<< zonkType ty)
  where
    dropSyn (TySyn _ t) = dropSyn t
    dropSyn (TyCon c ts) = TyCon c (map dropSyn ts)
    dropSyn (TyForAll vs (TyQual cs t)) = TyForAll vs (TyQual cs (dropSyn t))
    dropSyn t = t

-- * Unification and matching without side effects

data V = VB TyVar | VM MetaTyVar
  deriving (Eq)

type Sub = [(V, Ty)]

-- | Unification in which the given (bound) type variables of a candidate
--   and, when @metasFlexible@, the meta variables of the goal may be
--   instantiated; skolems and other variables are rigid. Nothing is
--   written to meta variables. With @metasFlexible = False@ it is the
--   one-way matching of E-4 (the candidate's variables are disjoint from
--   the goal's).
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
              (TyCon c ts, TyCon d us)
                | c == d && length ts == length us ->
                    foldM (\s' (a, b) -> go s' a b) s (zip ts us)
              (TyVar a, TyVar b) | a == b -> Just s
              (TyMetaV a, TyMetaV b) | a == b -> Just s
              (TyMult m, TyMult n) | m == n -> Just s
              _ -> Nothing

    bind s v t
      | occurs s v t = Nothing
      | otherwise = Just ((v, t) : s)

    occurs s v t =
      let t' = walk s t
      in  case varOf t' of
            Just v' -> v == v'
            Nothing -> case t' of
              TyCon _ ts -> any (occurs s v) ts
              _ -> False

-- | Applies a substitution for the candidate's variables.
applySub :: Sub -> Ty -> Ty
applySub s = substTy [(v, resolve t) | (VB v, t) <- s]
  where
    resolve t@(TyVar v) = maybe t resolve (lookup (VB v) s)
    resolve (TyCon c ts) = TyCon c (map resolve ts)
    resolve t = t

hasMetas :: Ty -> Bool
hasMetas = not . null . metaTyVars

-- * Candidates

-- | The local instances and their superclasses (E-3 (i), (ii)), in the
--   order used to choose among several (E-4 (3)): direct ones before
--   projections, and within each, the innermost first. Projections are
--   followed up to the given number of steps; the flag tells whether the
--   enumeration was cut by it. Candidates of the same type as an earlier
--   one are dropped (so cyclic superclasses end).
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
splitInstTy (InstFunTy h t) =
  let (vs, hs, hd) = splitInstTy t in (vs, h : hs, hd)
splitInstTy t = ([], [], t)

-- * Search

-- | Searches a goal (E-3, E-4 revised).
searchGoal :: Goal -> TC SearchResult
searchGoal g = normTy (goalTy g) >>= searchTy g 0

searchTy :: Goal -> Int -> Ty -> TC SearchResult
searchTy _ depth ty
  | depth > maxSearchDepth = pure (STooDeep ty)
searchTy g depth ty@(TyCon c _) = do
  -- L: local instances (E-4 (2), (3))
  (locals, cut) <- localCandidates (maxSearchDepth - depth) (goalLocals g)
  let matching = [e | (lt, e) <- locals, isJust (unifyPure [] False lt ty)]
      unifiable = [() | (lt, _) <- locals, isJust (unifyPure [] True lt ty)]
  case matching of
    e : _ -> pure (SFound e [])
    []
      | not (null unifiable) -> pure SStuck
      | otherwise -> globals cut
  where
    -- G: global instances (E-4 (4) revised)
    globals cut = do
      ienv <- asks tcInstEnv
      cands <- forM (maybe [] M.toList (M.lookup c ienv)) $ \(x, ity) -> do
        ity' <- normTy ity
        pure (x, ity, splitInstTy ity')
      let us = [cand | cand@(_, _, (vs, _, hd)) <- cands, isJust (unifyPure vs True hd ty)]
      case us of
        [] -> pure (if cut then STooDeep ty else SNoInstance ty)
        [(x, ity, (vs, hs, hd))] -> case unifyPure vs False hd ty of
          Nothing -> pure SStuck -- would instantiate metas of the goal
          Just s -> commit x ity (map (applySub s) hs)
        _
          | hasMetas ty -> pure SStuck
          | otherwise -> pure (SAmbiguous ty [x | (x, _, _) <- us])

    -- Subgoals are solved on the spot; stuck ones are postponed as new
    -- goals in the same scope.
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

-- | Makes a goal in the current scope, without adding it to the list of
--   goals (used for the superclass check, G-3 3-b).
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

-- | The hole standing for a goal's dictionary.
goalHole :: Goal -> LExp 'TypeCheck
goalHole g = Loc (fromMaybe NoLoc (goalLoc g)) (InstHole () (goalId g, goalTy g) (goalRef g))

-- | What to do with goals that cannot be decided (E-2).
data Unsolved
  = -- | in a local group: put back into the outer list (outer uses may fix
    --   the metas)
    PostponeOutward
  | -- | at the top level (the flag: the definition has a signature): an
    --   error, "write a signature" if the metas would be generalized in a
    --   definition without a signature, "ambiguous" otherwise
    ReportAtTopLevel Bool

-- | Solves goals: a found dictionary is written to the goal's hole; stuck
--   goals (and stuck subgoals) are handled by the policy; errors are
--   reported where the goals were made.
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
          -- In a top-level definition without a signature, a goal whose
          -- metas would be generalized is reported as "write a signature"
          -- even if no instance matches (with a signature, a local instance
          -- would solve it).
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

    -- whether the type has metas of an inner level (generalized at the top
    -- level)
    wouldBeGeneralized ty = do
      lv <- askCurrentTcLevel
      lvs <- mapM readTcLevelMv (nub (metaTyVars ty))
      pure (any (> lv) lvs)

-- | Reports the goals left in the list (after the top level, E-2: none
--   should remain) as ambiguous.
reportLeftoverGoals :: TC ()
reportLeftoverGoals = do
  ref <- asks tcGoals
  gs <- liftIO $ readIORef ref
  liftIO $ writeIORef ref []
  unless (null gs) $
    mapM_ (\g -> normTy (goalTy g) >>= atGoal g . reportError . AmbiguousGoal) gs
