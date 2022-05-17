{-# LANGUAGE ConstraintKinds #-}
module Language.Sparcl.Desugar (
  desugarExp, desugarTopDecls,
  runDesugar
  ) where

import           Data.Function                  (on)
import           Data.List                      (groupBy)
import           Data.Void

import           Control.Monad.Reader
import           Control.Monad.State

import           Language.Sparcl.SrcLoc
import qualified Language.Sparcl.Surface.Syntax as S

import           Language.Sparcl.Name

import qualified Language.Sparcl.Core.Syntax    as C
import           Language.Sparcl.Pass
import           Language.Sparcl.Typing.TCMonad
import qualified Language.Sparcl.Typing.Type    as T

import           Language.Sparcl.Pretty         hiding (list, (<$>))
-- import Debug.Trace

import           Language.Sparcl.DebugPrint

type NameSource = Int -- de Brujin levels

-- Desugaring may refer to types, so it will use type checking monad.
type Desugar m a = MonadTypeCheck m => ReaderT NameSource m a

type MonadDesugar m = (MonadReader Int m, MonadTypeCheck m)

withNewName :: MonadDesugar m => (Name -> m r) -> m r
withNewName k = do
  i <- ask
  local (+1) (k (Generated i Desugaring))

withNewNames :: MonadDesugar m => Int -> ([Name] -> m r) -> m r
withNewNames n k = do
  i <- ask
  local (+ n) (k $ map (flip Generated Desugaring) [i..i+n-1])

runDesugar :: MonadTypeCheck m => Desugar m a -> m a
runDesugar m = runReaderT m 0

numberOfArgs :: T.Ty -> Int
numberOfArgs (T.TyCon n [_,_,t]) | n == nameTyArr = numberOfArgs t + 1
numberOfArgs _                   = 0

desugarExp :: forall m. MonadDesugar m => S.LExp 'TypeCheck -> m (C.Exp Name)
desugarExp (Loc _ expr) = go expr
  where
    go :: S.Exp 'TypeCheck -> m (C.Exp Name)

    go (S.Var (x, _)) = return $ C.Var x
    go (S.Lit l)      = return $ C.Lit l
    go (S.App e1 e2)  =
      mkApp <$> desugarExp e1 <*> desugarExp e2

    go (S.Abs ps e) = desugarRHS [(ps, S.Clause e (S.HDecls () []) Nothing)]

    go (S.Con (c, ty)) = do
      ty' <- zonkType ty
      let n = numberOfArgs ty'
      withNewNames n $ \xs -> do
        let b = C.Con c [ C.Var x | x <- xs ]
        return $ foldr C.Abs b xs
    -- go (S.Con (c,_ty) es) =
    --   C.Con c <$> mapM desugarExp es

    go (S.Case e alts) = do
      e'  <- desugarExp e
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
          bs' <- mapM (\(Loc _ (S.DDef (n,ty) pcs)) -> do
                          r <- desugarRHS pcs
                          return (n, ty, r)) bs
          return $ C.Let bs' e'

    go (S.Let1 p1 e1 e2) = go (S.App (noLoc (S.Abs [p1] e2)) e1)

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

    go (S.RCon (c, ty)) = do
      ty' <- zonkType ty
      let n = numberOfArgs ty'
      withNewNames n $ \xs -> do
        let b = C.RCon c [ C.Var x | x <- xs ]
        return $ foldr C.Abs b xs

    go (S.RDO as er) = go (unLoc $ desugarRDO as er)



desugarRDO :: [(S.LPat 'TypeCheck, Loc (S.Exp 'TypeCheck))] -> Loc (S.Exp 'TypeCheck) -> Loc (S.Exp 'TypeCheck)
desugarRDO = go [] id
  where
    app e1 e2 = noLoc (S.App e1 e2)
    go _  _    [] er = er -- this branch is used only for the expressions of the form "revdo in e0"
    go ps kpin [(p,e)] er =
      let pinExp = kpin e
          pat    = noLoc $ S.PREV $ foldr1 (\p1 p2 -> makeTuplePatS [p1, p2]) $ reverse (p:ps)
      in noLoc $ S.Case pinExp [ (pat, S.Clause er (S.HDecls () []) Nothing)]

    go ps kpin ((p,e):as) er =
      let k hole = kpin $ noLoc S.RPin `app`
                          e `app`
                          noLoc (S.Abs [p] hole)
      in go (p:ps) k as er


makeTupleExpC :: [C.Exp Name] -> C.Exp Name
makeTupleExpC [e] = e
makeTupleExpC es  = C.Con (nameTuple (length es)) es

makeTuplePatS :: [S.LPat 'TypeCheck] -> S.LPat 'TypeCheck
makeTuplePatS [p] = p
makeTuplePatS ps  = noLoc (S.PCon (nameTuple len, T.conTy2Ty $ tupleConTy len) ps)
  where
    len = length ps

makeTuplePatC :: [C.Pat Name] -> C.Pat Name
makeTuplePatC [p] = p
makeTuplePatC ps  = C.PCon (nameTuple (length ps)) ps

makeCase :: Ord n => C.Exp n -> [(C.Pat n, C.Exp n)] -> C.Exp n
makeCase (C.Con n []) [(C.PCon m [], e)] | n == m = e
makeCase e0 [(C.PVar x, e)]              = mkApp (mkAbs x e) e0
makeCase e0 alts                         = C.Case e0 alts


-- Removes apparent eta-redex.
mkAbs :: Ord n => n -> C.Exp n -> C.Exp n
mkAbs n (C.App e (C.Var m)) | n == m && n `notElem` C.freeVars e = e
mkAbs n e                   = C.Abs n e

mkApp :: Eq n => C.Exp n -> C.Exp n -> C.Exp n
mkApp (C.Abs n e) e1 =
  case punchHoleAffine n e of
    Just c  -> c e1
    Nothing -> C.App (C.Abs n e) e1
  --subst n e1 e
mkApp e1 e2          = C.App e1 e2

-- data CheckSubst a = Substituted a
--                   | Untouched   a
--                   deriving Functor


data Occ a = Once !a | None !a | More
  deriving Functor

liftO2 :: (a -> b -> r) -> Occ a -> Occ b -> Occ r
liftO2 f (None a) (None b) = None (f a b)
liftO2 f (None a) (Once b) = Once (f a b)
liftO2 f (Once a) (None b) = Once (f a b)
liftO2 _ (Once _) (Once _) = More
liftO2 _ _        _        = More

-- @punchHoleAffine n e@ checks if @n@ occurs at most once in @e@, and
-- returned a holed expression if so.

punchHoleAffine :: Eq n => n -> C.Exp n -> Maybe (C.Exp n -> C.Exp n)
punchHoleAffine n = conv . go
  where
    conv More     = Nothing
    conv (None f) = Just f
    conv (Once f) = Just f

    list :: Monad f => [Occ (f a)] -> Occ (f [a])
    list = foldr (liftO2 $ liftM2 (:)) (None $ pure [])

    go (C.Var x) | x == n    = Once id
                 | otherwise = None (const $ C.Var x)

    go (C.Lit l) = None (const $ C.Lit l)
    go (C.App e1 e2) =
      liftO2 (liftM2 C.App) (go e1) (go e2)

    go (C.Abs x e) | x == n    = None (const $ C.Abs x e)
                   | otherwise = fmap (C.Abs x) <$> go e

    go (C.Con c es) =
      fmap (C.Con c) <$> list (map go es)

    go (C.Case _ _) = More
    go (C.Let _ _) = More
    go (C.RCase _ _) = More

    go (C.Lift e1 e2) =
      liftO2 (liftM2 C.Lift) (go e1) (go e2)

    go (C.Unlift e) = fmap C.Unlift <$> go e
    go (C.RCon c es) =
      fmap (C.RCon c) <$> list (map go es)

    go (C.RPin e1 e2) =
      liftO2 (liftM2 C.RPin) (go e1) (go e2)


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
          | CPVar  !Name
          | CPCon  !Name ![ CPat ]
--          | CPBang CPat
          deriving (Eq , Show)


instance Pretty CPat where
  pprPrec _ CPHole    = text "_"
  pprPrec _ (CPVar n) = ppr n
  pprPrec _ (CPCon n []) = ppr n
  pprPrec k (CPCon n ps) = parensIf (k > 0) $ ppr n <+> hsep (map (pprPrec 1) ps)
--  pprPrec _ (CPBang p)   = text "!" <> pprPrec 1 p



-- | 'separatePat' separate a unidirectional pattern from a pattern.
--   For example, for a patter @Cons a (rev b)@, it returns
--   @Cons a _@ and @[b]@. Extracted reversible patterns are ordered
--   from left-to-right. For example, for @Cons (rev a) (rev b)@
--   it generates @Cons _ _@ and @[a,b]@.
separatePat :: S.LPat 'TypeCheck -> (CPat, [S.LPat 'TypeCheck])
separatePat pat = go False (unLoc pat)
  where
    go _ (S.PVar (x, _ty)) = (CPVar x, [])
    go b (S.PCon (c, _ty) ps) =
      let (ps', subs) = gos b ps
      in (CPCon c ps', subs)

    go _ (S.PREV p)  = (CPHole, [p])
    go _ (S.PWild (x, _ty)) =
      -- (if b then CPVar x else CPBang (CPVar x), [])
      (CPVar x, [])
    -- go _ (S.PBang p) =
    --   let (p', subs) = go True (unLoc p)
    --   in (CPBang p', subs)

    gos _ []       = ([], [])
    gos b (p:ps) =
      let (p', subsP) = go b (unLoc p)
          (ps', subsPs) = gos b ps
      in (p':ps', subsP ++ subsPs)

{- |
'fillCPat' does the opposite of 'separatePat', but it generates
'C.Pat' instead of 'S.Pat'.
-}
fillCPat :: CPat -> [C.Pat Name] -> C.Pat Name
fillCPat = evalState . go
  where
    next :: State [C.Pat Name] (C.Pat Name)
    next = do
      ~(p:ps) <- get -- lazy pattern to avoid requiring MonadFail Identity.
      put ps
      return p

    go :: CPat -> State [C.Pat Name] (C.Pat Name)
    go (CPVar x)    = return (C.PVar x)
    go (CPCon c ps) = C.PCon c <$> mapM go ps
--    go (CPBang p)   = C.PBang <$> go p
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
    generateWithExp _ = withNewName $ \n ->
      return $ C.Abs n $ C.Con conTrue []
    -- generateWithExp _ = withNewName $ \n -> withNewName $ \n' ->
    --   -- FIXME: more sophisticated with-exp generation.
    --   return $ C.Bang $ C.Abs n $ C.Case (C.Var n) [ (C.PBang (C.PVar n'), C.Con conTrue []) ]

desugarAlts :: forall m. MonadDesugar m => [(S.LPat 'TypeCheck, S.Clause 'TypeCheck)] -> m [(C.Pat Name, C.Exp Name)]
desugarAlts alts = do
  let alts' = map (\(p,c) ->
                      let (cp, subs) = separatePat p
                      in (cp, subs, c)) alts
  -- grouping alts that have the same unidir patterns.
  debugPrint 3 $ text "Common patterns:" <+> ppr [ cp | (cp, _, _) <- alts' ]
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
    makeBCases ralts@((cp, firstSub, _):_) =
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
  let defs = [ (n, ty, pcs) | bs <- bss, Loc _ (S.DDef (n, ty) pcs) <- bs ]
  forM defs $ \(n, ty, pcs) -> do
    e <- desugarRHS pcs
    return (n, ty, e)

