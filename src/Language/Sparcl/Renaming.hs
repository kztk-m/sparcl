module Language.Sparcl.Renaming where

{-|
This modules performs:

- renaming of variables:
   + all top-level names are qualified by its original modules.
   + all variable names in right-hand sides are canonically qualified, if they are from other modules.
   + all local variable names are renamed by de Bruijn levels.
- resolution of fixity:
- stratifying mutual recursions.

Notice that renaming is a pure operation.

-}

import qualified Data.Map                       as M
import qualified Data.Set                       as S
import           Data.Void

import           Data.Graph                     as G
import           Data.List                      (partition)

import           Control.Monad.Except
import           Control.Monad.Reader
import           Control.Monad.State

import           Control.Arrow                  (first)

import           Language.Sparcl.Name
import           Language.Sparcl.Pass
import           Language.Sparcl.Pretty         hiding ((<$>))
import           Language.Sparcl.SrcLoc
import           Language.Sparcl.Surface.Syntax


-- | Operator Precedence Table
type OpTable = M.Map Name (Prec, Assoc)

-- | Tables for Defined Names
--
--   This is implemented as a mapping from surface names to sets of names.
--   Notice that one name can be mapped to multiple names.
--
--   (This feature is not implemented yet.)
--   A surface can be qualified. For example,
--
--   import Some.Module as F ( name )
--
--   introduces three entries:
--
--       Bare (User "name")               -> Original "Some.Module" "name" (Bare (User "name"))
--       Qual "F" (User "Name")           -> Original "Some.Module" "name" (Qual "F" (User "Name"))
--       Qual "Some.Module" (User "Name") -> Original "Some.Module" "name" (Qual "SomeModule" (User "Name"))
--
--
type NameTable = M.Map SurfaceName (S.Set (ModuleName, NameBase))

data RenamingEnv = RnEnv { rnOpTable   :: OpTable,
                           rnNameTable :: NameTable }

type Renaming a = ReaderT RenamingEnv (Either (SrcSpan,Doc)) a

runRenaming :: NameTable -> OpTable -> Renaming a -> Either (SrcSpan, Doc) a
runRenaming ntbl optbl m = runReaderT m (RnEnv optbl ntbl)

lookupFixity :: Name -> Renaming (Prec, Assoc)
lookupFixity op = do
  tbl <- asks rnOpTable
  case M.lookup op tbl of
    Just res -> return res
    Nothing  -> return (Prec 100, L)

isAssocLeft :: (Prec, Assoc) -> (Prec, Assoc) -> Bool
isAssocLeft (k1, a1) (k2, a2)
  | k1 >  k2 = True
  | k1 == k2, L <- a1, L <- a2 = True
  | otherwise = False

isAssocRight :: (Prec, Assoc) -> (Prec, Assoc) -> Bool
isAssocRight (k1, a1) (k2, a2)
  | k1 <  k2 = True
  | k1 == k2, R <- a1, R <- a2 = True
  | otherwise = False


type LocalNames = M.Map NameBase Name

type FreeVars  = S.Set Name
type BoundVars = S.Set Name

unBare :: SurfaceName -> NameBase
unBare (Bare n) = n
unBare _        = error "unBare: no Bare"

resolveImportedName :: SrcSpan -> SurfaceName -> Renaming Name
resolveImportedName _ (BuiltIn n) = return n
resolveImportedName loc n = do
  mp <- asks rnNameTable
  case fmap S.toList (M.lookup n mp) of
    Just [(mo, nm)]       ->
      return (Original mo nm n)
    Just qns@(_:_:_) ->
      let d = nest 2 $ text "Candidates are:" <$$>
                       vcat (map ppr qns)
      in throwError (loc, text "Ambiguous name" <+> ppr n <> nest 2 (line <> d) )
    _ ->
      throwError (loc, text "Unbound name: " <+> ppr n)

resolveName :: SrcSpan -> LocalNames -> SurfaceName -> Renaming Name
resolveName loc localnames n
  | Bare bn <- n, Just n' <- M.lookup bn localnames = return n'
  | otherwise =
      resolveImportedName loc n

-- De Bruijn Level
type DBLevel = Int

renameExp :: DBLevel -> LocalNames -> LExp 'Parsing -> Renaming (LExp 'Renaming, FreeVars)
renameExp level localnames (Loc loc expr) = first (Loc loc) <$> go expr
  where
--    reLoc = Loc loc
    go (Var n) = do
      n' <- resolveName loc localnames n
      return (Var n', S.singleton n')

    go (Lit l) = return (Lit l, S.empty)

    go (App e1 e2) = do
      (e1', fv1) <- renameExp level localnames e1
      (e2', fv2) <- renameExp level localnames e2
      return (App e1' e2', S.union fv1 fv2)

    go (Abs ps e) =
      renamePats level localnames S.empty ps $ \ps' level' localnames' bvP -> do
        (e', fv) <- renameExp level' localnames' e
        return (Abs ps' e', fv S.\\ bvP)

    go (Con c) = do
      c' <- resolveImportedName loc c
      return (Con c', S.empty)

    go Lift = return (Lift, S.empty)


    go (Sig e t) = do
      (e', fv) <- renameExp level localnames e
      t' <- renameTy 0 M.empty t
      return (Sig e' t', fv)


    go (Case e0 alts) = do
      (e0', fv)    <- renameExp level localnames e0
      (alts', fvs) <- unzip <$> mapM (renameAlt level localnames) alts
      return (Case e0' alts', S.unions (fv:fvs))

    go (Let decls e) =
      renameLocalDecls level localnames decls $ \decls' level' localnames' bvD fvD _ -> do
        (e', fvE) <- renameExp level' localnames' e
        return (Let decls' e', S.union fvE fvD S.\\ bvD)

    go (Parens e) = do
      (e', fvE) <- renameExp level localnames e
      return (Parens e', fvE)

    go (Op n e1 e2) = do
      n' <- resolveName loc localnames n
      (e', fv) <- rearrangeOp loc level localnames n' e1 e2
      return (unLoc e', S.insert n' fv)


    go (RCon c) = do
      e' <- RCon <$> resolveImportedName loc c
      return (e', S.empty)

    go Unlift = return (Unlift, S.empty)

    go RPin = return (RPin, S.empty)


    go (RDO as er) = do
      (as', er', fvs) <- goAs level localnames as er
      return (RDO as' er', fvs)

    goAs :: DBLevel -> LocalNames -> [(LPat 'Parsing, LExp 'Parsing)] -> LExp 'Parsing
            -> Renaming ([(LPat 'Renaming, LExp 'Renaming)] , LExp 'Renaming, FreeVars)
    goAs lv lns [] er = do
      (er', fvs) <- renameExp lv lns er
      return ([], er', fvs)
    goAs lv lns ((p,e):as) er = do
      (e', fvs1) <- renameExp lv lns e
      renamePat lv lns S.empty p $ \p' lv' lns' bvs' -> do
        (as', er', fvs2) <- goAs lv' lns' as er
        return ((p',e'):as', er', S.union fvs1 (fvs2 `S.difference` bvs'))





{-
Currently, the operators are parsed as if they were left-associative
and has the same precedence. Thus,

  x1 op1 x2 op2 x3 op3 ... opn xn+1

will be parsed as

  ((...((x1 op1 x2) op2 x3)...) opn xn+1)

Here we rearrange the operators in the right way.

Let us focus on op1 and op2 first. The association (x1 op1 x2) op2 x3
is right only if

  - op1 and op2 has the same precedence and op1 and op2 are
    left-associative, or
  - op1 has the greater precedence than op2.

Instead, it should be associated as x1 op1 (x2 op2 x3)

  - op1 and op2 has the same precedence and op1 and op2 are
    right-associative, or
  - op2 has the greater precedence than op1.

Otherwise, we need parentheses; that is, there is a syntax error.

In the former case, it is rather straight forward to proceed the

-}
rearrangeOp :: SrcSpan -> DBLevel -> LocalNames -> Name -> LExp 'Parsing -> LExp 'Parsing
               -> Renaming (LExp 'Renaming, FreeVars)
rearrangeOp loc level localnames op exp1 exp2 = do
  (exp2', fv2) <- renameExp level localnames exp2
  (exp' , fv)  <- go loc exp1 op exp2'
  return (exp', S.union fv fv2)
    where
      go l2 (Loc l1 (Op op1 e1 e2)) op2' e3' = do
        op1' <- resolveName loc localnames op1
        (k1, a1) <- lookupFixity op1'
        (k2, a2) <- lookupFixity op2'
        if | isAssocLeft (k1, a1) (k2, a2) -> do
               (e2',  fv2) <- renameExp level localnames e2
               (e12', fv1) <- go l1 e1 op1' e2'
               return (opExp l2 op2' e12' e3', S.union fv1 fv2)
           | isAssocRight (k1, a1) (k2, a2) -> do
               (e1',  fv1) <- renameExp level localnames e1
               (e23', fv2) <- go l2 e2 op2' e3'
               return (opExp l1 op1' e1' e23', S.union fv1 fv2)
           | otherwise ->
               throwError (loc,
                            nest 2 $
                            vcat [hsep [text "Unable to bracket:", text "_", ppr op1', text "_", ppr op2', text "_"],
                                  hsep [ppr op1', text "has fixity:", ppr k1, ppr a1],
                                  hsep [ppr op2', text "has fixity:", ppr k2, ppr a2]])
      go l e1 op' e2' = do
        (e1', fv1) <- renameExp level localnames e1
        return (opExp l op' e1' e2' , fv1)

      opExp l opName e1 e2 = Loc l (Op opName e1 e2)



renameAlt :: DBLevel -> LocalNames -> (LPat 'Parsing, Clause 'Parsing)
             -> Renaming ((LPat 'Renaming, Clause 'Renaming), FreeVars)
renameAlt level localnames (p, c) = do
  when (not (hasRev $ unLoc p) && hasWith c) $
    throwError (location p, text "Unidirectional patterns cannot have `with'-clause")
  renamePat level localnames S.empty p $ \p' level' localnames' bvP -> do
    (c', fv) <- renameClause level' localnames' c
    return ((p', c'), fv S.\\ bvP)


renameClause :: DBLevel -> LocalNames -> Clause 'Parsing -> Renaming (Clause 'Renaming, FreeVars)
renameClause level localnames (Clause e decls w) =
  renameLocalDecls level localnames decls $ \decls' level' localnames' fvD fvB _ -> do
     (e', fv)  <- renameExp level' localnames' e
     (w', fvw) <- case w of
             Just ew -> do
               (ew', fvw) <- renameExp level' localnames' ew
               return (Just ew', fvw)
             Nothing -> return (Nothing, S.empty)
     return (Clause e' decls' w', S.unions [fvB, fv, fvw] S.\\ fvD)

type CurrentNames = LocalNames

renameLocalDeclsWork
  :: DBLevel -> LocalNames -> CurrentNames -> Decls 'Parsing (LDecl 'Parsing)
  -> (Decls 'Renaming (LDecl 'Renaming) -> DBLevel -> LocalNames -> BoundVars -> FreeVars -> OpTable -> Renaming r)
  -> Renaming r
renameLocalDeclsWork _ _ _ (HDecls v _) _ = absurd v
renameLocalDeclsWork level' localnames currnames (Decls _ decls) cont = do
  let defs = [ (loc, unBare n, pcs)  | Loc loc (DDef n pcs) <- decls ]
  let sigs = [ (loc, unBare n, t)    | Loc loc (DSig n t) <- decls ]
  let fixs = [ (loc, unBare n, p, a) | Loc loc (DFixity n p a) <- decls ]

  let localnames' = M.union currnames localnames


  sigs' <- forM sigs $ \(loc, n, t) ->
    case M.lookup n currnames of
      Just n' -> do
        t' <- renameTy 0 M.empty t
        return (loc, n', t')
      Nothing ->
        throwError (loc, text "Signature declaration is allowed only for the current level name:" <+> ppr n)

  localOpTable <- fmap M.fromList $ forM fixs $ \(loc, n, p, a) ->
    case M.lookup n currnames of
      Just n' -> return (n', (p, a))
      Nothing ->
        throwError (loc, text "Fixity declaration is allowed only for the current level name:" <+> ppr n)


  deffvs <- forM defs $ \(loc, n, pcs) -> local (\c -> c { rnOpTable = M.union localOpTable (rnOpTable c) }) $ do
    unless (checkEqualLengths (map fst pcs)) $
      throwError (loc, text "Function" <+> ppr n <+> text "has different numbers of arguments.")

    let Just n' = M.lookup n currnames -- must succeed
    (pcs', fvs) <- fmap unzip $ forM pcs $ \(ps, c) -> do
      when (all (not . hasRev . unLoc) ps && hasWith c) $
        throwError (loc, text "Unidirectional patterns cannot have `with'-clause")
      renamePats level' localnames' S.empty ps $ \ps' level'' localnames'' fvP -> do
        (c', fvc) <- renameClause level'' localnames'' c
        return ((ps',c'), fvc S.\\ fvP)

    return (Loc loc (DDef n' pcs'), S.unions fvs)

  let defss = insertSigs sigs' $ stratify deffvs

  let fvs   = S.unions $ map snd deffvs

  cont (HDecls () defss) level' localnames' (S.fromList $ M.elems currnames) fvs localOpTable
  where
    insertSigs :: [(SrcSpan, Name, LTy 'Renaming)] -> [[LDecl 'Renaming]] -> [[LDecl 'Renaming]]
    insertSigs _sigs [] = [] -- sigs must be []
    insertSigs sigs (defs:defss) =
      let (sigs1, sigs2) = partition (`definedInDefs` defs) sigs
      in ([Loc loc (DSig n t) | (loc, n, t) <- sigs1] ++ defs) : insertSigs sigs2 defss

    definedInDefs (_, n, _) defs = n `elem` [ nm | Loc _ (DDef nm _) <- defs ]

    stratify :: [(LDecl 'Renaming, FreeVars)] -> [[LDecl 'Renaming]]
    stratify deffvs = map unSCC (G.stronglyConnComp graph)
      where
        unSCC (G.AcyclicSCC x) = [x]
        unSCC (G.CyclicSCC xs) = xs

        graph = [ (decl, n, S.toList fv) | (decl@(Loc _ (DDef n _)), fv) <- deffvs ]

    checkEqualLengths :: [[a]] -> Bool
    checkEqualLengths pss =
      let rs = map length pss
      in and $ zipWith (==) rs (tail rs)


hasRev :: Pat p -> Bool
hasRev (PVar _)    = False
hasRev (PREV _)    = True
hasRev (PCon _ ps) = any (hasRev . unLoc) ps
hasRev (PWild _)   = False

hasWith :: Clause p -> Bool
hasWith (Clause _ _ (Just _)) = True
hasWith _                     = False


renameLocalDecls :: DBLevel -> LocalNames -> Decls 'Parsing (LDecl 'Parsing)
                    -> (Decls 'Renaming (LDecl 'Renaming) -> DBLevel -> LocalNames -> BoundVars -> FreeVars -> OpTable -> Renaming r)
                    -> Renaming r
renameLocalDecls _ _ (HDecls v _) _ = absurd v
renameLocalDecls level localnames ds@(Decls _ decls) cont = do
  let defs = [ (loc, unBare n, pcs)  | Loc loc (DDef n pcs) <- decls ]
  let ns  = [ n | (_, n, _) <- defs ]
  let ns' = zipWith Alpha [level..(level + length ns - 1)] ns
  let level' = level + length ns

  -- current level names:
  -- NB: sig and fixity declarations are allowed only for current level names.
  let currnames = foldr (uncurry M.insert) M.empty $ zip ns ns'
  renameLocalDeclsWork level' localnames currnames ds cont


renameTopDecls ::
  ModuleName -> Decls 'Parsing (Loc (TopDecl 'Parsing))
  -> Renaming (Decls 'Renaming (Loc (Decl 'Renaming)),
               [Loc (Name, [Name], [Loc (CDecl 'Renaming)])],
               [Loc (Name, [Name], LTy 'Renaming)],
               BoundVars,
               OpTable)
renameTopDecls _ (HDecls v _) = absurd v
renameTopDecls currentModule (Decls _ topdecls) = do
  let decls = [ Loc loc d | Loc loc (DDecl d) <- topdecls ]
  let defs = [ (loc, unBare n, pcs)  | Loc loc (DDef n pcs) <- decls ]

  let dataDecls = [ (loc, unBare n, map unBare ns, cds) |
                    Loc loc (DData n ns cds) <- topdecls ]
  let typeDecls = [ (loc, unBare n, map unBare ns, ty) | Loc loc (DType n ns ty) <- topdecls ]

  let ns  = [ n | (_, n, _) <- defs ]

  let conName (NormalC c _)      = c
      conName (GeneralC c _ _ _) = c
  let names = ns
              ++ [ n | (_, n, _, _) <- dataDecls ]
              ++ [ unBare n | (_, _, _, cds) <- dataDecls, n <- map (conName . unLoc) cds ]
              ++ [ n | (_, n, _, _) <- typeDecls ]
  -- FIXME: check there is no overlaps in names.

  let toOrig n = Original currentModule n (Bare n)
  let nameTbl =
        M.fromListWith S.union $
          [ (Bare n, S.singleton (currentModule, n)) | n <- names ]
          ++ [ (Qual currentModule n, S.singleton (currentModule, n)) | n <- names]

  let ns' = [ toOrig n | n <- ns ]
  let level' = length ns

  let currnames = foldr (uncurry M.insert) M.empty $ zip ns ns'


  local (\rnEnv -> rnEnv { rnNameTable = M.unionWith S.union nameTbl (rnNameTable rnEnv) }) $ do
    typeDecls' <- forM typeDecls $ \(loc, n, tyns, ty) -> do
      let tyns' = zipWith Alpha [0..] tyns
      ty' <- renameTy (length tyns) (M.fromList $ zip tyns tyns') ty
      return $ Loc loc (toOrig n, tyns', ty')

    dataDecls' <- forM dataDecls $ \(loc, n, tyns, cdecls) -> do
      let tyns' = zipWith Alpha [0..] tyns
      let nm = M.fromList $ zip tyns tyns'
      cdecls' <- forM cdecls $ \case
        (Loc cloc (NormalC c tys)) -> do
          tys' <- mapM (renameTy (length tyns) nm) tys
          return $ Loc cloc (NormalC (toOrig $ unBare c) tys')
        (Loc cloc (GeneralC c xs q ts)) -> do
          let xs' = zipWith Alpha [length tyns..] $ map unBare xs
          let lv  = length tyns + length xs
          q'  <- mapM (renameTyC lv nm) q
          ts' <- mapM (\(m,t) -> do
                          m' <- renameTy lv nm m
                          t' <- renameTy lv nm t
                          return (m', t')) ts
          return $ Loc cloc $ GeneralC (toOrig $ unBare c) xs' q' ts'
      return $ Loc loc (toOrig n, tyns', cdecls')

    renameLocalDeclsWork level' M.empty currnames (Decls () decls) $ \ds' _ _ _boundVars _ opTable ->
      return (ds',
              dataDecls',
              typeDecls',
              S.fromList $ map toOrig names,
              opTable)

  -- where
  --   mapDecls f (Decls i ds)   = Decls  i (map f ds)
  --   mapDecls f (HDecls i dss) = HDecls i (map (map f) dss)


renameTyC :: DBLevel -> LocalNames -> TConstraint 'Parsing -> Renaming (TConstraint 'Renaming)
renameTyC lv nm (MSub ts1 ts2) = do
  ts1' <- mapM (renameTy lv nm) ts1
  ts2' <- mapM (renameTy lv nm) ts2
  return (MSub ts1' ts2')
renameTyC lv nm (TyEq t1 t2) = do
  t1' <- renameTy lv nm t1
  t2' <- renameTy lv nm t2
  return (TyEq t1' t2')

renameTy :: DBLevel -> LocalNames -> LTy 'Parsing -> Renaming (LTy 'Renaming)
renameTy level localnames lty = go level localnames lty (\lty' _ _ -> return lty')
  where
    go lv nm (Loc loc ty) k = go' lv nm loc ty $ \ty' lv' nm' -> k (Loc loc ty') lv' nm'

    gos lv nm [] k = k [] lv nm
    gos lv nm (t:ts) k =
      go lv nm t $ \t' lv' nm' ->
                     gos lv' nm' ts $ \ts' lv'' nm'' ->
                                        k (t':ts') lv'' nm''

    go' lv nm loc (TVar x) k = do
      let bn = unBare x
      case M.lookup bn nm of
        Just n  -> k (TVar n) lv nm
        Nothing -> throwError (loc, text "Unbound type variable:" <+> ppr x)

    go' lv nm loc (TCon c ts) k = do
      c' <- resolveImportedName loc c
      gos lv nm ts $ \ts' lv' nm' ->
        k (TCon c' ts') lv' nm'

    go' lv nm _loc (TForall x t) k = do
      let bn = unBare x
      let x'  = Alpha lv bn
      let nm' = M.insert bn x' nm
      go (lv+1) nm' t $ \t' lv'' nm'' -> k (TForall x' t') lv'' nm''

    go' lv nm _loc (TMult m) k = k (TMult m) lv nm
    go' lv nm _loc (TQual cs t) k =
      goCs lv nm cs $ \cs' lv' nm' ->
        go lv' nm' t $ \t' lv'' nm'' -> k (TQual cs' t') lv'' nm''

    goCs lv nm [] k = k [] lv nm
    goCs lv nm (c:cs) k =
      goC lv nm c $ \c' lv' nm' ->
        goCs lv' nm' cs $ \cs' lv'' nm'' -> k (c':cs') lv'' nm''

    goC lv nm (MSub ts1 ts2) k =
      gos lv  nm  ts1 $ \ts1' lv1 nm1 ->
      gos lv1 nm1 ts2 $ \ts2' lv2 nm2 ->
      k (MSub ts1' ts2') lv2 nm2

    goC lv nm (TyEq t1 t2) k =
      go lv  nm  t1 $ \t1' lv1 nm1 ->
      go lv1 nm1 t2 $ \t2' lv2 nm2 ->
      k (TyEq t1' t2') lv2 nm2


{- |
'renamePats' renames variable as DFS manner, but renaming of patterns under REV is done
after renaming of other part. For example,

   A x (rev y) z  -> A 0 (rev 2) 1

-}

type ToBeFilled a = State [LPat 'Renaming] a

renamePats1 :: DBLevel -> LocalNames -> BoundVars -> [LPat 'Parsing]
               -> (ToBeFilled [LPat 'Renaming] -> [LPat 'Parsing] ->
                   DBLevel -> LocalNames -> BoundVars -> Renaming r) -> Renaming r
renamePats1 level localnames boundVars z cont =
  case z of
    []   -> cont (pure []) [] level localnames boundVars
    p:ps ->
      renamePat1  level  localnames  boundVars  p  $ \p'  qp  level'  localnames'  boundVars' ->
      renamePats1 level' localnames' boundVars' ps $ \ps' qps level'' localnames'' boundVars'' ->
      cont ((:) <$> p' <*> ps') (qp ++ qps) level'' localnames'' boundVars''


renamePat1 :: DBLevel -> LocalNames -> BoundVars -> LPat 'Parsing
              -> (ToBeFilled (LPat 'Renaming) -> [LPat 'Parsing] ->
                  DBLevel -> LocalNames -> BoundVars -> Renaming r) -> Renaming r

renamePat1 level localnames boundVars (Loc loc pat) cont =
  go pat $ \p' qs level' localnames' boundVars' -> cont (Loc loc <$> p') qs level' localnames' boundVars'
  where
    go (PVar x) k =
      let bn = unBare x
          n' = Alpha level bn
          nm' = M.insert bn n' localnames
      in k (pure $ PVar n') [] (level + 1) nm' (S.insert n' boundVars)

    go (PWild _) k =
      let n'  = Alpha level (User "_")
      in k (pure $ PWild n') [] (level + 1) localnames boundVars

    go (PCon c ps) k = do
      c' <- resolveImportedName loc c
      renamePats1 level localnames boundVars ps $ \ps' queue level' localnames' boundVars' ->
        k (PCon c' <$> ps') queue level' localnames' boundVars'
    -- go (PBang p) k =
    --   renamePat1 level localnames boundVars p $ \p' queue level' localnames' boundVars' ->
    --     k (PBang <$> p') queue level' localnames' boundVars'
    go (PREV p) k =
      k (PREV <$> fillLater) [p] level localnames boundVars

    fillLater = do
      n:ns <- get
      put ns
      return n

renamePats :: DBLevel -> LocalNames -> BoundVars -> [LPat 'Parsing]
              -> ([LPat 'Renaming] -> DBLevel -> LocalNames -> BoundVars -> Renaming r) -> Renaming r
renamePats level localnames boundVars [] k =
  k [] level localnames boundVars
renamePats level localnames boundVars ps k =
  renamePats1 level  localnames  boundVars  ps $ \ps' qs level1 localnames1 boundVars1 ->
  renamePats  level1 localnames1 boundVars1 qs $ \qs' level2 localnames2 boundVars2 ->
  k (evalState ps' qs') level2 localnames2 boundVars2

-- renamePats level localnames bvs [] k = k [] level localnames bvs
-- renamePats level localnames bvs (p:ps) k =
--   renamePat level localnames bvs p $ \p' lv' nm' bvs' ->
--    renamePats lv' nm' bvs' ps $ \ps' lv'' nm'' bvs''  -> k (p' : ps') lv'' nm'' bvs''

renamePat :: DBLevel -> LocalNames -> BoundVars -> LPat 'Parsing
             -> (LPat 'Renaming -> DBLevel -> LocalNames -> BoundVars -> Renaming r) -> Renaming r
renamePat level localnames boundVars p k =
  renamePat1 level  localnames  boundVars  p  $ \p' qs level1 localnames1 boundVars1 ->
  renamePats level1 localnames1 boundVars1 qs $ \qs'   level2 localnames2 boundVars2 ->
  k (evalState p' qs') level2 localnames2 boundVars2
-- renamePat level localnames boundVars (Loc loc pat) cont = go pat $ \p' lv nm bvs -> cont (Loc loc p') lv nm bvs
--   where
--     go (PVar x) k =
--       let bn = unBare x
--           n' = Alpha level bn
--           nm' = M.insert bn n' localnames
--       in k (PVar n') (level + 1) nm' (S.insert n' boundVars)
--     go (PCon c ps) k = do
--       c' <- resolveImportedName loc c
--       renamePats level localnames boundVars ps $ \ps' level' localnames' bvs' ->
--         k (PCon c' ps') level' localnames' bvs'
--     go (PBang p) k =
--       renamePat level localnames boundVars p $ \p' level' localnames' bvs' ->
--         k (PBang p') level' localnames' bvs'
--     go (PREV p) k =
--       renamePat level localnames boundVars p $ \p' level' localnames' bvs' ->
--         k (PREV p') level' localnames' bvs'

--     go (PWild _) k = do
--       let n'  = Alpha level (User "_")
--       k (PWild n') (level + 1) localnames boundVars

