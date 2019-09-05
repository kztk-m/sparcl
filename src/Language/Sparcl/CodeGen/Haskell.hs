{-# LANGUAGE NoMonomorphismRestriction #-}

module Language.Sparcl.CodeGen.Haskell where

import           Data.Char                      (isLower, isNumber, isUpper,
                                                 ord)

import           Control.Monad.Cont             hiding (lift)
import           Control.Monad.State            hiding (lift)

import           Data.Functor.Identity

import qualified System.FilePath                as FP

import qualified Control.Monad.Trans            as T (lift)

import           Language.Sparcl.Literal
import           Language.Sparcl.Name

import           Language.Sparcl.Core.Syntax    as C
import           Language.Sparcl.Pretty         hiding (list, (<$>))
import           Language.Sparcl.Typing.Type

-- FIXME: These dependencies should be removed in future
import           Language.Sparcl.Exception
import           Language.Sparcl.Pass
import           Language.Sparcl.Surface.Syntax as S (Export, Import (..))

import           Prelude                        hiding (abs)

class NameGen m n where
  newName :: m n

class IsName n where
  fromName :: Name -> n

instance IsName Name where
  fromName = id

class HsName n where
  rtName :: String -> n
  hsName :: String -> n



class (Monad m, IsName n, HsName n, MiniHaskellPat n p,
       MiniHaskellType n t, MiniHaskellConstraint n t c) =>
      MiniHaskellExp m n p e d s t c | m -> e, m -> d, m -> s, m -> n, m -> p, m -> t, m -> c  where
  var :: n -> m e
  lit :: Literal -> m e
  app :: e -> e -> m e
  abs :: n -> e -> m e

  con :: n -> [e] -> m e
  case_ :: e -> [(p, e)] -> m e

  let_ :: [d] -> e -> m e

  vald :: n -> e -> m d
  sigd :: n -> t -> m d
  datad :: n -> [n] -> [(n,[n],[c],[t])] -> m d
  typed :: n -> [n] -> t -> m d

  list  :: [e] -> m e
  tuple :: [e] -> m e

  -- lift   :: e -> e -> m e
  -- unlift :: e -> m e

  -- rcase :: e -> [(e,e, e,e)] -> m e
  -- rpin  :: e -> e -> m e
  -- rpair :: e -> e -> m e
  -- runit :: m e

  -- rununit :: e -> e -> m e
  -- runpair :: e -> e -> m e

  -- just :: e -> m e -- Just in Haskell
  -- nothing :: m e   -- Nothing in Haskell

  do_     :: [s] -> m e
  lets    :: [d] -> m s
  binds   :: n -> e -> m s
  nobinds :: e -> m s

class IsName n => MiniHaskellPat n p | p -> n where
  pvar :: n -> p
  pcon :: n -> [p] -> p
  ptuple :: [p] -> p

class (IsName n, HsName n) => MiniHaskellType n t | t -> n where
  tyvar  :: n -> t
  tycon  :: n -> [t] -> t
  tyfun  :: t -> t -> t
  tytuple  :: [t] -> t
  tylist   :: t -> t
  tyforall :: [n] -> t -> t

class (MiniHaskellType n t) => MiniHaskellConstraint n t c | c -> n, c -> t  where
  tyeq :: t -> t -> c

-- Tentatively disabled modulePrefix

-- modulePrefix :: String
-- modulePrefix = "Sparcl"

runtimePrefix :: String
runtimePrefix = "Language.Sparcl.Runtime."

baseSubstitute :: String
baseSubstitute = "Language.Sparcl.Base"

targetFilePath :: ModuleName -> String
targetFilePath = go id . genModuleName
  where
    go k [] = k "" FP.<.> "hs"
    go k (c:cs)
      | c == '.'  = k "" FP.</> go id cs
      | otherwise = go (k . (c:)) cs

genModuleName :: ModuleName -> String
genModuleName m@(ModuleName n)
  | m == baseModule = baseSubstitute
  | otherwise       = n

rhsName :: Name -> String
rhsName nn@(Original m n _)
  | nn == conTrue  = "Prelude.True"
  | nn == conFalse = "Prelude.False"
  | otherwise =
    let s = unUser n
    in parensIfs (isOp s) $ genModuleName m ++ "." ++ encNameG s

rhsName (Alpha i n)      = "_a" ++ encNameL (unUser n) ++ "_" ++ show i
rhsName (Local n)        = "_l" ++ encNameL (unUser n)
rhsName (Generated n p)  = "_g" ++ phaseStr p ++ show n

parensIfs :: Bool -> String -> String
parensIfs True s  = "(" ++ s ++ ")"
parensIfs False s = s


lhsName :: Name -> String
lhsName (Original _ n _) =
  let s = unUser n
  in parensIfs (isOp s) $ encNameG s
lhsName (Alpha i n)      = "_a" ++ encNameL (unUser n) ++ "_" ++ show i
lhsName (Local n)        = "_l" ++ encNameL (unUser n)
lhsName (Generated n p)  = "_g" ++ phaseStr p ++ show n

phaseStr :: Phase -> String
phaseStr Desugaring = "d"
phaseStr CodeGen    = "c"

encNameL :: String -> String
encNameL = go
  where
    go [] = []
    go (c:cs)
      | c == 'z' = "zz" ++ go cs
      | c == '_' = "z_" ++ go cs
      | isLower c || isUpper c || isNumber c = c:go cs
      | otherwise = "z" ++ show (ord c) ++ go cs

isOp :: String -> Bool
isOp s
  | h:_ <- s, isLower h = False
  | h:_ <- s, isUpper h = False
  | otherwise           = True

encNameG :: String -> String
encNameG n = n

unUser :: NameBase -> String
unUser (User n) = n
unUser _        = error "Expected user-defined name."


data GName = RtName String
           | HsName String
           | FromName Name

instance IsName GName where
  fromName = FromName

instance HsName GName where
  hsName = HsName
  rtName = RtName

lhsNameG :: GName -> String
lhsNameG (FromName n) = lhsName n
lhsNameG _            = error "Cannot happen."

rhsNameG :: GName -> String
rhsNameG (FromName n) = rhsName n
rhsNameG (HsName s)   = s
rhsNameG (RtName s)   = runtimePrefix ++ s


instance MiniHaskellPat GName (Precedence -> Doc) where
  pvar n _ = text (lhsNameG n)
  pcon n ps prec =
    parensIf (prec > 0) $ hsep (text (rhsNameG n) : map (\p -> p 1) ps)
  ptuple ps _ =
    parens (hsep $ punctuate comma $ map (\p -> p 0) ps)

type TextGen = Precedence -> Doc

instance MiniHaskellExp Identity GName
                        (Precedence -> Doc) (Precedence -> Doc) Doc Doc (Precedence -> Doc) Doc where

  var n = Identity $ \_ -> text (rhsNameG n)
  lit n = Identity $ \_ -> text (prettyShow n)

  abs n x = Identity $ \prec ->
    parensIf (prec > 0) $ nest 2 $
      text "\\" <> text (lhsNameG n) <+> text "->" <+> x 0

  app e1 e2 = Identity $ \prec ->
    parensIf (prec > 9) $ e1 9 <+> e2 10

  con n [] = Identity $ \_ -> text (rhsNameG n)
  con n es = Identity $ \prec ->
    parensIf (prec > 9) $ text (rhsNameG n) <+> hsep (map ($ 10) es)


  case_ e0 pes = Identity $ \prec ->
    parensIf (prec > 0) $
      text "case" <+> e0 1 <+> text "of" <>
      nest 2 (line <>
             align (hsblock $ map (\(p,e) -> p 0 <+> text "->" <> nest 2 (line <> e 0)) pes))

  let_ ds e = Identity $ \prec ->
    parensIf (prec > 0) $
    text "let" <+> align (hsblock ds) <>
    line <> text "in" <+> align (e 0)

  -- bind nes = Identity $ \isTopLevel ->
  --   (if isTopLevel then vcat else hsblock) $ map (\(n,e) -> align $ nest 2 $ text (lhsNameG n) <+> text "=" </> e 0) nes
  --   where

  vald n e = Identity $ nest 2 $ text (lhsNameG n) <+> text "=" </> e 0
  sigd n t = Identity $ nest 2 $ text (lhsNameG n) <+> text "::" </> t 0

  datad n tvs cs = Identity $
    text "data" <+> text (lhsNameG n) <+> hsep (map (text . lhsNameG) tvs)
    <> nest 2 ((line <>) . vcat $ zipWith (<+>) (text "=":repeat (text "|")) $
              flip map cs $ \(c, ns, q, ts) ->
                  let fd = if null ns then empty
                           else text "forall" <+> hsep (map (text . lhsNameG) ns) <> text "."
                      cd = if null q then empty
                           else parens (hsep $ punctuate comma q) <+> text "=> "
                  in fd <> cd <> text (lhsNameG c) <+> hsep (map ($ 10) ts))

  typed n tvs t = Identity $
    text "type" <+> text (lhsNameG n) <+> hsep (map (text . lhsNameG) tvs) <+> text "=" <+> t 0

  list es = Identity $ \_ ->
    brackets $ hsep $ punctuate comma $ map ($ 0) es

  tuple es = Identity $ \_ ->
    parens $ hsep $ punctuate comma $ map ($ 0) es

  do_ [s] = Identity $ \prec -> parensIf (prec > 0) s  -- it must be the case that s is nobind expression.
  do_ ss = Identity $ \prec ->
    parensIf (prec > 0) $ nest 2 $ text "do" <>
      line <> hsblock ss

  lets d = Identity $
    text "let" <+> align (hsblock d)

  binds n e = Identity $
    text (lhsNameG n) <+> text "<-" <+> e 0

  nobinds e = Identity $ e 0


instance MiniHaskellType GName (Precedence -> Doc) where
  tyvar x _ = text (lhsNameG x)

  tycon n [] _    = text (rhsNameG n)
  tycon n ts prec = parensIf (prec > 2) $
                    text (rhsNameG n) <+> hsep (map ($ 3) ts)
  tytuple ts _ = parens $ hsep $ punctuate comma (map ($ 0) ts)
  tylist  t  _ = brackets $ t 0
  tyfun t1 t2 prec = parensIf (prec > 1) $
                     t1 2 <+> text "->" <+> t2 1
  tyforall tvs t prec = parensIf (prec > 0) $
                        text "forall" <+> hsep (map (text . lhsNameG) tvs) <> text "."
                        <+> t 0

instance MiniHaskellConstraint GName (Precedence -> Doc) Doc where
  tyeq t1 t2 = t1 0 <+> text "~" <+> t2 0

hsblock :: [Doc] -> Doc
hsblock []  = text "{}"
hsblock [d] = d
hsblock ds  = vcat (zipWith (<+>) (text "{":repeat (text ";")) ds) <> text "}"


toDocExp :: (forall m n p e d s t c. MiniHaskellExp m n p e d s t c => m e) -> Doc
toDocExp (m :: Identity (Precedence -> Doc)) = runIdentity m 0

toDocDec :: (forall m n p e d s t c. MiniHaskellExp m n p e d s t c => m [d]) -> Doc
toDocDec (m :: Identity [Doc]) = vcat $ runIdentity m

toDocTop :: ModuleName ->
            Maybe [Export 'Parsing] -> -- ^ export list
            [Import 'Parsing] -> -- ^ import list
            [C.DDecl Name] -> -- ^ data type declaration
            [C.TDecl Name] -> -- ^ type declaration
            C.Bind Name -> -- ^ bindings
            Doc
toDocTop mn exports imports ddecls tdecls defs =
  vcat [langPragmas,
        text "module" <+> text (genModuleName mn) <+>
         (case exports of
            Nothing -> text ""
            Just vs -> parens (align $ vcat $ punctuate comma $ map (ppr . unLoc) vs))
         <+> text "where",
        renderImports imports,
        text "import qualified Language.Sparcl.Runtime",
        text "import qualified" <+> text baseSubstitute,
        text "",
        -- renderDDecls ddecls,
        -- renderTDecls tdecls,
        toDocDec $ runGen $ genTopBind ddecls tdecls defs ]
  where
    langPragmas = vcat [ text "{-# OPTIONS_GHC -Wno-missing-signatures #-}"
                       , text "{-# OPTIONS_GHC -Wno-overlapping-patterns #-}"
                       , text "{-# OPTIONS_GHC -Wno-incomplete-patterns #-}" ]

    renderImports [] = text ""
    renderImports (Import m is:imps) =
      text "import" <+> text (genModuleName m) <+>
      (case is of
          Nothing -> text ""
          Just ns -> parens (align $ vcat $ punctuate comma $ map (ppr . unLoc) ns))
      <> line <> renderImports imps


    -- renderDDecls [] = text ""
    -- renderDDecls (DDecl n tvs cs:ds) =
    --   text "data" <+> text (lhsName n) <+> hsep (map ppr tvs) <>
    --   nest 2 ((line <>) . vcat $ zipWith (<+>) (text "=":repeat (text "|")) $
    --           flip map cs $ \(c,ts) ->
    --              text (lhsName c) <+> hsep (map (renderTyAsHs 10) ts))
    --   <> line <> renderDDecls ds


    -- renderTDecls [] = text ""
    -- renderTDecls (TDecl n tys ty:ds) =
    --   text "type" <+> text (lhsName n) <+> hsep (map ppr tys) <+> text "=" <+> renderTyAsHs 0 ty
    --   <> line <> renderTDecls ds


    -- renderTyAsHs = go
    --   where
    --     go :: Precedence -> Ty -> Doc
    --     go prec (TyCon c tys)
    --       | c == nameTyLArr, [t1,t2] <- tys =
    --           parensIf (prec > 4) $
    --           go 5 t1 <+> text "->" <+> go 4 t2
    --       | c == nameTyList, [t1] <- tys =
    --           brackets (go 1 t1)
    --       | Just _ <- checkNameTyTuple c =
    --           parens $ hsep $ punctuate comma $ map (go 0) tys
    --       | c == nameTyRev, [t1] <- tys =
    --           parensIf (prec > 9) $
    --           text "Rev" <+> go 10 t1
    --       | c == nameTyBang, [t1] <- tys =
    --           go prec t1
    --       | c == nameTyInt || c == nameTyDouble || c == nameTyChar || c == nameTyBool =
    --           ppr c
    --       | otherwise = parensIf (prec > 9) $
    --       text (rhsName c) <+> hsep (map (go 10) tys)
    --     go _    (TyVar tv)    = ppr tv
    --     go prec (TyForAll tvs ty) = parensIf (prec > 0) $
    --       text "forall" <+> hsep (map ppr tvs) <> text "." <+> go 0 ty
    --     go prec (TySyn ty _)  = go prec ty
    --     go _    (TyMetaV _)   = error "Cannot happen."


genTopBind :: MiniHaskellExp m n p e d s t c =>
              [C.DDecl Name] -> -- ^ data type declaration
              [C.TDecl Name] -> -- ^ type declaration
              C.Bind Name -> Gen m [d]
genTopBind ddecls tdecls topbind = do
  d1 <- T.lift $ sequence [ datad (fromName n) (map genTyVar tvs)
                            [ (fromName c, map fromName ns, genC q, map genTy ts) | (c,ns,q,ts) <- cs ]
                          | DDecl n tvs cs <- ddecls ]
  d2 <- T.lift $ sequence [ typed (fromName n) (map genTyVar tvs) (genTy t)
                          | TDecl n tvs t <- tdecls ]
  d3 <- genBind topbind
  return $ d1 ++ d2 ++ d3

genTyVar :: IsName n => TyVar -> n
genTyVar (BoundTv n) = fromName n
genTyVar _           = error "Cannot happen."

genC :: MiniHaskellConstraint n t c => [TyConstraint] -> [c]
genC [] = []
genC (MSub _ _:cs) = genC cs
genC (TyEq t1 t2:cs) =
  tyeq (genTy t1) (genTy t2) : genC cs

genTy :: MiniHaskellType n t => Ty -> t
genTy (TyCon c tys)
  | c == nameTyArr, [_,t1,t2] <- tys =
      tyfun (genTy t1) (tycon (rtName "R") [genTy t2])
  | c == nameTyList, [t1] <- tys =
      tylist (genTy t1)
  | c == nameTyRev, [t1] <- tys =
      tycon (rtName "Rev") [genTy t1]
  | Just _ <- checkNameTyTuple c =
      tytuple (map genTy tys)
  | c == nameTyBang, [t1] <- tys =
      genTy t1
  | c == nameTyInt =
      tycon (hsName "Prelude.Int") []
  | c == nameTyDouble =
      tycon (hsName "Prelude.Double") []
  | c == nameTyChar =
      tycon (hsName "Prelude.Char") []
  | c == nameTyBool =
      tycon (hsName "Prelude.Bool") []
  | otherwise =
      tycon (fromName c) $ map genTy tys
genTy (TyForAll tvs (TyQual _ ty)) =
  tyforall (map genTyVar tvs) (genTy ty)
genTy (TyVar tv)   = tyvar (genTyVar tv)
genTy (TySyn ty _) = genTy ty
genTy (TyMetaV _)  = tytuple [] -- defaulting to unit
genTy (TyMult m)   = cannotHappen (text "Multiplicity" <+> ppr m <+> text "appear where a type is expected.")


type Gen = StateT Int
type GenExp m s e = Cont (m [s]) e

runGen :: Monad m => Gen m e -> m e
runGen m = evalStateT m 0

-- genBind :: MiniHaskellExp m n p e d s => C.Bind Name -> Gen m d
-- genBind ds = do
--   ds' <- mapM (\(x,e) -> do
--                   e' <- genExp e
--                   return (fromName x, e')) ds
--   bind ds'

genBind :: MiniHaskellExp m n p e d s t c => C.Bind Name -> Gen m [d]
genBind ds = do
  ds' <- forM ds $ \(x,ty,e) -> do
    e'  <- genExp e
    e'' <- T.lift $ mkApp (var $ rtName "runRevUnsafe") (do_ =<< addReturn e')
    return (fromName x, genTy ty, e'')
  T.lift $ concat <$> mapM (\(n,t,e) -> do
                               d1 <- sigd n t
                               d2 <- vald n e
                               return [d1,d2]) ds'



instance (IsName n, Monad m) => NameGen (StateT Int m) n where
  newName = do
    i <- get
    put $! i + 1
    return $ fromName $ Generated i CodeGen

mkApp :: MiniHaskellExp m n p e d s t c => m e -> m e -> m e
mkApp e1 e2 = do
  f <- e1
  x <- e2
  app f x

addReturn :: MiniHaskellExp m n p e d s t c => GenExp m s e -> m [s]
addReturn e =
  runCont e $ \v -> do
    s <- nobinds =<< var (hsName "Prelude.return") `mkApp` return v
    return [s]

lift :: MiniHaskellExp m n p e d s t c => GenExp m s e -> GenExp m s e -> Gen m (GenExp m s e)
lift e1 e2 = do
  r <- newName
  return $ cont $ \k ->
    runCont e1 $ \v1 ->
    runCont e2 $ \v2 -> do
       e <- var (rtName "liftRev") `mkApp` return v1 `mkApp` return v2
       liftM2 (:) (binds r e) (k =<< var r)

unlift :: MiniHaskellExp m n p e d s t c => GenExp m s e -> Gen m (GenExp m s e)
unlift e = do
  r <- newName
  return $ cont $ \k ->
    runCont e $ \v ->
       liftM2 (:) (binds r =<< var (rtName "unliftRev") `mkApp` return v) (k =<< var r)

runit :: MiniHaskellExp m n p e d s t c => Gen m (GenExp m s e)
runit = do
  r <- newName
  return $ cont $ \k ->
    liftM2 (:) (binds r =<< var (rtName "unitRev")) (k =<< var r)

rpair :: MiniHaskellExp m n p e d s t c => GenExp m s e -> GenExp m s e -> Gen m (GenExp m s e)
rpair e1 e2 = do
  r <- newName
  return $ cont $ \k ->
    runCont e1 $ \d1 ->
    runCont e2 $ \d2 -> do
      e <- var (rtName "pairRev") `mkApp` return d1 `mkApp` return d2
      vr <- var r
      liftM2 (:) (binds r e) (k vr)

rpin :: MiniHaskellExp m n p e d s t c => GenExp m s e -> GenExp m s e -> Gen m (GenExp m s e)
rpin e1 e2 = do
  r <- newName
  return $ cont $ \k ->
    runCont e1 $ \d1 ->
    runCont e2 $ \d2 -> do
      e <- var (rtName "pinRev") `mkApp` return d1 `mkApp` return d2
      vr <- var r
      liftM2 (:) (binds r e) (k vr)

rununit :: MiniHaskellExp m n p e d s t c => GenExp m s e -> GenExp m s e -> Gen m (GenExp m s e)
rununit e1 e2 = do
  r <- newName
  return $ cont $ \k ->
    runCont e1 $ \v1 -> do
     let e2' = do_ =<< runCont e2 (\v2 -> do
                                      s <- nobinds =<< mkApp (var $ hsName "Prelude.return") (return v2)
                                      return [s])
     e <- var (rtName "ununitRev") `mkApp` return v1 `mkApp` e2'
     liftM2 (:) (binds r e) (k =<< var r)


runpair :: MiniHaskellExp m n p e d s t c => GenExp m s e -> GenExp m s e -> Gen m (GenExp m s e)
runpair e1 e2 = do
  r <- newName
  x <- newName
  y <- newName

  f <- newName
  return $ cont $ \k ->
    runCont e1 $ \v1 -> do
    let e2' = abs x =<< abs y =<< do_ =<< runCont e2 (\v2 -> do
                                                         s1 <- binds f =<< mkApp (return v2) (var x)
                                                         s2 <- nobinds =<< mkApp (var f) (var y)
                                                         return [s1,s2])
    e <- var (rtName "unpairRev") `mkApp` return v1 `mkApp` e2'
    liftM2 (:) (binds r e) (k =<< var r)

rcase :: forall m n p e d s t c.
         MiniHaskellExp m n p e d s t c =>
         GenExp m s e -> [(GenExp m s e, GenExp m s e, GenExp m s e, GenExp m s e)] -> Gen m (GenExp m s e)
rcase e0 _e4s = do
  r <- newName
  i <- newName
  return $ cont $ \k ->
    runCont e0 $ \v0 -> go r i v0 [] _e4s k
  where
    go :: n -> n -> e -> [e] -> [(GenExp m s e, GenExp m s e, GenExp m s e, GenExp m s e)] -> (e -> m [s]) -> m [s]
    go r _ v0 es [] k = do
      s   <- binds r =<< var (rtName "caseRev") `mkApp` return v0 `mkApp` list (reverse es)
      (s:) <$> (k =<< var r)
    go r i v0 es ((e1,e2,e3,e4):e4s) k =
      runCont e1 $ \v1 ->
      runCont e2 $ \v2 ->
      runCont e4 $ \v4 -> do
      -- We want to delay the computation of e3 : M (a -> M b), so we guard it by lambda.
      v3 <- abs i =<< do_ =<< runCont e3 (\v3 -> do
                                     s <- nobinds =<< return v3 `mkApp` var i
                                     return [s])
      vbr <- con (rtName "Branch") [v1, v2, v3, v4]
      go r i v0 (vbr:es) e4s k


mkCon :: MiniHaskellExp m n p e d s t c => Name -> [e] -> m e
mkCon n es
  | Just _ <- checkNameTuple n = tuple es
  | otherwise                  = con (fromName n) es

lets_ :: MiniHaskellExp m n p e d s t c => n -> e -> m s
lets_ r e = lets =<< fmap (:[]) (vald r e)

genExp :: MiniHaskellExp m n p e d s t c => C.Exp Name -> Gen m (GenExp m s e)
genExp (C.Var x) = return $ cont $ \k ->
  k =<< var (fromName x)
genExp (C.Lit l) = return $ cont $ \k ->
  k =<< lit l
genExp (C.App e1 e2) = do
  e1' <- genExp e1
  e2' <- genExp e2
  r   <- newName
  return $ cont $ \k ->
    runCont e1' $ \v1 ->
    runCont e2' $ \v2 ->
    liftM2 (:) (binds r =<< app v1 v2) (k =<< var r)
genExp (C.Abs x e) = do
  r  <- newName
  e' <- genExp e
  return $ cont $ \k ->
    liftM2 (:) (lets_ r =<< abs (fromName x) =<< do_ =<< addReturn e') (k =<< var r)

--  abs (fromName x) =<< genExp e
genExp (C.Con n es) = do
  es' <- mapM genExp es
  return $ cont $ \k -> go id es' k
  where
    go vs [] k = k =<< mkCon n (vs [])
    go vs (e:es') k =
      runCont e $ \v ->
      go (vs . (v:)) es' k

  -- xs <- mapM genExp es
  -- con (fromName n) xs
genExp (C.Case e0 pes) = do
  r <- newName
  e0' <- genExp e0
  pes' <- mapM (\(p,e) -> do
                   e' <- genExp e
                   return (genPat p, e')) pes
  return $ cont $ \k ->
    runCont e0' $ \v0 -> do
      pes'' <- mapM (\(p,e) -> do
                        e' <- do_ =<< addReturn e
                        return (p,e')) pes'
      liftM2 (:) (binds r =<< case_ v0 pes'') (k =<< var r)

genExp (C.Let ds e1) = do
  ds' <- genBind ds
  e1' <- genExp e1
  return $ cont $ \k -> do
    s1 <- lets ds'
    s2 <- runCont e1' k
    return (s1:s2)

genExp (C.Lift e1 e2) = do
  e1' <- genExp e1
  e2' <- genExp e2
  lift e1' e2'
genExp (C.Unlift e) = do
  e' <- genExp e
  unlift e'

genExp (C.RPin e1 e2) = do
  e1' <- genExp e1
  e2' <- genExp e2
  rpin e1' e2'

genExp (C.RCon n es) = do
  r  <- newName
  rr <- newName
  x  <- newName
  zs <- mapM (const newName) [1..len]
  es' <- mapM genExp es
  epair' <- pairsToRightR es'
  return $ cont $ \k ->
    runCont epair' $ \vpair -> do
      fwd <- abs x =<< (do vx <- var x
                           body <- var (hsName "Prelude.return") `mkApp` (mkCon n =<< mapM var zs)
                           case_ vx [ (pairsToRightP (map pvar zs), body) ])
      bwd <- abs x =<< (do vx <- var x
                           body <- var (hsName "Prelude.return") `mkApp` (pairsToRight =<< mapM var zs)
                           case_ vx [ (mkConP n (map pvar zs), body) ])
      e <- var (rtName "liftRev") `mkApp` return fwd `mkApp` return bwd
      liftM2 (:) (binds r e) $
        liftM2 (:) (binds rr =<< var r `mkApp` return vpair) (k =<< var rr)
  where
    len = length es

-- do
--   let len = length es
--   x <- newName
--   zs <- mapM (const newName) [1..len]
--   es' <- mapM genExp es
--   e'  <- pairsToRightR es'
--   let n' = fromName n
--   vx <- var x
--   fwd <- do
--     body <- con n' =<< mapM var zs
--     abs x =<< case_ vx [ (pairsToRightP (map pvar zs), body) ]

--   bwd <- do
--     body <- pairsToRight =<< mapM var zs
--     abs x =<< case_ vx [ (pcon n' (map pvar zs), body) ]

--   f <- lift fwd bwd
--   app f e'

genExp (C.RCase e0 alts) = do
  e0' <- genExp e0
  alts' <- mapM genRAlts alts
  rcase e0' alts'


genRAlts :: forall m n p e d s t c.
            MiniHaskellExp m n p e d s t c => (Pat Name, Exp Name, Exp Name) -> Gen m (GenExp m s e, GenExp m s e, GenExp m s e, GenExp m s e)
genRAlts (pat, bexp, wexp) = do
  x <- newName
  y <- newName
  let fvP = map fromName $ freeVarsP pat
  let pat' = genPat pat

  let f :: GenExp m s e
      f = cont $ \k -> do
        body1 <- var (hsName "Prelude.return") `mkApp` (just =<< pairsToRight =<< mapM var fvP)
        body2 <- var (hsName "Prelude.return") `mkApp` nothing
        vx <- var x
        k =<< abs x =<< case_ vx [ (pat', body1), (pvar y, body2) ]
  let g :: GenExp m s e
      g = cont $ \k -> do
        body1 <- var (hsName "Prelude.return") `mkApp` (just =<< genExpFromPat pat)
        vx <- var x
        k =<< abs x =<< case_ vx [ (pairsToRightP (map pvar fvP), body1)]

  wexp' <- genExp wexp

  bexp' <- do
    b <- mkUnpairs x fvP =<< genExp bexp
    return $ cont $ \k -> k =<< abs x =<< do_ =<< addReturn b

  return (f, g, bexp', wexp')
  where
    nothing :: m e
    nothing = con (hsName "Prelude.Nothing") []

    just :: e -> m e
    just e = con (hsName "Prelude.Just") [e]

    mkUnpairs :: n -> [n] -> GenExp m s e -> Gen m (GenExp m s e)
    mkUnpairs x [] body = do
      let vx = cont $ \k -> k =<< var x
      rununit vx body
    mkUnpairs x [y] body = do
      r <- newName
      return $ cont $ \k -> do
        f <- abs y =<< do_ =<< addReturn body
        z <- var x
        liftM2 (:) (binds r =<< app f z) (k =<< var r)
    mkUnpairs x (y:ys) body = do
      let vx = cont $ \k -> k =<< var x
      r <- newName
      rr <- newName
      res <- mkUnpairs r ys body
      runpair vx (cont $ \k ->
                         liftM2 (:) (lets_ rr =<< abs y =<< mkApp (var $ hsName "Prelude.return")
                                                                  (abs r =<< do_ =<< addReturn res))
                                    (k =<< var rr))


-- just :: MiniHaskellExp m n p e d s => GenExp m s e -> Gen m (GenExp m s e)
-- just e = do
--   r <- newName
--   return $ cont $ \k ->
--     runCont e $ \v ->
--     liftM2 (:) (binds r =<< con (hsName "Prelude.Just") [v]) (k =<< var r)

-- nothing :: MiniHaskellExp m n p e d s => Gen m (GenExp m s e)
-- nothing = do
--   return $ cont $ \k ->
--     (k =<< con (hsName "Prelude.Nothing") [])


    -- bexp' <- do
  --       abs x =<< mkUnpairs x fvP =<< genExp bexp
  -- return (f, g, bexp', wexp')
  -- where
  --   mkUnpairs x [] body = do
  --     vx <- var x
  --     rununit vx body
  --   mkUnpairs x [y] body = do
  --     f <- abs y body
  --     z <- var x
  --     app f z
  --   mkUnpairs x (y:ys) body = do
  --     vx <- var x
  --     r <- newName
  --     runpair vx =<< (abs y =<< abs r =<< mkUnpairs r ys body)


  -- x <- newName
  -- vx <- var x
  -- let fvP  = map fromName $ freeVarsP pat
  -- let pat' = genPat pat
  -- -- let just x  = con (Original (ModuleName "Prelude") (User "Just"))   [x]
  -- -- let nothing = con (Original (ModuleName "Prelude") (User "Nothing")) []

  -- f <- do
  --   body1 <- just =<< pairsToRight =<< mapM var fvP
  --   body2 <- nothing
  --   abs x =<< case_ vx [ (pat', body1), (pvar x, body2) ]
  -- g <- do
  --   body1 <- just =<< genExpFromPat pat
  --   abs x =<< case_ vx [ (pairsToRightP (map pvar fvP), body1) ]

  -- wexp' <- genExp wexp

  -- bexp' <- do
  --       abs x =<< mkUnpairs x fvP =<< genExp bexp
  -- return (f, g, bexp', wexp')
  -- where
  --   mkUnpairs x [] body = do
  --     vx <- var x
  --     rununit vx body
  --   mkUnpairs x [y] body = do
  --     f <- abs y body
  --     z <- var x
  --     app f z
  --   mkUnpairs x (y:ys) body = do
  --     vx <- var x
  --     r <- newName
  --     runpair vx =<< (abs y =<< abs r =<< mkUnpairs r ys body)





-- mkTup :: MiniHaskellExp m n p e d s => [e] -> m e
-- mkTup [e] = return e
-- mkTup es  = con (fromName $ nameTuple $ length es) es

mkConP :: MiniHaskellPat n p => Name -> [p] -> p
mkConP n ps
  | Just _ <- checkNameTuple n = ptuple ps
  | otherwise                  = pcon (fromName n) ps

genPat :: MiniHaskellPat n p => C.Pat Name -> p
genPat (C.PVar x)    = pvar (fromName x)
genPat (C.PCon n ps) = mkConP n (map genPat ps)

genExpFromPat :: MiniHaskellExp m n p e d s t c => C.Pat Name -> m e
genExpFromPat (C.PVar x)    = var (fromName x)
genExpFromPat (C.PCon n ps) = mkCon n =<< mapM genExpFromPat ps

pairsToRight :: MiniHaskellExp m n p e d s t c => [e] -> m e
pairsToRight []  = tuple []
pairsToRight [e] = return e
pairsToRight (e:es) = do
  r' <- pairsToRight es
  tuple [e, r']


pairsToRightR :: MiniHaskellExp m n p e d s t c => [GenExp m s e] -> Gen m (GenExp m s e)
pairsToRightR []  = runit
pairsToRightR [e] = T.lift $ return e
pairsToRightR (e:es) = do
  r' <- pairsToRightR es
  rpair e r'

pairsToRightP :: MiniHaskellPat n p => [p] -> p
pairsToRightP []  = ptuple []
pairsToRightP [p] = p
pairsToRightP (p:ps) =
  ptuple [p, pairsToRightP ps]
