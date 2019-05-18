{-# OPTIONS_GHC -Wno-orphans #-}

module Language.Sparcl.TH (sparcl, sparclf, parseToQDec, parseToQDec') where

import Language.Sparcl.CodeGen.Haskell as Gen
import Language.Sparcl.Core.Syntax as C
import Language.Sparcl.Pretty hiding ((<$>))
-- import Language.Sparcl.Typing.Type as C
import Language.Sparcl.Typing.TCMonad
-- import Language.Sparcl.Literal

import Language.Sparcl.Surface.Parsing (parseDecl)
import Language.Sparcl.Module (baseModuleInfo, ModuleInfo(..))
import Language.Sparcl.Exception (staticError)

import Language.Sparcl.Renaming 
import Language.Sparcl.Typing.Typing (inferTopDecls)
import Language.Sparcl.Desugar       (desugarTopDecls, runDesugar)

import qualified Language.Haskell.TH as TH
import qualified Language.Haskell.TH.Syntax as TH
import qualified Language.Haskell.TH.Quote as TH

import Control.Monad.IO.Class

data HName = HName { hLhsName :: TH.Name, hRhsName :: TH.Name }


mkGName :: String -> String -> HName 
mkGName m s = HName (TH.mkName s) (TH.mkName (m ++ "." ++ s))

mkLName :: String -> HName
mkLName s   = HName (TH.mkName s) (TH.mkName s)

instance IsName HName where
  fromName nn@(Original m n _)
    | nn == conTrue  = mkGName "Prelude" "True"
    | nn == conFalse = mkGName "Prelude" "False" 
    | otherwise      =
      HName (TH.mkName $ unUser n)
            (TH.mkName $ Gen.genModuleName m ++ "." ++ (unUser n))
  fromName (Alpha i n) = mkLName $ "_a" ++ Gen.encNameL (unUser n) ++ show i
  fromName (Local n)   = mkLName $ "_l" ++ Gen.encNameL (unUser n)
  fromName (Generated n p) = mkLName $ "_g" ++ Gen.phaseStr p ++ show n


instance HsName HName where
  hsName s = HName (error "hsName: The name can only be used in RHS.") (TH.mkName s)
  rtName s = HName (TH.mkName s) (TH.mkName $ Gen.runtimePrefix ++ s)
  
    
      



instance MiniHaskellPat HName TH.Pat where
  pvar n = TH.VarP (hLhsName n)
  pcon n ps = TH.ConP (hRhsName n) ps
  ptuple ps = TH.TupP ps 

instance MiniHaskellExp TH.Q HName TH.Pat TH.Exp TH.Dec TH.Stmt TH.Type where
  var n = TH.varE (hRhsName n)
  lit l = TH.litE (l2l l)
    where
      l2l :: Literal -> TH.Lit
      l2l (LitChar c) = TH.CharL c
      l2l (LitDouble d) = TH.DoublePrimL (realToFrac d)
      l2l (LitInt i)    = TH.IntegerL (fromIntegral i)
      l2l (LitRational r) = TH.RationalL r 
      
  app e1 e2 = return $ TH.AppE e1 e2
  abs x e = return $ TH.LamE [TH.VarP $ hLhsName x] e

  con n es = return $ foldl TH.AppE (TH.ConE (hRhsName n)) es

  case_ e0 pes = return $ TH.CaseE e0 $
                 map (\(p,e) -> TH.Match p (TH.NormalB e) []) pes

  let_ ds e = return $ TH.LetE ds e
  --bind = mapM (\(n,e) -> return $ TH.ValD (TH.VarP $ hLhsName n) (TH.NormalB e) [])

  vald n e = return $ TH.ValD (TH.VarP $ hLhsName n) (TH.NormalB e) []
  sigd n t = return $ TH.SigD (hLhsName n) t

  datad n tvs cs = return $
    TH.DataD [] (hLhsName n) [TH.PlainTV $ hLhsName tv | tv <- tvs] Nothing
     [ TH.NormalC (hLhsName c) [ (TH.Bang TH.NoSourceUnpackedness TH.SourceStrict, t) | t <- ts] | (c,ts) <- cs ] 
     []
  typed n tvs t = return $
    TH.TySynD (hLhsName n) [TH.PlainTV $ hLhsName tv | tv <- tvs ] t 


  list = return . TH.ListE
  tuple = return . TH.TupE 

  do_ = return . TH.DoE

  lets = return . TH.LetS
  nobinds = return . TH.NoBindS
  binds n e = return $ (TH.BindS (TH.VarP $ hLhsName n) e)


instance MiniHaskellType HName TH.Type where
  tyvar x = TH.VarT $ hLhsName x
  tyfun t1 t2 = TH.ArrowT `TH.AppT` t1 `TH.AppT` t2
  tycon n ts  =
    foldl TH.AppT (TH.ConT (hRhsName n)) ts
  tytuple ts = foldl TH.AppT (TH.TupleT (length ts)) ts
  tylist t   = TH.ListT `TH.AppT` t
  tyforall ns t =
    TH.ForallT [TH.PlainTV (hLhsName tv) | tv <- ns] [] t 

-- ty2ty :: C.Ty -> TH.Type
-- ty2ty (C.TyCon n ts)
--   | n == nameTyLArr, [t1,t2] <- ts  =
--       TH.ArrowT `TH.AppT` ty2ty t1 `TH.AppT` (TH.ConT (TH.mkName $ Gen.runtimePrefix ++ "R") `TH.AppT` ty2ty t2)
--   | n == nameTyList, [t1] <- ts =
--       TH.ListT `TH.AppT` ty2ty t1
--   | Just _ <- checkNameTyTuple n =
--       foldl (\r a -> r `TH.AppT` ty2ty a) (TH.TupleT $ length ts) ts
--   | n == nameTyRev, [t1] <- ts =
--       TH.ConT (TH.mkName $ Gen.runtimePrefix ++ "Rev") `TH.AppT` ty2ty t1
--   | n == nameTyBang, [t1] <- ts =
--       ty2ty t1
--   | n == nameTyInt =
--     TH.ConT (TH.mkName "Prelude.Int")
--   | n == nameTyDouble =
--     TH.ConT (TH.mkName "Prelude.Double")
--   | n == nameTyChar =
--     TH.ConT (TH.mkName "Prelude.Char")
--   | n == nameTyBool =
--     TH.ConT (TH.mkName "Prelude.Bool")
--   | otherwise = 
--     foldl (\r a -> r `TH.AppT` ty2ty a) (TH.ConT $ TH.mkName $ rhsName n) ts
-- ty2ty (C.TyForAll tvs ty) =
--   TH.ForallT [TH.PlainTV (TH.mkName (prettyShow tv)) | tv <- tvs] [] (ty2ty ty)
-- ty2ty (C.TyVar tv)   = TH.VarT $ TH.mkName (prettyShow tv)
-- ty2ty (C.TySyn ty _) = ty2ty ty
-- ty2ty (C.TyMetaV _)  = error "Cannot happen."

-- convertDataDecls :: [C.DDecl C.Name] -> TH.Q [TH.Dec]
-- convertDataDecls = return . map convertDataDecl
--   where
--     convertDataDecl :: C.DDecl C.Name -> TH.Dec
--     convertDataDecl (C.DDecl n tvs cs) =
--       TH.DataD [] (TH.mkName $ Gen.lhsName n)
--                   [ TH.PlainTV (TH.mkName $ prettyShow tv) | tv <- tvs ]
--                   Nothing (map genC cs) []
--       where
--         genC (c,ts) = TH.NormalC (TH.mkName $ lhsName c) $
--                       map (\t -> (TH.Bang TH.NoSourceUnpackedness TH.SourceStrict, ty2ty t)) ts 

-- convertTypeDecls :: [C.TDecl C.Name] -> TH.Q [TH.Dec]
-- convertTypeDecls = return . map convertTypeDecl
--   where
--     convertTypeDecl :: C.TDecl C.Name -> TH.Dec
--     convertTypeDecl (TDecl n tvs ty) =
--       TH.TySynD (TH.mkName $ rhsName n)
--                 [ TH.PlainTV (TH.mkName $ prettyShow tv) | tv <- tvs ]
--                 (ty2ty ty)


parseToQDec' :: FilePath -> String -> TH.Q [TH.Dec]
parseToQDec' fp str = do
  decs <- parseToQDec str
  liftIO $ writeFile fp $ show $ TH.ppr decs
  return decs
  

parseToQDec :: String -> TH.Q [TH.Dec]
parseToQDec str = do
  decls <- either (staticError . text) return $ parseDecl str

  TH.Module _ (TH.ModName modName) <- TH.thisModule
  let currentModule = ModuleName modName 

  let opTable   = miOpTable baseModuleInfo
  let nameTable = miNameTable baseModuleInfo 
  
  (renamedDecls, dataDecls, synDecls, _newNames, _newOpTable) <-
      liftIO $ either nameError return $ runRenaming nameTable opTable $ renameTopDecls currentModule decls

  tinfo <- liftIO initTypingContext
  -- liftIO $ setEnvs tinfo (miTypeTable baseModuleInfo) (miSynTable baseModuleInfo)

  (typedDecls, _nts, dataDecls', typeDecls', _newTypeTable, _newSynTable) <-
      liftIO $ runTCWith tinfo (miTypeTable baseModuleInfo) (miSynTable baseModuleInfo) $ inferTopDecls renamedDecls dataDecls synDecls

  desugarred <- liftIO $ runTC tinfo $ runDesugar $ desugarTopDecls typedDecls

  -- dDecs <- convertDataDecls dataDecls'
  -- tDecs <- convertTypeDecls typeDecls'

  decs  <- Gen.runGen $ Gen.genTopBind dataDecls' typeDecls' desugarred

--  let res = dDecs ++ tDecs ++ decs

  -- liftIO $ print $ TH.ppr decs
  
  return decs
  where
    nameError (l, d) =
       staticError (nest 2 (ppr l </> d))

sparcl :: TH.QuasiQuoter
sparcl = TH.QuasiQuoter {
  TH.quoteDec  = parseToQDec,
  TH.quoteExp  = unimplemented "expression",
  TH.quotePat  = unimplemented "pattern",
  TH.quoteType = unimplemented "type"
  }
  where
    unimplemented s = error $ "sparcl: " ++ "quasiquoter for " ++ s ++ " is not implemented."

sparclf :: TH.QuasiQuoter
sparclf = TH.quoteFile sparcl 
