{-# LANGUAGE ConstraintKinds #-}
module Language.Sparcl.Module where

import qualified Data.Map as M
import qualified Data.Set as S

import Language.Sparcl.Core.Syntax
import Language.Sparcl.Desugar
import Language.Sparcl.Eval
import Language.Sparcl.Value
import Language.Sparcl.Exception 
import Language.Sparcl.Typing.Typing
import Language.Sparcl.Typing.TC
import Language.Sparcl.Class

import Language.Sparcl.Surface.Parsing 

import System.Directory as Dir (doesFileExist)
import qualified System.FilePath as FP ((</>), (<.>))

import Control.Monad.Reader
import System.IO 

import Language.Sparcl.Pretty
import qualified Text.PrettyPrint.ANSI.Leijen as D

import Data.IORef 

-- import Control.Exception (Exception, throw)

data ModuleInfo = ModuleInfo {
  miModuleName :: ModuleName,
  miTables     :: Tables 
  }

data InterpInfo = InterpInfo {
  iiSearchPath  :: [FilePath],
  iiTables      :: Tables, 
  iiTInfo       :: TInfo,
  iiModuleTable :: IORef ModuleTable
  }

type ModuleTable = M.Map ModuleName ModuleInfo   

-- type M = ReaderT InterpInfo (StateT ModuleTable IO)
type M = ReaderT InterpInfo IO 

data Tables = Tables
              { tDefinedNames :: [QName],
                tOpTable      :: OpTable,
                tTypeTable    :: TypeTable,
                tSynTable     :: SynTable,
                tValueTable   :: ValueTable 
              }

mergeTables :: Tables -> Tables -> Tables
mergeTables t1 t2 =
  setDefinedNames  (tDefinedNames t1 ++ ) $
  setOpTable       (M.union $ tOpTable t1) $
  setTypeTable     (M.union $ tTypeTable t1) $
  setSynTable      (M.union $ tSynTable t1) $
  setValueTable    (M.union $ tValueTable t1) $
  t2

setDefinedNames :: ([QName] -> [QName]) -> Tables -> Tables 
setDefinedNames f t = t { tDefinedNames = f (tDefinedNames t) }

setOpTable :: (OpTable -> OpTable) -> Tables -> Tables 
setOpTable f t = t { tOpTable = f (tOpTable t) }

setTypeTable :: (TypeTable -> TypeTable) -> Tables -> Tables
setTypeTable f t = t { tTypeTable = f (tTypeTable t) }

setSynTable :: (SynTable -> SynTable) -> Tables -> Tables
setSynTable f t = t { tSynTable = f (tSynTable t) }

setValueTable :: (ValueTable -> ValueTable) -> Tables -> Tables
setValueTable f t = t { tValueTable = f (tValueTable t) }

iiSetTable :: (Tables -> Tables) -> InterpInfo -> InterpInfo 
iiSetTable f t = t { iiTables = f (iiTables t) } 

miSetTables :: (Tables -> Tables) -> ModuleInfo -> ModuleInfo
miSetTables f t = t { miTables = f (miTables t) }  

instance HasOpTable M where
  getOpTable     = asks $ tOpTable . iiTables
  localOpTable f = local $ iiSetTable $ setOpTable f 
    
instance HasTypeTable M where
  getTypeTable = asks $ tTypeTable . iiTables
  localTypeTable f = local $ iiSetTable $ setTypeTable f 

instance HasDefinedNames M where
  getDefinedNames = asks $ tDefinedNames . iiTables
  localDefinedNames f = local $ iiSetTable $ setDefinedNames f

instance HasSynTable M where
  getSynTable = asks $ tSynTable . iiTables
  localSynTable f = local $ iiSetTable $ setSynTable f

instance HasValueTable M where
  getValueTable = asks $ tValueTable . iiTables
  localValueTable f = local $ iiSetTable $ setValueTable f 


instance HasTInfo M where
  getTInfo = asks iiTInfo

class HasModuleTable m where
  getModuleTable :: m ModuleTable
--  localModuleTable :: (ModuleTable -> ModuleTable) -> m r -> m r 

instance HasModuleTable M where
  getModuleTable = do
    ref <- asks iiModuleTable
    liftIO $ readIORef ref

  -- localModuleTable f m = do
  --   ref <- asks iiModuleTable
  --   old <- liftIO $ readIORef ref
  --   liftIO $ writeIORef ref (f old)
  --   res <- m
  --   liftIO $ writeIORef ref old
  --   return res

instance HasSearchPath M where
  getSearchPath = asks iiSearchPath
  localSearchPath f =
    local $ \ii -> ii { iiSearchPath = f (iiSearchPath ii) }

type HasTables m = (HasDefinedNames m,
                    HasOpTable m, 
                    HasTypeTable m,
                    HasSynTable m,
                    HasValueTable m) 

class HasModuleTable m => ModifyModuleTable m where
  modifyModuleTable :: (ModuleTable -> ModuleTable) -> m ()

instance ModifyModuleTable M where
  modifyModuleTable f = do
    ref <- asks iiModuleTable
    old <- liftIO $ readIORef ref
    liftIO $ writeIORef ref (f old)
  
    



-- runMTest :: [FilePath] -> M a -> IO a
-- runMTest searchPath m = do
--   tinfo <- initTInfo
--   let ii = initInterpInfo tinfo searchPath 
--   evalStateT (runReaderT (withImport baseModuleInfo m) ii) M.empty

runM :: [FilePath] -> TInfo -> M a -> IO a
runM searchPath tinfo m = do
  ii <- initInterpInfo tinfo searchPath 
  -- (res, _) <- runStateT (runReaderT (withImport baseModuleInfo m) ii) M.empty
  runReaderT (withImport baseModuleInfo m) ii 
--  return res

initTables :: Tables 
initTables = Tables [] M.empty M.empty M.empty M.empty

initInterpInfo :: TInfo -> [FilePath] -> IO InterpInfo
initInterpInfo tinfo searchPath = do
  ref <- newIORef M.empty  
  return $ InterpInfo { iiSearchPath = searchPath,
                        iiTables = initTables, 
                        iiTInfo      = tinfo,
                        iiModuleTable = ref }
    
baseModuleInfo :: ModuleInfo 
baseModuleInfo = ModuleInfo {
  miModuleName = baseModule,
  miTables = Tables { 
      tDefinedNames = [
          conTrue, conFalse,
          nameTyBang, nameTyBool, nameTyChar, nameTyDouble,
          nameTyInt, nameTyLArr, nameTyRev, nameTyList,
          base "+", base "-", base "*",
          eqInt, leInt, ltInt,
          eqChar, leChar, ltChar
      ], 
  
      tTypeTable = M.fromList [
          conTrue  |-> boolTy,
          conFalse |-> boolTy,
          base "+" |-> intTy -@ (intTy -@ intTy),
          base "-" |-> intTy -@ (intTy -@ intTy),
          base "*" |-> intTy -@ (intTy -@ intTy),
          eqInt  |-> intTy -@ intTy -@ boolTy,
          leInt  |-> intTy -@ intTy -@ boolTy,
          ltInt  |-> intTy -@ intTy -@ boolTy,
          eqChar |-> charTy -@ charTy -@ boolTy,
          leChar |-> charTy -@ charTy -@ boolTy,
          ltChar |-> charTy -@ charTy -@ boolTy 
          ],
    
      tSynTable = M.empty,
      tOpTable  = M.fromList [
          base "+" |-> (Prec 60, L),
          base "-" |-> (Prec 60, L),
          base "*" |-> (Prec 70, L) ], 
        
      tValueTable = M.fromList [
          base "+" |-> intOp (+),
          base "-" |-> intOp (-),
          base "*" |-> intOp (*),
            eqInt  |-> (VFun $ \n -> return $ VFun $ \m -> return $ fromBool (unInt n == unInt m)),
            leInt  |-> (VFun $ \n -> return $ VFun $ \m -> return $ fromBool (unInt n <= unInt m)),
            ltInt  |-> (VFun $ \n -> return $ VFun $ \m -> return $ fromBool (unInt n <  unInt m)),
            eqChar |-> (VFun $ \c -> return $ VFun $ \d -> return $ fromBool (unChar c == unChar d)),
            leChar |-> (VFun $ \c -> return $ VFun $ \d -> return $ fromBool (unChar c <= unChar d)),
            ltChar |-> (VFun $ \c -> return $ VFun $ \d -> return $ fromBool (unChar c <  unChar d))
          ]
      }
  }
  where
    eqInt = base "eqInt"
    leInt = base "leInt"
    ltInt = base "ltInt"
    eqChar = base "eqChar"
    leChar = base "leChar"
    ltChar = base "ltChar"
 
    unInt  (VLit (LitInt n)) = n
    unInt  _                 = rtError $ D.text "Not an integer"
    unChar (VLit (LitChar n)) = n
    unChar _                  = rtError $ D.text "Not a character"

    fromBool True  = VCon conTrue  []
    fromBool False = VCon conFalse []
    
    intOp f = VFun $ \(VLit (LitInt n)) -> return $ VFun $ \(VLit (LitInt m)) -> return (VLit (LitInt (f n m)))
    
    intTy = TyCon (base "Int") []
    base n = QName baseModule (NormalName n) 
    a |-> b = (a, b) 
    infix 0 |-> 
  

debugPrint :: MonadIO m => String -> m ()
debugPrint = liftIO . hPutStrLn stderr 

withOpTable :: HasOpTable m => OpTable -> m r -> m r
withOpTable newOpTable m = do
  -- opTable <- asks iiOpTable
  -- local (\ii -> ii { iiOpTable = M.union newOpTable opTable }) m
  localOpTable (M.union newOpTable) m 

withTypeTable :: HasTypeTable m => TypeTable -> m r -> m r
withTypeTable newTbl m = do
  localTypeTable (M.union newTbl) m
  -- tbl <- asks iiTypeTable
  -- local (\ii -> ii { iiTypeTable = M.union newTbl tbl }) m

withSynTable :: HasSynTable m => SynTable -> m r -> m r 
withSynTable newTbl m = do
  localSynTable (M.union newTbl) m 
  -- tbl <- asks iiSynTable
  -- local (\ii -> ii { iiSynTable = M.union newTbl tbl }) m

withValueTable :: HasValueTable m => ValueTable -> m r -> m r 
withValueTable newTbl m = do
  localValueTable (M.union newTbl) m 
  -- tbl <- asks iiValueTable
  -- local (\ii -> ii { iiValueTable = M.union newTbl tbl }) m

withDefinedNames :: HasDefinedNames m => [QName] -> m r -> m r
withDefinedNames newTbl m = do
  localDefinedNames (newTbl ++) m 
  -- tbl <- asks iiDefinedNames
  -- local (\ii -> ii { iiDefinedNames = newTbl ++ tbl}) m 


-- withImport :: ModuleInfo -> M r -> M r
withImport :: HasTables m => ModuleInfo -> m r -> m r 
withImport mod m = do
  let t = miTables mod 
  withOpTable (tOpTable t) $
    withTypeTable (tTypeTable t) $
      withSynTable (tSynTable t) $
        withDefinedNames (tDefinedNames t) $
          withValueTable (tValueTable t) m 
  

withImports :: HasTables m => [ModuleInfo] -> m r -> m r
withImports ms comp =
  foldr withImport comp ms 

ext :: String
ext = "sparcl"

moduleNameToFilePath :: ModuleName -> FilePath
moduleNameToFilePath mn =
  (foldr1 (FP.</>) mn) FP.<.> ext

restrictNames :: [QName] -> ModuleInfo -> ModuleInfo
restrictNames ns mi = 
  let mn = miModuleName mi
      ns' = S.fromList $ ns ++ [ QName mn n | BName n <- ns ]
      restrict :: M.Map QName a -> M.Map QName a 
      restrict x = M.restrictKeys x ns' 
      mi' = miSetTables (\t -> t { tDefinedNames = filter (`elem` ns) (tDefinedNames t), 
                                   tOpTable    = restrict (tOpTable t),
                                   tTypeTable  = restrict (tTypeTable t),
                                   tSynTable   = restrict (tSynTable t),
                                   tValueTable = restrict (tValueTable t) }) mi 
  in mi' 
                 

searchModule :: (MonadIO m, HasSearchPath m) => ModuleName -> m FilePath
searchModule mod = do
  dirs <- getSearchPath
  let file = moduleNameToFilePath mod 
  let searchFiles = [ dir FP.</> file | dir <- dirs ]
  fs <- liftIO $ mapM Dir.doesFileExist searchFiles
  case map fst $ filter snd $ zip searchFiles fs of
    fp:_ -> return fp 
    _    -> error $ "ERROR: Cannot find module " ++ foldr1 (\a b -> a ++ "." ++ b) mod


readModule :: (MonadIO m, HasTables m, HasTInfo m, HasSearchPath m, ModifyModuleTable m) =>
              FilePath -> m ModuleInfo
readModule fp = do
  -- Clear cache. 
  modifyModuleTable (const $ M.empty)
  -- reset emvironments. 
  localDefinedNames (const []) $
    localOpTable (const $ M.empty) $
      localTypeTable (const $ M.empty) $
        localSynTable (const $ M.empty) $
          withImport baseModuleInfo $ 
            readModuleWork fp 

readModuleWork :: (MonadIO m, HasTables m, HasTInfo m, HasSearchPath m, ModifyModuleTable m) =>
                  FilePath -> m ModuleInfo
readModuleWork fp = do
  debugPrint $ "Parsing " ++ fp ++ " ..." 
  s <- liftIO $ readFile fp 
  Module mod exports imports decls <- either (staticError . D.text) return $ parseModule fp s

  debugPrint $ "Parsing Ok." 

  
  ms <- mapM (\(Import m is) ->
                 do md <- interpModuleWork m
                    case is of
                      Nothing -> return md
                      Just ns -> 
                        return $ restrictNames (map (qualifyName m) ns) md) imports

  withImports ms $ do 
    definedNames <- getDefinedNames
    opTable      <- getOpTable

    debugPrint $ "Desugaring ..."
    debugPrint $ show $ D.group $ D.nest 2 $ D.text "w.r.t. opTable: " D.<$> pprMap opTable
    
    (decls', newDefinedNames, newOpTable, newDataTable, newSynTable) <-
           liftIO $ runDesugar mod definedNames opTable (desugarTopDecls decls)

    debugPrint $ "Desugaring Ok."
    debugPrint $ show (D.group $ D.nest 2 $ D.text "Desugared syntax:" D.</> D.align (ppr decls'))

    withOpTable newOpTable $
      withTypeTable newDataTable $
        withSynTable newSynTable $ do
          modTbl <- getModuleTable 
          tyEnv  <- getTypeTable

          debugPrint "Type checking..."
          debugPrint $ show (D.text "under ty env" D.<+> pprMap tyEnv)

          tinfo <- getTInfo 
          synEnv <- getSynTable
          liftIO $ setEnvs tinfo tyEnv synEnv 
          
          nts <- liftIO $ runTC tinfo $ inferDecls decls'


          -- let env = foldr M.union M.empty $ map miValueTable ms
          env <- getValueTable 
          let env' = runEval (evalUDecls env decls') 

          let newMod = ModuleInfo {
                miModuleName = mod, 
                miTables = Tables {
                    tOpTable    = newOpTable,
                    tDefinedNames = newDefinedNames, 
                    tSynTable   = newSynTable,
                    tTypeTable  = foldr (uncurry M.insert) ({- M.mapKeys (qualifyName mod) -} newDataTable) nts,
                    tValueTable = -- M.mapKeys (qualifyName mod) $
                        env'
                  }
                }                

          modifyModuleTable (const $ M.insert mod newMod modTbl)

          case exports of
            Just es -> 
              return $ restrictNames (map (qualifyName mod) es) newMod
            _ ->
              return newMod

   where
     qualifyName cm (BName n) = QName cm n
     qualifyName _  (QName cm n) = QName cm n 
              
  
interpModuleWork :: (MonadIO m, HasTables m, HasTInfo m, HasSearchPath m, ModifyModuleTable m) =>
                    ModuleName -> m ModuleInfo 
interpModuleWork mod = do
  modTable <- getModuleTable 
  case M.lookup mod modTable of
    Just modData -> return modData
    _            -> do 
      fp <- searchModule mod
      readModuleWork fp 
               
  
  
  
