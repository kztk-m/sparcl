{-# LANGUAGE ConstraintKinds #-}
module Language.Sparcl.Module where

import qualified Data.Map as M
import qualified Data.Set as S

import Data.Function (on) 

import System.Directory as Dir (doesFileExist, createDirectoryIfMissing)
import qualified System.FilePath as FP ((</>), (<.>), takeDirectory)

import qualified Control.Monad.State as St
import Control.Monad.IO.Class
import Control.Monad (forM, when)
import System.IO 

import Language.Sparcl.Pretty hiding ((<$>))

import Language.Sparcl.Core.Syntax
import Language.Sparcl.Surface.Syntax (Prec(..), Assoc(..))
import Language.Sparcl.Desugar
import Language.Sparcl.Renaming 
import Language.Sparcl.Value
import Language.Sparcl.Exception 
import Language.Sparcl.Typing.Typing
import Language.Sparcl.Typing.Type
import Language.Sparcl.Typing.TCMonad
import Language.Sparcl.Class

import Language.Sparcl.CodeGen.Haskell (toDocTop, targetFilePath) 

import Language.Sparcl.Surface.Parsing 

-- import Control.Exception (Exception, throw)

data KeyName
data KeyOp
data KeyType
data KeySyn
data KeySearchPath
data KeyValue
data KeyTC
data KeyVerb
data KeyLoadPath 

type MonadModule v m =
  (MonadIO m,
   Has   KeyLoadPath   FilePath m, 
   Has   KeyTC         TypingContext m,
   Has   KeyVerb       Int   m, 
   Local KeyName       NameTable m, 
   Local KeyOp         OpTable   m,
   Local KeyType       TypeTable m,
   Local KeySyn        SynTable m,
   Has   KeySearchPath [FilePath] m,   
   Local KeyValue      (M.Map Name v) m) 

data ModuleInfo v = ModuleInfo {
  miModuleName :: ModuleName,
  miNameTable  :: NameTable,
  miOpTable    :: OpTable,
  miTypeTable  :: TypeTable,
  miSynTable   :: SynTable,
  miValueTable :: M.Map Name v,
  miHsFile     :: FilePath 
  }

-- for caching.
type ModuleTable v = M.Map ModuleName (ModuleInfo v)

type M v m a = MonadModule v m => St.StateT (ModuleTable v) m a 




-- data ModuleInfo = ModuleInfo {
--   miModuleName :: ModuleName,
--   miTables     :: Tables 
--   }

-- data InterpInfo = InterpInfo {
--   iiSearchPath  :: [FilePath],
--   iiTables      :: Tables, 
--   iiTInfo       :: TInfo,
--   iiModuleTable :: IORef ModuleTable
--   }


-- -- type M = ReaderT InterpInfo (StateT ModuleTable IO)
-- type M = ReaderT InterpInfo IO 

-- data Tables = Tables
--               { tDefinedNames :: [QName],
--                 tOpTable      :: OpTable,
--                 tTypeTable    :: TypeTable,
--                 tSynTable     :: SynTable,
--                 tValueTable   :: ValueTable 
--               }

-- mergeTables :: Tables -> Tables -> Tables
-- mergeTables t1 t2 =
--   setDefinedNames  (tDefinedNames t1 ++ ) $
--   setOpTable       (M.union $ tOpTable t1) $
--   setTypeTable     (M.union $ tTypeTable t1) $
--   setSynTable      (M.union $ tSynTable t1) $
--   setValueTable    (M.union $ tValueTable t1) $
--   t2

-- setDefinedNames :: ([QName] -> [QName]) -> Tables -> Tables 
-- setDefinedNames f t = t { tDefinedNames = f (tDefinedNames t) }

-- setOpTable :: (OpTable -> OpTable) -> Tables -> Tables 
-- setOpTable f t = t { tOpTable = f (tOpTable t) }

-- setTypeTable :: (TypeTable -> TypeTable) -> Tables -> Tables
-- setTypeTable f t = t { tTypeTable = f (tTypeTable t) }

-- setSynTable :: (SynTable -> SynTable) -> Tables -> Tables
-- setSynTable f t = t { tSynTable = f (tSynTable t) }

-- setValueTable :: (ValueTable -> ValueTable) -> Tables -> Tables
-- setValueTable f t = t { tValueTable = f (tValueTable t) }

-- iiSetTable :: (Tables -> Tables) -> InterpInfo -> InterpInfo 
-- iiSetTable f t = t { iiTables = f (iiTables t) } 

-- miSetTables :: (Tables -> Tables) -> ModuleInfo -> ModuleInfo
-- miSetTables f t = t { miTables = f (miTables t) }  

-- instance HasOpTable M where
--   getOpTable     = asks $ tOpTable . iiTables
--   localOpTable f = local $ iiSetTable $ setOpTable f 
    
-- instance HasTypeTable M where
--   getTypeTable = asks $ tTypeTable . iiTables
--   localTypeTable f = local $ iiSetTable $ setTypeTable f 

-- instance HasDefinedNames M where
--   getDefinedNames = asks $ tDefinedNames . iiTables
--   localDefinedNames f = local $ iiSetTable $ setDefinedNames f

-- instance HasSynTable M where
--   getSynTable = asks $ tSynTable . iiTables
--   localSynTable f = local $ iiSetTable $ setSynTable f

-- instance HasValueTable M where
--   getValueTable = asks $ tValueTable . iiTables
--   localValueTable f = local $ iiSetTable $ setValueTable f 


-- instance HasTInfo M where
--   getTInfo = asks iiTInfo

-- class HasModuleTable m where
--   getModuleTable :: m ModuleTable
-- --  localModuleTable :: (ModuleTable -> ModuleTable) -> m r -> m r 

-- instance HasModuleTable M where
--   getModuleTable = do
--     ref <- asks iiModuleTable
--     liftIO $ readIORef ref

--   -- localModuleTable f m = do
--   --   ref <- asks iiModuleTable
--   --   old <- liftIO $ readIORef ref
--   --   liftIO $ writeIORef ref (f old)
--   --   res <- m
--   --   liftIO $ writeIORef ref old
--   --   return res

-- instance HasSearchPath M where
--   getSearchPath = asks iiSearchPath
--   localSearchPath f =
--     local $ \ii -> ii { iiSearchPath = f (iiSearchPath ii) }

-- type HasTables m = (HasDefinedNames m,
--                     HasOpTable m, 
--                     HasTypeTable m,
--                     HasSynTable m,
--                     HasValueTable m) 

-- class HasModuleTable m => ModifyModuleTable m where
--   modifyModuleTable :: (ModuleTable -> ModuleTable) -> m ()

-- instance ModifyModuleTable M where
--   modifyModuleTable f = do
--     ref <- asks iiModuleTable
--     old <- liftIO $ readIORef ref
--     liftIO $ writeIORef ref (f old)
  
    



-- runMTest :: [FilePath] -> M a -> IO a
-- runMTest searchPath m = do
--   tinfo <- initTInfo
--   let ii = initInterpInfo tinfo searchPath 
--   evalStateT (runReaderT (withImport baseModuleInfo m) ii) M.empty


runM :: MonadModule v m => M v m a -> m a
runM m = St.evalStateT m M.empty 

-- runM :: [FilePath] -> TInfo -> M a -> IO a
-- runM searchPath tinfo m = do
--   ii <- initInterpInfo tinfo searchPath 
--   -- (res, _) <- runStateT (runReaderT (withImport baseModuleInfo m) ii) M.empty
--   runReaderT (withImport baseModuleInfo m) ii 
-- --  return res

-- initTables :: Tables 
-- initTables = Tables [] M.empty M.empty M.empty M.empty

-- initInterpInfo :: TInfo -> [FilePath] -> IO InterpInfo
-- initInterpInfo tinfo searchPath = do
--   ref <- newIORef M.empty  
--   return $ InterpInfo { iiSearchPath = searchPath,
--                         iiTables = initTables, 
--                         iiTInfo      = tinfo,
--                         iiModuleTable = ref }
    
baseModuleInfo :: ModuleInfo Value 
baseModuleInfo = ModuleInfo {
  miModuleName = baseModule,
  miNameTable  = M.fromListWith (S.union) $
                 [ (Bare n, S.fromList [(mn ,n)]) | Original mn n _ <- names ]
                 ++ [ (Qual mn n, S.fromList [(mn, n)]) | Original mn n _ <- names ], 
  miOpTable    = opTable,
  miTypeTable  = typeTable,
  miSynTable   = synTable,
  miValueTable = valueTable,
  miHsFile     = "Language.Sparcl.Base"
  }
  where
    eqInt = base "eqInt"
    leInt = base "leInt"
    ltInt = base "ltInt"
    eqChar = base "eqChar"
    leChar = base "leChar"
    ltChar = base "ltChar"

    unInt  (VLit (LitInt n)) = n
    unInt  _                 = rtError $ text "Not an integer"
    unChar (VLit (LitChar n)) = n
    unChar _                  = rtError $ text "Not a character"

    typeTable = M.fromList [
          conTrue  |-> boolTy,
          conFalse |-> boolTy,
          base "+" |-> intTy -@ (intTy -@ intTy),
          base "-" |-> intTy -@ (intTy -@ intTy),
          base "*" |-> intTy -@ (intTy -@ intTy),

          -- is it OK? 
          eqInt  |-> intTy -@ intTy -@ boolTy,
          leInt  |-> intTy -@ intTy -@ boolTy,
          ltInt  |-> intTy -@ intTy -@ boolTy,
          eqChar |-> charTy -@ charTy -@ boolTy,
          leChar |-> charTy -@ charTy -@ boolTy,
          ltChar |-> charTy -@ charTy -@ boolTy,

          nameTyInt  |-> typeKi,
          nameTyBool |-> typeKi,
          nameTyChar |-> typeKi          
          ]

    synTable = M.empty

    opTable = M.fromList [
      base "+" |-> (Prec 60, L),
      base "-" |-> (Prec 60, L),
      base "*" |-> (Prec 70, L) ]

    
    valueTable = M.fromList [
          base "+" |-> intOp (+),
          base "-" |-> intOp (-),
          base "*" |-> intOp (*),
          eqInt  |-> (VFun $ \n -> return $ VFun $ \m -> return $ fromBool $ ((==) `on` unInt ) n m),
          leInt  |-> (VFun $ \n -> return $ VFun $ \m -> return $ fromBool $ ((<=) `on` unInt ) n m),
          ltInt  |-> (VFun $ \n -> return $ VFun $ \m -> return $ fromBool $ ((<)  `on` unInt ) n m),
          eqChar |-> (VFun $ \c -> return $ VFun $ \d -> return $ fromBool $ ((==) `on` unChar) c d),
          leChar |-> (VFun $ \c -> return $ VFun $ \d -> return $ fromBool $ ((<=) `on` unChar) c d),
          ltChar |-> (VFun $ \c -> return $ VFun $ \d -> return $ fromBool $ ((<)  `on` unChar) c d)
          ]

    names = M.keys typeTable

    fromBool True  = VCon conTrue  []
    fromBool False = VCon conFalse []
    
    intOp f = VFun $ \(VLit (LitInt n)) -> return $ VFun $ \(VLit (LitInt m)) -> return (VLit (LitInt (f n m)))
    
    intTy = TyCon (base "Int") []
    base n = nameInBase (User n) 
    a |-> b = (a, b) 
    infix 0 |-> 
  


  
debugPrint :: (Has KeyVerb Int m, MonadIO m) => Int -> Doc -> m ()
debugPrint n s = do 
  vlevel <- ask (key @KeyVerb)
  when (vlevel >= n) $ 
    liftIO $ displayIO stderr $ renderPretty 0.8 80 $
      dullcyan $ text ("[DEBUG " ++ show n ++ "]") <+> align s <> line
    
      



-- withOpTable :: HasOpTable m => OpTable -> m r -> m r
-- withOpTable newOpTable m = do
--   -- opTable <- asks iiOpTable
--   -- local (\ii -> ii { iiOpTable = M.union newOpTable opTable }) m
--   localOpTable (M.union newOpTable) m 

-- withTypeTable :: HasTypeTable m => TypeTable -> m r -> m r
-- withTypeTable newTbl m = do
--   localTypeTable (M.union newTbl) m
--   -- tbl <- asks iiTypeTable
--   -- local (\ii -> ii { iiTypeTable = M.union newTbl tbl }) m

-- withSynTable :: HasSynTable m => SynTable -> m r -> m r 
-- withSynTable newTbl m = do
--   localSynTable (M.union newTbl) m 
--   -- tbl <- asks iiSynTable
--   -- local (\ii -> ii { iiSynTable = M.union newTbl tbl }) m

-- withValueTable :: HasValueTable m => ValueTable -> m r -> m r 
-- withValueTable newTbl m = do
--   localValueTable (M.union newTbl) m 
--   -- tbl <- asks iiValueTable
--   -- local (\ii -> ii { iiValueTable = M.union newTbl tbl }) m

-- withDefinedNames :: HasDefinedNames m => [Name] -> m r -> m r
-- withDefinedNames newTbl m = do
--   localDefinedNames (newTbl ++) m 
--   -- tbl <- asks iiDefinedNames
--   -- local (\ii -> ii { iiDefinedNames = newTbl ++ tbl}) m 


-- withImport :: ModuleInfo -> M r -> M r
-- withImport :: HasTables m => ModuleInfo -> m r -> m r
withImport :: MonadModule v m => ModuleInfo v -> m r -> m r 
withImport mo m =
  local (key @KeyName) (M.unionWith (S.union) $ miNameTable mo) $
   local (key @KeyOp) (M.union $ miOpTable mo) $ 
    local (key @KeyType) (M.union $ miTypeTable mo) $
     local (key @KeySyn) (M.union $ miSynTable mo) $
      local (key @KeyValue) (M.union $ miValueTable mo) $ m 
  -- let t = miTables mod 
  -- withOpTable (tOpTable t) $
  --   withTypeTable (tTypeTable t) $
  --     withSynTable (tSynTable t) $
  --       withDefinedNames (tDefinedNames t) $
  --         withValueTable (tValueTable t) m 
  

withImports :: MonadModule v m => [ModuleInfo v] -> m r -> m r
withImports ms comp =
  foldr withImport comp ms

withNoTables :: MonadModule v m => m r -> m r
withNoTables m =
  local (key @KeyName) (const $ M.empty) $
   local (key @KeyOp) (const $ M.empty) $
    local (key @KeyType) (const $ M.empty) $
     local (key @KeySyn) (const $ M.empty) $
      local (key @KeyValue) (const $ M.empty) m 

ext :: String
ext = "sparcl"

moduleNameToFilePath :: ModuleName -> FilePath
moduleNameToFilePath (ModuleName mo) = go mo 
  where
    go = go2' id
    
    go2' ds [] = ds "" FP.<.> ext 
    go2' ds (c:cs)
      | c == '.'  = ds "" FP.</> go2' id cs
      | otherwise = go2' (ds . (c:)) cs  



    
--  (foldr1 (FP.</>) mn) FP.<.> ext

restrictNames :: [Name] -> ModuleInfo v -> ModuleInfo v 
restrictNames ns mi = 
  mi { miNameTable = M.mapMaybe conv (miNameTable mi),
       miOpTable   = restrict (miOpTable mi),
       miTypeTable = restrict (miTypeTable mi),
       miSynTable  = restrict (miSynTable mi),
       miValueTable = restrict (miValueTable mi)
        }
  where
    ns' = S.fromList $ ns
    
    restrict :: M.Map Name a -> M.Map Name a 
    restrict x = M.restrictKeys x ns'      

    mnsI = S.fromList [ (mn, n) | Original mn n _ <- ns ] 

    conv mns =
      let res = S.intersection mns mnsI 
      in if S.null res then
           Nothing
         else
           Just res 
        
searchModule :: (MonadIO m, MonadModule v m) => ModuleName -> m FilePath
searchModule mo = do
  dirs <- ask (key @KeySearchPath) 
  let file = moduleNameToFilePath mo
  let searchFiles = [ dir FP.</> file | dir <- dirs ]
  fs <- liftIO $ mapM Dir.doesFileExist searchFiles
  case map fst $ filter snd $ zip searchFiles fs of
    fp:_ -> return fp 
    _    -> staticError $ text "Cannot find module:" <+> ppr mo


importNames :: MonadModule v m => ModuleName -> [Loc SurfaceName] -> ModuleInfo v -> m (ModuleInfo v)
importNames mn ns m = do
  onames <- forM ns $ \(Loc loc n) -> do
    case n of
      Bare bn -> return (Original mn bn (Bare bn))
      _      -> staticError $ nest 2 $
        vcat [ ppr loc ,
               text "Qualified names in the import list:" <+> ppr n ]

  return $ restrictNames onames m 

exportNames :: MonadModule v m => [Loc SurfaceName] -> ModuleInfo v -> m (ModuleInfo v)
exportNames ns m = do
  -- In general, ns can contain names that come from other modules.
  -- Then, exporting is done by filtering all the available names.

  nameTbl <- M.union (miNameTable m)  <$> ask (key @KeyName)
  opTbl   <- M.union (miOpTable m)    <$> ask (key @KeyOp)
  typeTbl <- M.union (miTypeTable m)  <$> ask (key @KeyType)
  synTbl  <- M.union (miSynTable m)   <$> ask (key @KeySyn)
  valTbl  <- M.union (miValueTable m) <$> ask (key @KeyValue)

  onames <- forM ns $ \(Loc loc n) -> do
    case S.toList <$> M.lookup n nameTbl of
      Just [(mn, bn)] -> return (Original mn bn n)
      Just qs  -> staticError $ nest 2 $ 
        vcat [ ppr loc,  
               text "Ambiguous name in the export list:" <+> ppr n,
               text "candidates are:",
               vcat (map ppr qs) ]               
      Nothing  -> staticError $ nest 2 $
        vcat [ppr loc,
              text "Unbound name in the export list:" <+> ppr n] 

  return $ restrictNames onames $ m { miNameTable = nameTbl,
                                      miOpTable = opTbl,
                                      miTypeTable = typeTbl,
                                      miSynTable = synTbl,
                                      miValueTable = valTbl }

  

-- readModule :: FilePath -> M v m ModuleInfo
-- readModule fp = do
--   -- Clear cache. 
--   modifyModuleTable (const $ M.empty)
--   -- reset emvironments. 
--   localDefinedNames (const []) $
--     localOpTable (const $ M.empty) $
--       localTypeTable (const $ M.empty) $
--         localSynTable (const $ M.empty) $
--           withImport baseModuleInfo $ 
--             readModuleWork fp 

readModule :: FilePath -> (M.Map Name v -> Bind Name -> [(Name, v)]) -> M v m (ModuleInfo v)
readModule fp interp = do
  debugPrint 1 $ text "Parsing" <+> ppr fp <+> text "..."  
  s <- liftIO $ readFile fp 
  Module currentModule exports imports decls <- either (staticError . text) return $ parseModule fp s

  debugPrint 1 $ text "Parsing Ok." 
  
  ms <- forM imports $ \(Import m is) -> do
    md <- interpModuleWork m interp
    case is of
      Nothing -> return md
      Just ns -> 
        importNames m ns md -- restrictNames (map (qualifyName m) ns) md) imports

  withImports ms $ do
    nameTable <- ask (key @KeyName)
    opTable   <- ask (key @KeyOp) 

    debugPrint 1 $ text "Renaming ..."
    debugPrint 2 $ group $
      text "w.r.t." </>
      vcat [ nest 2 (text "opTable:" <> line <> align (pprMap opTable)),
             nest 2 (text "nameMap:" <> line <> align (pprMap (M.map S.toList nameTable))) ]
    
    -- (decls', newDefinedNames, newOpTable, newDataTable, newSynTable) <-
    --        liftIO $ runDesugar mod definedNames opTable (desugarTopDecls decls)

    (renamedDecls, tyDecls, synDecls, newNames, newOpTable) <-
      liftIO $ either nameError return $ runRenaming nameTable opTable $ renameTopDecls currentModule decls
  
    -- debugPrint $ "Desugaring Ok."
    -- debugPrint $ show (D.group $ D.nest 2 $ D.text "Desugared syntax:" D.</> D.align (ppr decls'))

    -- debugPrint $ "Type checking ..."
    -- debugPrint $ show (D.text "under ty env" D.<+> pprMap tyEnv)

    debugPrint 1 $ text "Renaming Ok."

    tinfo  <- ask (key @KeyTC)
    tyEnv  <- ask (key @KeyType)
    synEnv <- ask (key @KeySyn)

    debugPrint 1 $ text "Type checking ..."
    debugPrint 2 $ text "under ty env" </> pprMap tyEnv

    (typedDecls, nts, dataDecls', typeDecls', newTypeTable, newSynTable) <-
      liftIO $ runTCWith tinfo tyEnv synEnv $ inferTopDecls renamedDecls tyDecls synDecls

    debugPrint 1 $ text "Type checking Ok." 
    debugPrint 1 $ text "Desugaring ..."
    bind <- liftIO $ runTC tinfo $ runDesugar $ desugarTopDecls typedDecls 

    debugPrint 1 $ text "Desugaring Ok."
    debugPrint 2 $ text "Desugared:" <> line <> align (vcat (map (\(x,_,e) -> ppr (x,e)) bind))


    loadPath <- ask (key @KeyLoadPath)
    let hsFile = loadPath FP.</> targetFilePath currentModule

    liftIO $ do let dir = FP.takeDirectory hsFile
                Dir.createDirectoryIfMissing True dir
                writeFile hsFile $
                  show $ toDocTop currentModule exports imports dataDecls' typeDecls' bind
    
    -- for de

    valEnv <- ask (key @KeyValue)
    let newValueEnv = interp valEnv bind 

    let newNameTable =
          let mns = [ (mn, n) | Original mn n _ <- S.toList newNames ]
          in M.fromList $
             [ (Bare n, S.singleton (mn, n)) | (mn, n) <- mns ]
             ++
             [ (Qual mn n, S.singleton (mn, n)) | (mn, n) <- mns ] 
    
    let newMod = ModuleInfo {
          miModuleName = currentModule,
          miOpTable   = newOpTable,
          miNameTable = newNameTable,
          miSynTable  = newSynTable,
          miTypeTable = foldr (uncurry M.insert) newTypeTable nts, 
          miValueTable = M.fromList newValueEnv,
          miHsFile     = hsFile
          }                

    newMod' <- case exports of
      Just es -> exportNames es newMod
      _       -> return newMod

    St.modify (M.insert currentModule newMod')
    return newMod' 
      

    -- withOpTable newOpTable $
    --   withTypeTable newDataTable $
    --     withSynTable newSynTable $ do
    --       modTbl <- getModuleTable 
    --       tyEnv  <- getTypeTable

    --       debugPrint "Type checking..."
    --       debugPrint $ show (D.text "under ty env" D.<+> pprMap tyEnv)

    --       tinfo <- getTInfo 
    --       synEnv <- getSynTable
    --       liftIO $ setEnvs tinfo tyEnv synEnv 
          
    --       nts <- liftIO $ runTC tinfo $ inferDecls decls'


    --       -- let env = foldr M.union M.empty $ map miValueTable ms
    --       env <- getValueTable 
    --       let env' = runEval (evalUDecls env decls') 

    --       let newMod = ModuleInfo {
    --             miModuleName = mod,
    --             miOpTable   = newOpTable,
    --             miNameTable = newNameTable,
    --             miSynTable  = newSynTable,
    --             miTypeTable = foldr (uncurry M.insert) newDataType nts, 
    --             miValueTable = env' 
    --             }                

    --       modifyModuleTable (const $ M.insert mod newMod modTbl)

    --       case exports of
    --         Just es ->
    --           return $ restrictNames (map (qualifyName mod) es) newMod
    --         _ ->
    --           return newMod

   where
     nameError (l, d) =
       staticError (nest 2 (ppr l </> d))
     
--      qualifyName = undefined
     -- qualifyName cm (BName n) = QName cm n
     -- qualifyName _  (QName cm n) = QName cm n 
              
  
interpModuleWork :: ModuleName -> (M.Map Name v -> Bind Name -> [(Name,v)]) -> M v m (ModuleInfo v) 
interpModuleWork mo interp = do
  modTable <- St.get
  case M.lookup mo modTable of
    Just modData -> return modData
    _            -> do 
      fp <- searchModule mo
      m <- readModule fp interp
      when (miModuleName m /= mo) $
        staticError $ text "The file" <+> ppr fp <+> text "must define module" <+> ppr mo
      return m 
      
      
               
  
  
  
