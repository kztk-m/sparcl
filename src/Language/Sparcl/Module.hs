module Language.Sparcl.Module where

import qualified Data.Map as M
import qualified Data.Set as S

import Language.Sparcl.Untyped.Desugar.Syntax
import Language.Sparcl.Untyped.Desugar
import Language.Sparcl.Untyped.Eval
import Language.Sparcl.Typing.Typing
import Language.Sparcl.Typing.TC 

import Language.Sparcl.Untyped.Parsing 

import System.Directory as Dir
import System.FilePath as FP

import Control.Monad.Reader
import Control.Monad.State.Strict 
import System.IO 

import Language.Sparcl.Pretty
import qualified Text.PrettyPrint.ANSI.Leijen as D

import Control.Exception (Exception, throw)

data ModuleInfo = ModuleInfo {
  miModuleName :: ModuleName,
  miDefinedNames :: [QName], 
  miTypeTable  :: TypeTable,
  miSynTable   :: SynTable, 
  miOpTable    :: OpTable,
  miValueTable :: ValueTable 
  }

data InterpInfo = InterpInfo {
  iiSearchPath  :: [FilePath],
  iiDefinedNames :: [QName], 
  iiTypeTable   :: TypeTable,
  iiSynTable    :: SynTable,
  iiOpTable     :: OpTable,
  iiValueTable  :: M.Map QName Value,
  iiTInfo       :: TInfo 
  }

type ModuleTable = M.Map ModuleName ModuleInfo   
type ValueTable  = M.Map QName Value 

type M = ReaderT InterpInfo (StateT ModuleTable IO) 


data StaticException = StaticException Doc

instance Show StaticException where
  show (StaticException d) =
    show (D.red (D.text "[Error]") D.<> D.nest 2 (D.line D.<> d))

instance Exception StaticException

staticError :: Doc -> a
staticError d = throw (StaticException d)


runMTest :: [FilePath] -> M a -> IO a
runMTest searchPath m = do
  tinfo <- initTInfo
  let ii = initInterpInfo tinfo searchPath 
  evalStateT (runReaderT (withImport baseModuleInfo m) ii) M.empty

runM :: [FilePath] -> TInfo -> M a -> IO a
runM searchPath tinfo m = do
  let ii = initInterpInfo tinfo searchPath 
  (res, _) <- runStateT (runReaderT (withImport baseModuleInfo m) ii) M.empty
  return res

initInterpInfo :: TInfo -> [FilePath] -> InterpInfo
initInterpInfo tinfo searchPath = 
  InterpInfo { iiSearchPath = searchPath,
               iiTypeTable  = M.empty,
               iiDefinedNames = [], 
               iiSynTable   = M.empty,
               iiOpTable    = M.empty,
               iiValueTable = M.empty,
               iiTInfo      = tinfo }
baseModuleInfo :: ModuleInfo 
baseModuleInfo = ModuleInfo {
  miModuleName = baseModule,

  miDefinedNames = [
      conTrue, conFalse,
      nameTyBang, nameTyBool, nameTyChar, nameTyDouble,
      nameTyInt, nameTyLArr, nameTyRev, nameTyList,
      base "+", base "-", base "*",
      eqInt, leInt, ltInt,
      eqChar, leChar, ltChar
      ], 
  
  miTypeTable = M.fromList [
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
    
  miSynTable = M.empty,
  miOpTable  = M.fromList [
      base "+" |-> (Prec 60, L),
      base "-" |-> (Prec 60, L),
      base "*" |-> (Prec 70, L) ], 
               
  miValueTable = M.fromList [
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
  

debugPrint :: String -> M ()
debugPrint = lift . lift . hPutStrLn stderr 

withOpTable :: OpTable -> M r -> M r
withOpTable newOpTable m = do
  opTable <- asks iiOpTable
  local (\ii -> ii { iiOpTable = M.union newOpTable opTable }) m

withTypeTable :: TypeTable -> M r -> M r
withTypeTable newTbl m = do
  tbl <- asks iiTypeTable
  local (\ii -> ii { iiTypeTable = M.union newTbl tbl }) m

withSynTable :: SynTable -> M r -> M r 
withSynTable newTbl m = do
  tbl <- asks iiSynTable
  local (\ii -> ii { iiSynTable = M.union newTbl tbl }) m

withValueTable :: ValueTable -> M r -> M r 
withValueTable newTbl m = do
  tbl <- asks iiValueTable
  local (\ii -> ii { iiValueTable = M.union newTbl tbl }) m

withDefinedNames :: [QName] -> M r -> M r
withDefinedNames newTbl m = do
  tbl <- asks iiDefinedNames
  local (\ii -> ii { iiDefinedNames = newTbl ++ tbl}) m 


withImport :: ModuleInfo -> M r -> M r 
withImport mod m = do
  let opTbl  = miOpTable  mod
  let tyTbl  = miTypeTable mod
  let synTbl = miSynTable  mod
  let defTbl = miDefinedNames mod
  let valTbl = miValueTable mod
  withOpTable opTbl $ withTypeTable tyTbl $ withSynTable synTbl $ withDefinedNames defTbl $ withValueTable valTbl m 
  

withImports :: [ModuleInfo] -> M r -> M r
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
      mi' = mi { miModuleName = mn,
                 miOpTable   = M.restrictKeys (miOpTable mi) ns',
                 miTypeTable = M.restrictKeys (miTypeTable mi) ns',
                 miSynTable  = M.restrictKeys (miSynTable mi) ns',
                 miValueTable = M.restrictKeys (miValueTable mi) ns' }
  in mi' 
                 

searchModule :: ModuleName -> M FilePath
searchModule mod = do
  dirs <- asks iiSearchPath
  let file = moduleNameToFilePath mod 
  let searchFiles = [ dir FP.</> file | dir <- dirs ]
  fs <- lift $ mapM (lift . Dir.doesFileExist) searchFiles
  case map fst $ filter snd $ zip searchFiles fs of
    fp:_ -> return fp 
    _    -> error $ "ERROR: Cannot find module " ++ foldr1 (\a b -> a ++ "." ++ b) mod

readModule :: FilePath -> M ModuleInfo
readModule fp = do
  debugPrint $ "Parsing " ++ fp ++ " ..." 
  s <- lift $ lift $ readFile fp 
  Module mod exports imports decls <- either (staticError . D.text) return $ parseModule fp s

  debugPrint $ "Parsing Ok." 

  
  ms <- mapM (\(Import m is) ->
                 do md <- interpModule m
                    case is of
                      Nothing -> return md
                      Just ns -> 
                        return $ restrictNames (map (qualifyName m) ns) md) imports

  withImports ms $ do 
    definedNames <- asks iiDefinedNames
    opTable      <- asks iiOpTable

    debugPrint $ "Desugaring ..."
    debugPrint $ show $ D.group $ D.nest 2 $ D.text "w.r.t. opTable: " D.<$> pprMap opTable
    
    (decls', newDefinedNames, newOpTable, newDataTable, newSynTable) <-
           lift $ lift $ runDesugar mod definedNames opTable (desugarTopDecls decls)

    debugPrint $ "Desugaring Ok."
    debugPrint $ show (D.group $ D.nest 2 $ D.text "Desugared syntax:" D.</> D.align (ppr decls'))

    withOpTable newOpTable $
      withTypeTable newDataTable $
        withSynTable newSynTable $ do
          modTbl <- get
          tyEnv  <- asks iiTypeTable

          debugPrint "Type checking..."
          debugPrint $ show (D.text "under ty env" D.<+> pprMap tyEnv)

          tinfo <- asks iiTInfo 
          synEnv <- asks iiSynTable
          liftIO $ setEnvs tinfo tyEnv synEnv 
          
          res <- liftIO $ runTC tinfo $ inferDecls decls'

          nts <- either staticError return res

          -- let env = foldr M.union M.empty $ map miValueTable ms
          env <- asks iiValueTable 
          let env' = runEval (evalUDecls env decls') 

          let newMod = ModuleInfo {
                miModuleName = mod, 
                  miOpTable    = newOpTable,
                  miDefinedNames = newDefinedNames, 
                  miSynTable   = newSynTable,
                  miTypeTable  = foldr (uncurry M.insert) ({- M.mapKeys (qualifyName mod) -} newDataTable) nts,
                  miValueTable = -- M.mapKeys (qualifyName mod) $
                                 env' 
                }                

          put (M.insert mod newMod modTbl)

          case exports of
            Just es -> 
              return $ restrictNames (map (qualifyName mod) es) newMod
            _ ->
              return newMod

   where
     qualifyName cm (BName n) = QName cm n
     qualifyName _  (QName cm n) = QName cm n 
              
  
interpModule :: ModuleName -> M ModuleInfo 
interpModule mod = do
  modTable <- get
  case M.lookup mod modTable of
    Just modData -> return modData
    _            -> do 
      fp <- searchModule mod
      readModule fp 
               
  
  
  
