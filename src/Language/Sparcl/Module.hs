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
import Control.Monad.State 
import System.IO 

import Language.Sparcl.Pretty
import qualified Text.PrettyPrint.ANSI.Leijen as D

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
  iiValueTable  :: M.Map QName Value
  }

type ModuleTable = M.Map ModuleName ModuleInfo   
type ValueTable  = M.Map QName Value 

type M = ReaderT InterpInfo (StateT (TInfo, ModuleTable) IO) 


runM :: [FilePath] -> M a -> IO a
runM searchPath m = do 
  let ii = InterpInfo { iiSearchPath = searchPath,
                        iiTypeTable  = M.empty,
                        iiDefinedNames = [], 
                        iiSynTable   = M.empty,
                        iiOpTable    = M.empty,
                        iiValueTable = M.empty  }
  evalStateT (runReaderT (withImport baseModuleInfo m) ii) (initTInfo M.empty M.empty, M.empty)

baseModuleInfo :: ModuleInfo 
baseModuleInfo = ModuleInfo {
  miModuleName = baseModule,

  miDefinedNames = [
      conTrue, conFalse,
      nameTyBang, nameTyBool, nameTyChar, nameTyDouble,
      nameTyInt, nameTyLArr, nameTyRev, nameTyList,
      base "+", base "-", base "*"
      ], 
  
  miTypeTable = M.fromList [
      conTrue  |-> boolTy,
      conFalse |-> boolTy,
      base "+" |-> intTy -@ (intTy -@ intTy),
      base "-" |-> intTy -@ (intTy -@ intTy),
      base "*" |-> intTy -@ (intTy -@ intTy) ],
    
  miSynTable = M.empty,
  miOpTable  = M.fromList [
      base "+" |-> (Prec 60, L),
      base "-" |-> (Prec 60, L),
      base "*" |-> (Prec 70, L) ], 
               
  miValueTable = M.fromList [
      base "+" |-> intOp (+),
      base "-" |-> intOp (-),
      base "*" |-> intOp (*) ]
  }
  where
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
  Module mod exports imports decls <- either error return $ parseModule fp s

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
          (ti, modTbl) <- get
          tyEnv  <- asks iiTypeTable

          debugPrint "Type checking..."
          debugPrint $ show (D.text "under ty env" D.<+> pprMap tyEnv)
          
          synEnv <- asks iiSynTable
          let (res, ti') = runTC (ti { tiTyEnv = M.map (\t -> (Omega, t)) tyEnv, tiSyn = synEnv }) $
                           inferDecls decls'

          nts <- either (error . show) return res

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

          put (ti', M.insert mod newMod modTbl)

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
  modTable <- gets snd
  case M.lookup mod modTable of
    Just modData -> return modData
    _            -> do 
      fp <- searchModule mod
      readModule fp 
               
  
  
  
