{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE TypeApplications #-}

module Language.Sparcl.Module (
  ModuleContext (..),
  ModuleInfo (..),
  Loader (..),
  runLoader,
  runLoaderWith,
  readModule,
  baseModuleInfo,
  typeOfExpressionStr,
  valueOfExpressionStr,
) where

import qualified Data.Map as M
import qualified Data.Set as S

import Data.Function (on)
import Data.Ratio ((%))

import System.Directory as Dir (doesFileExist)
import qualified System.FilePath as FP ((<.>), (</>))

import Control.Monad (forM, when)
import Control.Monad.IO.Class

import Language.Sparcl.Pretty hiding ((<$>))

import Language.Sparcl.Core.Syntax
import Language.Sparcl.Desugar
import Language.Sparcl.Exception
import Language.Sparcl.Multiplicity
import Language.Sparcl.Renaming
import Language.Sparcl.Surface.Syntax (Assoc (..), Prec (..))
import qualified Language.Sparcl.Surface.Syntax as Surf
import Language.Sparcl.Typing.TCMonad
import Language.Sparcl.Typing.Type
import Language.Sparcl.Typing.Typing
import Language.Sparcl.Value

import Control.DeepSeq (NFData (..))
import Control.Exception (evaluate)
import Control.Monad.Reader (MonadReader (local), ReaderT (..), asks)
import Data.IORef (IORef, modifyIORef', newIORef, readIORef)
import Language.Sparcl.DebugPrint
import Language.Sparcl.Pass (Pass (..))
import Language.Sparcl.Surface.Parsing

data ModuleInfo v = ModuleInfo
  { miModuleName :: !ModuleName
  , miModuleContext :: ModuleContext v
  }

data ModuleContext v = ModuleContext
  { mcNameTable :: !NameTable
  , mcOpTable :: !OpTable
  , mcTypeTable :: !TypeTable
  , mcConTable :: !CTypeTable
  , mcSynTable :: !SynTable
  , mcValueTable :: !(M.Map Name v)
  }

instance Semigroup (ModuleContext v) where
  m1 <> m2 =
    ModuleContext
      { mcNameTable = M.unionWith S.union (mcNameTable m1) (mcNameTable m2)
      , mcOpTable = M.union (mcOpTable m1) (mcOpTable m2)
      , mcTypeTable = M.union (mcTypeTable m1) (mcTypeTable m2)
      , mcConTable = M.union (mcConTable m1) (mcConTable m2)
      , mcSynTable = M.union (mcSynTable m1) (mcSynTable m2)
      , mcValueTable = M.union (mcValueTable m1) (mcValueTable m2)
      }

emptyModuleContext :: ModuleContext v
emptyModuleContext = ModuleContext{mcNameTable = M.empty, mcOpTable = M.empty, mcTypeTable = M.empty, mcConTable = M.empty, mcSynTable = M.empty, mcValueTable = M.empty}

instance Monoid (ModuleContext v) where
  mempty = emptyModuleContext

-- for caching.
type ModuleTable v = M.Map ModuleName (ModuleInfo v)

data LoadContext v = LoadContext
  { lcSearchPath :: ![FilePath]
  , lcDebugLevel :: !Int
  , lcTC :: !TypingContext
  , lcModuleContext :: !(ModuleContext v)
  , lcModuleTable :: !(IORef (ModuleTable v))
  }

-- type M v m a = (MonadModule v m) => St.StateT (ModuleTable v) m a
newtype Loader v a = Loader (ReaderT (LoadContext v) IO a)
  deriving newtype (Functor, Applicative, Monad, MonadIO, MonadReader (LoadContext v))

getModuleTable :: Loader v (ModuleTable v)
getModuleTable = do
  ref <- asks lcModuleTable
  liftIO $ readIORef ref

updateModuleTable :: (ModuleTable v -> ModuleTable v) -> Loader v ()
updateModuleTable upd = do
  ref <- asks lcModuleTable
  liftIO $ modifyIORef' ref upd
instance MonadDebug (Loader v) where
  askDebugLevel = asks lcDebugLevel

runLoader :: [FilePath] -> Int -> TypingContext -> Loader Value a -> IO a
runLoader sp dl tc = runLoaderWith sp dl tc (miModuleContext baseModuleInfo)

runLoaderWith :: [FilePath] -> Int -> TypingContext -> ModuleContext v -> Loader v a -> IO a
runLoaderWith sp dl tc mc (Loader m) = do
  r <- newIORef M.empty
  runReaderT m (LoadContext{lcSearchPath = sp, lcDebugLevel = dl, lcTC = tc, lcModuleContext = mc, lcModuleTable = r})

baseModuleInfo :: ModuleInfo Value
baseModuleInfo =
  ModuleInfo
    { miModuleName = baseModule
    , miModuleContext =
        ModuleContext
          { mcNameTable =
              M.fromListWith S.union $
                [(Bare n, S.fromList [(mn, n)]) | Original mn n _ <- names]
                  ++ [(Qual mn n, S.fromList [(mn, n)]) | Original mn n _ <- names]
          , mcOpTable = opTable
          , mcConTable = conTable
          , mcTypeTable = typeTable
          , mcSynTable = synTable
          , mcValueTable = valueTable
          }
    }
  where
    eqInt = base "eqInt"
    leInt = base "leInt"
    ltInt = base "ltInt"
    eqChar = base "eqChar"
    leChar = base "leChar"
    ltChar = base "ltChar"

    eqRational = base "eqRational"
    leRational = base "leRational"
    ltRational = base "ltRational"

    unInt (VLit (LitInt n)) = n
    unInt _ = cannotHappen $ text "Not an integer"
    unChar (VLit (LitChar n)) = n
    unChar _ = cannotHappen $ text "Not a character"
    unRat (VLit (LitRational n)) = n
    unRat _ = cannotHappen $ text "Not a rational"

    conTable =
      M.fromList
        [ conTrue |-> ConTy [] [] [] [] boolTy
        , conFalse |-> ConTy [] [] [] [] boolTy
        , base "U"
            |-> let a = BoundTv (Local $ User "a")
                in  ConTy [a] [] [] [(TyVar a, omega)] (TyCon (base "Un") [TyVar a])
        , base "MkMany"
            |-> let [a, p] = map (BoundTv . Local . User) ["a", "p"]
                in  ConTy [p, a] [] [] [(TyVar a, TyVar p)] (TyCon (base "Many") [TyVar p, TyVar a])
        ]

    typeTable =
      M.fromList
        [ base "+" |-> intTy -@ (intTy -@ intTy)
        , base "-" |-> intTy -@ (intTy -@ intTy)
        , base "*" |-> intTy -@ (intTy -@ intTy)
        , base "%" |-> intTy -@ (intTy -@ rationalTy)
        , -- operators on rationals
          base "+%" |-> rationalTy -@ (rationalTy -@ rationalTy)
        , base "-%" |-> rationalTy -@ (rationalTy -@ rationalTy)
        , base "*%" |-> rationalTy -@ (rationalTy -@ rationalTy)
        , base "/%" |-> rationalTy -@ (rationalTy -@ rationalTy)
        , -- In future, we should use type classes.
          eqInt |-> intTy -@ intTy -@ boolTy
        , leInt |-> intTy -@ intTy -@ boolTy
        , ltInt |-> intTy -@ intTy -@ boolTy
        , eqChar |-> charTy -@ charTy -@ boolTy
        , leChar |-> charTy -@ charTy -@ boolTy
        , ltChar |-> charTy -@ charTy -@ boolTy
        , eqRational |-> rationalTy -@ rationalTy -@ boolTy
        , leRational |-> rationalTy -@ rationalTy -@ boolTy
        , ltRational |-> rationalTy -@ rationalTy -@ boolTy
        , nameTyInt |-> typeKi
        , nameTyBool |-> typeKi
        , nameTyChar |-> typeKi
        , nameTyRational |-> typeKi
        , base "Un" |-> typeKi `arrKi` typeKi
        ]

    synTable = M.empty

    opTable =
      M.fromList
        [ base "+" |-> (Prec 60, L)
        , base "-" |-> (Prec 60, L)
        , base "*" |-> (Prec 70, L)
        , base "%" |-> (Prec 70, L)
        , base "+%" |-> (Prec 60, L)
        , base "-%" |-> (Prec 60, L)
        , base "*%" |-> (Prec 70, L)
        , base "/%" |-> (Prec 70, L)
        ]

    valueTable =
      M.fromList
        [ base "+" |-> intOp (+)
        , base "-" |-> intOp (-)
        , base "*" |-> intOp (*)
        , base "%" |-> (VFun $ \(VLit (LitInt n)) -> return $ VFun $ \(VLit (LitInt m)) -> return $ VLit (LitRational (fromIntegral n % fromIntegral m)))
        , base "+%" |-> ratOp (+)
        , base "-%" |-> ratOp (-)
        , base "*%" |-> ratOp (*)
        , base "/%" |-> ratOp (/)
        , eqInt |-> (VFun $ \n -> return $ VFun $ \m -> return $ fromBool $ ((==) `on` unInt) n m)
        , leInt |-> (VFun $ \n -> return $ VFun $ \m -> return $ fromBool $ ((<=) `on` unInt) n m)
        , ltInt |-> (VFun $ \n -> return $ VFun $ \m -> return $ fromBool $ ((<) `on` unInt) n m)
        , eqChar |-> (VFun $ \c -> return $ VFun $ \d -> return $ fromBool $ ((==) `on` unChar) c d)
        , leChar |-> (VFun $ \c -> return $ VFun $ \d -> return $ fromBool $ ((<=) `on` unChar) c d)
        , ltChar |-> (VFun $ \c -> return $ VFun $ \d -> return $ fromBool $ ((<) `on` unChar) c d)
        , eqRational |-> (VFun $ \n -> return $ VFun $ \m -> return $ fromBool $ ((==) `on` unRat) n m)
        , leRational |-> (VFun $ \n -> return $ VFun $ \m -> return $ fromBool $ ((<=) `on` unRat) n m)
        , ltRational |-> (VFun $ \n -> return $ VFun $ \m -> return $ fromBool $ ((<) `on` unRat) n m)
        ]

    names = M.keys typeTable ++ M.keys conTable

    fromBool True = VCon conTrue []
    fromBool False = VCon conFalse []

    intOp f = VFun $ \(VLit (LitInt n)) -> return $ VFun $ \(VLit (LitInt m)) -> return (VLit (LitInt (f n m)))
    ratOp f = VFun $ \(VLit (LitRational n)) -> return $ VFun $ \(VLit (LitRational m)) -> return (VLit (LitRational (f n m)))

    rationalTy = TyCon (base "Rational") []
    intTy = TyCon (base "Int") []
    base n = nameInBase (User n)
    a |-> b = (a, b)
    infix 0 |->

withImport :: ModuleInfo v -> Loader v r -> Loader v r
withImport mo = local $ \lc ->
  let mc = lcModuleContext lc
  in  lc{lcModuleContext = miModuleContext mo <> mc}

withImports :: [ModuleInfo v] -> Loader v r -> Loader v r
withImports ms comp =
  foldr withImport comp ms

ext :: String
ext = "sparcl"

moduleNameToFilePath :: ModuleName -> FilePath
moduleNameToFilePath (ModuleName mo) = go mo
  where
    go = go2' id

    go2' ds [] = ds "" FP.<.> ext
    go2' ds (c : cs)
      | c == '.' = ds "" FP.</> go2' id cs
      | otherwise = go2' (ds . (c :)) cs

--  (foldr1 (FP.</>) mn) FP.<.> ext

restrictNames :: [Name] -> ModuleInfo v -> ModuleInfo v
restrictNames ns mi =
  mi
    { miModuleContext =
        ModuleContext
          { mcNameTable = M.mapMaybe conv (mcNameTable mc)
          , mcOpTable = restrict (mcOpTable mc)
          , mcTypeTable = restrict (mcTypeTable mc)
          , mcConTable = restrict (mcConTable mc)
          , mcSynTable = restrict (mcSynTable mc)
          , mcValueTable = restrict (mcValueTable mc)
          }
    }
  where
    mc = miModuleContext mi
    ns' = S.fromList ns

    restrict :: M.Map Name a -> M.Map Name a
    restrict x = M.restrictKeys x ns'

    mnsI = S.fromList [(mn, n) | Original mn n _ <- ns]

    conv mns =
      let res = S.intersection mns mnsI
      in  if S.null res
            then
              Nothing
            else
              Just res

searchModule :: ModuleName -> Loader v FilePath
searchModule mo = do
  dirs <- asks lcSearchPath
  let file = moduleNameToFilePath mo
  let searchFiles = [dir FP.</> file | dir <- dirs]
  fs <- liftIO $ mapM Dir.doesFileExist searchFiles
  case map fst $ filter snd $ zip searchFiles fs of
    fp : _ -> return fp
    [] -> do
      vlevel <- askDebugLevel
      staticError $ text "Cannot find module:" <+> ppr mo <> reportSearchFiles vlevel searchFiles
  where
    reportSearchFiles vlevel sf
      | vlevel < 2 = mempty
      | otherwise =
          line <> text "Files searched:" <+> align (vcat (map ppr sf))

importNames :: ModuleName -> [Loc SurfaceName] -> ModuleInfo v -> Loader v (ModuleInfo v)
importNames mn ns m = do
  onames <- forM ns $ \(Loc loc n) ->
    case n of
      Bare bn -> return (Original mn bn (Bare bn))
      _ ->
        staticError $
          nest 2 $
            vcat
              [ ppr loc
              , text "Qualified names in the import list:" <+> ppr n
              ]

  return $ restrictNames onames m

exportNames :: [Loc SurfaceName] -> ModuleInfo v -> Loader v (ModuleInfo v)
exportNames ns m = do
  -- In general, ns can contain names that come from other modules.
  -- Then, exporting is done by filtering all the available names.

  nameTbl <- M.union (mcNameTable $ miModuleContext m) <$> asks (mcNameTable . lcModuleContext)
  opTbl <- M.union (mcOpTable $ miModuleContext m) <$> asks (mcOpTable . lcModuleContext)
  typeTbl <- M.union (mcTypeTable $ miModuleContext m) <$> asks (mcTypeTable . lcModuleContext)
  conTbl <- M.union (mcConTable $ miModuleContext m) <$> asks (mcConTable . lcModuleContext)
  synTbl <- M.union (mcSynTable $ miModuleContext m) <$> asks (mcSynTable . lcModuleContext)
  valTbl <- M.union (mcValueTable $ miModuleContext m) <$> asks (mcValueTable . lcModuleContext)

  onames <- forM ns $ \(Loc loc n) ->
    case S.toList <$> M.lookup n nameTbl of
      Just [(mn, bn)] -> return (Original mn bn n)
      Just qs ->
        staticError $
          nest 2 $
            vcat
              [ ppr loc
              , text "Ambiguous name in the export list:" <+> ppr n
              , text "candidates are:"
              , vcat (map ppr qs)
              ]
      Nothing ->
        staticError $
          nest 2 $
            vcat
              [ ppr loc
              , text "Unbound name in the export list:" <+> ppr n
              ]

  return $
    restrictNames onames $
      m
        { miModuleContext =
            ModuleContext
              { mcNameTable = nameTbl
              , mcOpTable = opTbl
              , mcTypeTable = typeTbl
              , mcConTable = conTbl
              , mcSynTable = synTbl
              , mcValueTable = valTbl
              }
        }

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

readExp :: String -> Loader v (Loader v (Exp Name), Ty)
readExp str = do
  nameTable <- asks (mcNameTable . lcModuleContext)
  opTable <- asks (mcOpTable . lcModuleContext)

  debugPrint 1 $ text "Parsing expression..."
  parsedExp <- either (staticError . text) return $ parseExp' "<*repl*>" str
  debugPrint 1 $ text "Parsing Ok."
  debugPrint 1 $ text "Renaming expression..."
  (renamedExp, _) <- either nameError return $ runRenaming nameTable opTable (renameExp 0 M.empty parsedExp)
  debugPrint 1 $ text "Renaming Ok."

  typeTable <- asks (mcTypeTable . lcModuleContext)
  conTable <- asks (mcConTable . lcModuleContext)
  synTable <- asks (mcSynTable . lcModuleContext)

  debugPrint 1 $ text "Type checking expression..."
  debugPrint 3 $
    text "under:"
      <+> align
        ( vcat
            [ text "tyenv: " <+> align (pprMap typeTable)
            , text "synenv:" <+> align (pprMap synTable)
            ]
        )

  -- liftIO $ setEnvs tinfo typeTable synTable
  (typedExp, ty) <- do
    tc <- asks lcTC
    liftIO $ execTCWith tc conTable typeTable synTable $ inferExp renamedExp
  debugPrint 1 $ text "Type checking Ok."
  ty' <- liftIO $ evaluate ty

  let eComp = do
        debugPrint 1 $ text "Desugaring expression..."
        desugaredExp <- do
          tc <- asks lcTC
          liftIO $ execTC tc $ runDesugar $ desugarExp typedExp
        debugPrint 1 $ text "Desugaring Ok."
        debugPrint 2 $ nest 2 $ vsep [text "Desugared:", align (ppr desugaredExp)]

        liftIO $ evaluate desugaredExp

  return (eComp, ty')

typeOfExpressionStr :: String -> Loader v Ty
typeOfExpressionStr s = do
  (_, ty) <- readExp s
  pure ty

valueOfExpressionStr :: String -> (M.Map Name v -> Bind Name -> IO [(Name, v)]) -> Loader v v
valueOfExpressionStr s interp = do
  (mExp, ty) <- readExp s
  e <- mExp

  valEnv <- asks (mcValueTable . lcModuleContext)
  let name = Generated (-1) CodeGen
  res <- liftIO $ interp valEnv [(name, ty, e)]
  case res of
    [(_, v)] -> pure v
    _ -> rtError $ text "internal error in evaluation"

interpDecls ::
  (NFData v) =>
  Maybe ModuleName
  -> Surf.Decls 'Parsing (Loc (Surf.TopDecl 'Parsing))
  -> (M.Map Name v -> Bind Name -> IO [(Name, v)])
  -> Loader v (ModuleInfo v)
interpDecls mCurrentModuleName decls interp = do
  let currentModule
        | Just n <- mCurrentModuleName = n
        | otherwise = ModuleName "<nowhere>"

  nameTable <- asks (mcNameTable . lcModuleContext)
  opTable <- asks (mcOpTable . lcModuleContext)

  debugPrint 1 $ text "Renaming ..."
  debugPrint 2 $
    group $
      text "w.r.t."
        </> vcat
          [ nest 2 (text "opTable:" <> line <> align (pprMap opTable))
          , nest 2 (text "nameMap:" <> line <> align (pprMap (M.map S.toList nameTable)))
          ]

  -- (decls', newDefinedNames, newOpTable, newDataTable, newSynTable) <-
  --        liftIO $ runDesugar mod definedNames opTable (desugarTopDecls decls)

  (renamedDecls, tyDecls, synDecls, newNames, newOpTable) <-
    liftIO $ either nameError return $ runRenaming nameTable opTable $ renameTopDecls currentModule decls

  -- debugPrint $ "Desugaring Ok."
  -- debugPrint $ show (D.group $ D.nest 2 $ D.text "Desugared syntax:" D.</> D.align (ppr decls'))

  -- debugPrint $ "Type checking ..."
  -- debugPrint $ show (D.text "under ty env" D.<+> pprMap tyEnv)

  debugPrint 1 $ text "Renaming Ok."
  debugPrint 2 $ ppr renamedDecls

  tyEnv <- asks (mcTypeTable . lcModuleContext)
  conEnv <- asks (mcConTable . lcModuleContext)
  synEnv <- asks (mcSynTable . lcModuleContext)

  debugPrint 1 $ text "Type checking ..."
  debugPrint 2 $ text "under ty env" </> pprMap tyEnv

  (typedDecls, nts, _dataDecls', _typeDecls', newCTypeTable, newSynTable) <- do
    tc <- asks lcTC
    liftIO $ execTCWith tc conEnv tyEnv synEnv $ inferTopDecls renamedDecls tyDecls synDecls

  debugPrint 1 $ text "Type checking Ok."
  debugPrint 1 $ text "Desugaring ..."
  bind <- do
    tc <- asks lcTC
    liftIO $ execTC tc $ runDesugar $ desugarTopDecls typedDecls

  debugPrint 1 $ text "Desugaring Ok."
  debugPrint 2 $ text "Desugared:" <> line <> align (vcat (map (\(x, _, e) -> ppr (x, e)) bind))

  -- loadPath <- ask (key @KeyLoadPath)
  -- let hsFile = loadPath FP.</> targetFilePath currentModule

  -- liftIO $ do let dir = FP.takeDirectory hsFile
  --             Dir.createDirectoryIfMissing True dir
  --             writeFile hsFile $
  --               show $ toDocTop currentModule exports imports dataDecls' typeDecls' bind

  -- for de

  valEnv <- asks (mcValueTable . lcModuleContext)
  newValueEnv <- liftIO $ interp valEnv bind
  let !() = rnf $ map snd newValueEnv

  let newNameTable =
        let mns = [(mn, n) | Original mn n _ <- S.toList newNames]
        in  M.fromList $
              [(Bare n, S.singleton (mn, n)) | (mn, n) <- mns]
                ++ [(Qual mn n, S.singleton (mn, n)) | (mn, n) <- mns]

  let newMod =
        ModuleInfo
          { miModuleName = currentModule
          , miModuleContext =
              ModuleContext
                { mcOpTable = newOpTable
                , mcNameTable = newNameTable
                , mcSynTable = newSynTable
                , mcTypeTable = M.fromList nts
                , mcConTable = newCTypeTable
                , mcValueTable = M.fromList newValueEnv
                }
          }
  pure newMod

nameError :: (Pretty t) => (t, Doc) -> a
nameError (l, d) = staticError (nest 2 (ppr l </> d))

readModule :: (NFData v) => FilePath -> (M.Map Name v -> Bind Name -> IO [(Name, v)]) -> Loader v (ModuleInfo v)
readModule fp interp = do
  debugPrint 1 $ text "Parsing" <+> ppr fp <+> text "..."
  s <- liftIO $ readFile fp
  Module currentModule exports imports decls <- either (staticError . text) return $ parseModule fp s

  debugPrint 1 $ text "Parsing Ok."
  debugPrint 2 $ ppr decls

  ms <- forM imports $ \(Import m is) -> do
    md <- interpModuleWork m interp
    case is of
      Nothing -> return md
      Just ns ->
        importNames m ns md -- restrictNames (map (qualifyName m) ns) md) imports
  withImports ms $ do
    newMod <- interpDecls (Just currentModule) decls interp
    newMod' <- case exports of
      Just es -> exportNames es newMod
      Nothing -> return newMod

    updateModuleTable (M.insert currentModule newMod')
    return newMod'

interpModuleWork :: (NFData v) => ModuleName -> (M.Map Name v -> Bind Name -> IO [(Name, v)]) -> Loader v (ModuleInfo v)
interpModuleWork mo interp = do
  modTable <- getModuleTable
  case M.lookup mo modTable of
    Just modData -> return modData
    Nothing -> do
      fp <- searchModule mo
      m <- readModule fp interp
      when (miModuleName m /= mo) $
        staticError $
          text "The file" <+> ppr fp <+> text "must define module" <+> ppr mo
      return m
