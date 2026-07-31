{-# LANGUAGE CPP #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -fprint-potential-instances #-}

module Language.Sparcl.REPL (startREPL, VerbosityLevel) where

import Control.DeepSeq
import Control.Exception (
  IOException,
  SomeException,
  evaluate,
 )
import Control.Monad (join, liftM2)
import Control.Monad.Catch
import Control.Monad.IO.Class
import qualified Control.Monad.Reader as Rd
import Control.Monad.Trans (MonadTrans, lift)
import Data.Char (isSpace)
import Data.IORef
import Data.List (isPrefixOf)
import qualified Data.Map as M
import Data.Maybe (fromMaybe)
import qualified Data.Set as S
import Data.Time.Clock (getCurrentTime)

-- import qualified Language.Haskell.Interpreter    as Hint
import qualified Language.Haskell.TH as TH
import qualified System.Console.Haskeline as HL
import System.Directory (
  getCurrentDirectory,
  getHomeDirectory,
 )
import qualified System.FilePath as FP ((</>))
import System.IO (stdout)

import Control.Monad.Reader (asks, local)
import Language.Sparcl.Command
import Language.Sparcl.Core.Syntax hiding (REPL)
import Language.Sparcl.DebugPrint
import Language.Sparcl.Eval
import Language.Sparcl.Exception
import Language.Sparcl.Module
import Language.Sparcl.Pretty hiding ((<$>))
import Language.Sparcl.Typing.TCMonad
import Language.Sparcl.Value

-- import Data.Coerce

data Conf
  = Conf
  { confSearchPath :: ![FilePath]
  , confLoadPath :: !FilePath
  , confCurrentDir :: !FilePath
  , confVerbosity :: !Int
  , confLastLoad :: !(Maybe FilePath)
  , confTC :: !TypingContext
  , confModuleContext :: !(IORef (ModuleContext Value))
  }

-- To avoid orphan instances
newtype MyInputT m a = MyInputT {runMyInputT :: HL.InputT m a}
  deriving (Functor, Applicative, Monad, MonadIO, MonadTrans)
#if MIN_VERSION_haskeline(0,8,0)
  deriving (MonadThrow, MonadCatch, MonadMask)
#else
  deriving HL.MonadException
#endif

#if !MIN_VERSION_haskeline(0,8,0)
instance HL.MonadException m => MonadThrow (MyInputT m) where
  throwM = HL.throwIO

instance HL.MonadException m => MonadCatch (MyInputT m) where
  catch = HL.catch

-- FIXME: I am not sure the following implementation is OK or not.
instance (HL.MonadException m) => MonadMask (MyInputT m) where
  mask k = HL.controlIO $ \(HL.RunIO run) -> liftIO $ mask' $ \restore ->
    run $ k (join . liftIO . restore . run)
    where
      mask' = mask @IO

  uninterruptibleMask k = HL.controlIO $ \(HL.RunIO run) -> liftIO $ uninterruptibleMask' $ \restore ->
    run $ k (join . liftIO . restore . run)
    where
      uninterruptibleMask' = uninterruptibleMask @IO

  generalBracket before after comp =
    HL.controlIO $ \(HL.RunIO run) -> uncurry (liftM2 (,)) <$>
                     generalBracket' (run before)
                             (\ma me -> run (do { a <- ma; e <- c2c me; after a e}))
                             (\ma -> run (ma >>= comp))
    where
      c2c :: forall mm b. Monad mm => ExitCase (mm b) -> mm (ExitCase b)
      c2c (ExitCaseSuccess mb)  =
        ExitCaseSuccess <$> mb
      c2c (ExitCaseException e) = return (ExitCaseException e)
      c2c ExitCaseAbort         = return ExitCaseAbort

      generalBracket' :: IO a -> (a -> ExitCase b -> IO c) -> (a -> IO b) -> IO (b, c)
      generalBracket' = generalBracket
#endif

-- newtype REPL a = REPL { unREPL :: Rd.ReaderT Conf (Hint.InterpreterT (MyInputT IO)) a }
newtype REPL a = REPL {unREPL :: Rd.ReaderT Conf (MyInputT IO) a}
  deriving
    ( Functor
    , Applicative
    , Monad
    , MonadIO
    , Rd.MonadReader Conf
    , MonadThrow
    , MonadCatch
    , MonadMask
    )

instance MonadDebug REPL where
  askDebugLevel = asks confVerbosity

-- instance Hint.MonadInterpreter REPL where
--   fromSession s = REPL $ lift (Hint.fromSession s)
--   modifySessionRef s f = REPL $ lift (Hint.modifySessionRef s f)
--   runGhc c = REPL $ lift (Hint.runGhc c)

runREPL :: HL.Settings IO -> Conf -> REPL a -> IO a
runREPL setting conf comp = do
  HL.runInputT setting $ runMyInputT $ Rd.runReaderT (unREPL $ resetModule >> comp) conf

-- let rethrow :: (MonadThrow m, Exception e) => m (Either e a) -> m a
--     rethrow m = m >>= either throwM return
-- HL.runInputT setting $ runMyInputT $ rethrow $ Hint.runInterpreter $ Rd.runReaderT (unREPL $ resetModule >> comp) conf

type VerbosityLevel = Int

initConf :: IO Conf
initConf = do
  tinfo <- initTypingContext
  -- refNt <- newIORef M.empty
  -- refOt <- newIORef M.empty
  -- refSt <- newIORef M.empty
  -- refTt <- newIORef M.empty
  -- refCt <- newIORef M.empty
  -- refVt <- newIORef M.empty
  refMC <- newIORef mempty

  return $
    Conf
      { confSearchPath = ["."]
      , confLoadPath = ".sparcl"
      , confCurrentDir = "."
      , confVerbosity = 0
      , confLastLoad = Nothing
      , confTC = tinfo
      , confModuleContext = refMC
      }

localLastLoad :: FilePath -> REPL r -> REPL r
localLastLoad fp =
  Rd.local (\conf -> conf{confLastLoad = Just fp})

-- liftIO $ modifyIORef ref $ \conf -> conf { confLastLoad = Just fp }

-- getConf :: REPL Conf
-- getConf = do
--   ref <- ask
--   liftIO $ readIORef ref

replCompletion :: IORef (ModuleContext v) -> HL.CompletionFunc IO
replCompletion cref (curr0, rest0) =
  case checkLoadMode curr0 of
    Just (prefix, sp, r) -> do
      (s, cs) <- HL.completeFilename (reverse r, rest0)
      return (s ++ reverse (prefix ++ sp), cs)
    Nothing ->
      completeIDs (curr0, rest0)
  where
    completeIDs :: HL.CompletionFunc IO
    completeIDs (curr, rest) =
      HL.completeWord Nothing " \t\n\r" f (curr, rest)
      where
        f :: String -> IO [HL.Completion]
        f str = do
          names <- M.keys . mcNameTable <$> readIORef cref
          return $ map HL.simpleCompletion $ filter (str `isPrefixOf`) $ commands curr ++ makeNameStrings names

        makeNameStrings :: [SurfaceName] -> [String]
        makeNameStrings ns =
          S.toList
            ( S.fromList
                ( [s | Bare (User s) <- ns]
                    ++ [s | (_, s) <- qualified]
                )
            )
            ++ [m ++ "." ++ s | (m, s) <- qualified]
          where
            qualified = [(m, n) | Qual (ModuleName m) (User n) <- ns]

        commands :: String -> [String]
        commands s
          | all (not . isSpace) s
              && not (null s)
              && last s == ':' =
              commandStrings
          | otherwise = []

        commandStrings =
          [s | NoArgCommand s _ _ <- commandSpec]
            ++ [s | StringCommand s _ _ _ <- commandSpec]

    -- check whether the input is in the form of "... daol:"
    checkLoadMode :: String -> Maybe (String, String, String)
    checkLoadMode = check . parse . reverse
      where
        -- split "foo  bar baz" to "foo", "  ", "bar baz"
        parse s =
          let (w1, rest) = break isSpace s
              (sp, w2) = span isSpace rest
          in  (w1, sp, w2)

        check (w1, sp, w2)
          | isLoadPrefix w1 && not (null sp) = Just (w1, sp, w2)
          | otherwise = Nothing

        isLoadPrefix [] = False
        isLoadPrefix [_] = False
        isLoadPrefix str = str `isPrefixOf` ":load"

startREPL :: VerbosityLevel -> Maybe [FilePath] -> Maybe FilePath -> IO ()
startREPL vl searchPath inputFile = do
  conf <- initConf
  currentDir <- getCurrentDirectory
  let sp = fromMaybe [currentDir] searchPath
  let conf' = conf{confVerbosity = vl, confSearchPath = sp, confCurrentDir = currentDir}
  homedir <- getHomeDirectory
  let historyFilePath = homedir FP.</> ".sparcl_history"
  let setting =
        HL.setComplete
          (replCompletion $ confModuleContext conf')
          HL.defaultSettings
            { HL.historyFile = Just historyFilePath
            }
  let comp = case inputFile of
        Just fp -> procLoad fp
        Nothing -> waitCommand
  putStrLn $ "Built: " ++ compileTime
  runREPL setting conf' comp
  where
    compileTime =
      $( do
          t <- TH.runIO $ getCurrentTime
          return $ TH.LitE $ TH.StringL (show t)
       )

commandSpec :: [CommandSpec (REPL ())]
commandSpec =
  [ NoArgCommand ":quit" (return ()) (text "Quit REPL.")
  , StringCommand ":load" procLoad "FILEPATH" (text "Load a program.")
  , NoArgCommand ":reload" procReload (text "Reload the last program.")
  , StringCommand ":verbosity" procVerbosity "[0-3]" (text "Change the current verbosity.")
  , NoArgCommand ":help" procHelp (text "Show this help.")
  , StringCommand ":type" procType "EXP" (text "Print the expression's type.")
  ]

procHelp :: REPL ()
procHelp = do
  liftIO $ print $ commandUsage commandSpec
  waitCommand

procVerbosity :: String -> REPL ()
procVerbosity vlStr =
  case reads vlStr of
    [(n, "")] ->
      local (\cf -> cf{confVerbosity = max n 0}) waitCommand
    _ -> do
      liftIO $ putStrLn "Verbosity level should an integer"
      waitCommand

checkError :: (MonadCatch m, MonadIO m) => m a -> m a -> m a
checkError m f =
  m
    `catch` ( \(e :: RunTimeException) -> do
                liftIO $ print e
                f
            )
    `catch` ( \(e :: StaticException) -> do
                liftIO $ print e
                f
            )
    `catch` ( \(e :: IOException) -> do
                liftIO $ print e
                f
            )
    `catch` ( \(e :: SomeException) -> do
                liftIO $ putStrLn "Unexpected exception is thrown."
                liftIO $ print e
                f
            )

tryExec :: (MonadCatch m, MonadIO m) => m a -> m (Maybe a)
tryExec m =
  checkError (fmap Just m) (return Nothing)

setModule :: ModuleInfo Value -> REPL ()
setModule m = do
  () <- asks confModuleContext >>= \ref -> liftIO $ modifyIORef ref (miModuleContext m <>)

  -- if miModuleName m == baseModule
  --   then Hint.setImports [miHsFile m ]
  --   else Hint.loadModules [miHsFile m]

  let mc = miModuleContext m

  debugPrint 1 $ text "Module:" <+> ppr (miModuleName m) <+> text "has been loaded."
  debugPrint 1 $ vcat $ map (\(n, t) -> fillBreak 8 (ppr n <+> text ":") <+> align (ppr t)) (M.toList $ mcTypeTable mc)
  debugPrint 3 $
    text "  "
      <> align
        ( vcat
            [ fillBreak 8 (text "names:") <+> align (pprMap $ M.map S.toList $ mcNameTable mc)
            , fillBreak 8 (text "ops:") <+> align (pprMap $ mcOpTable mc)
            , fillBreak 8 (text "constructors:") <+> align (pprMap $ mcConTable mc)
            , fillBreak 8 (text "types:") <+> align (pprMap $ mcTypeTable mc)
            , fillBreak 8 (text "synonyms:") <+> align (pprMap $ mcSynTable mc)
            , fillBreak 8 (text "values:") <+> align (pprMap $ mcValueTable mc)
            ]
        )

resetModule :: REPL ()
resetModule = do
  ref <- asks confModuleContext
  liftIO $ writeIORef ref mempty

  --  Hint.reset

  --  modifyTables $ const initTables
  -- ref <- ask
  -- liftIO $ modifyIORef ref $ \conf -> conf { confTables = initTables }
  local (\cf -> cf{confVerbosity = 0}) $ setModule baseModuleInfo

reportTypeInfo :: ModuleInfo Value -> REPL ()
reportTypeInfo m = do
  liftIO $
    hPutDocWith stdout 100 0.9 $
      vcat
        [ vcat $ map (\(n, t) -> fillBreak 8 (ppr n <+> text ":") <+> align (ppr t)) (M.toList $ mcTypeTable $ miModuleContext m)
        , text "Ok."
        ]
        <> line

fromFreshLoader :: Loader Value a -> REPL a
fromFreshLoader m = do
  tc <- asks confTC
  dl <- asks confVerbosity
  sps <- asks confSearchPath
  liftIO $ runLoader sps dl tc m

fromLoader :: Loader Value a -> REPL a
fromLoader m = do
  tc <- asks confTC
  dl <- asks confVerbosity
  sps <- asks confSearchPath
  mc <- asks confModuleContext >>= \ref -> liftIO $ readIORef ref
  liftIO $ runLoaderWith sps dl tc mc m

procLoad :: String -> REPL ()
procLoad fp = do
  -- searchPath <- getSearchPath
  -- tinfo <- getTInfo
  currentDir <- Rd.asks confCurrentDir
  let fp' = currentDir FP.</> trimSpace fp
  localLastLoad fp $ do
    res <-
      checkError
        (fmap Just $ fromFreshLoader $ readModule fp' (\env bind -> pure $ M.toList $ runEval (evalUBind env bind)))
        (return Nothing)
    case res of
      Nothing -> do
        waitCommand
      Just m -> do
        resetModule
        setModule m
        reportTypeInfo m
        waitCommand
  where
    trimSpace :: String -> String
    trimSpace [] = []
    trimSpace (c : s) | isSpace c = trimSpace s
    trimSpace ('"' : s) = findDQ s
    trimSpace s = trimTrailingSpace s

    trimTrailingSpace :: String -> String
    trimTrailingSpace = reverse . dropWhile isSpace . reverse

    findDQ :: String -> String
    findDQ [] = rtError $ text "No matching quote."
    findDQ ('"' : _) = []
    findDQ (c : s) = c : findDQ s

procReload :: REPL ()
procReload = do
  lastLoad <- Rd.asks confLastLoad
  case lastLoad of
    Nothing -> do
      liftIO $ putStrLn "Command :load has not been performed yet. Nothing happened."
      waitCommand
    Just fp -> procLoad fp

procType :: String -> REPL ()
procType str = do
  res <- tryExec $ fromLoader $ typeOfExpressionStr str

  case res of
    Nothing -> waitCommand
    Just ty -> do
      liftIO $ hPutDocWith stdout 120 0.8 $ ppr ty
      liftIO $ putStrLn ""
      waitCommand

procExp :: String -> REPL ()
procExp "" = waitCommand
procExp str = do
  res <- tryExec $ fromLoader $ valueOfExpressionStr str (\env bind -> pure $ runEval (evalUBindNoAcc env bind))

  case res of
    Nothing -> waitCommand
    Just v -> do
      liftIO $ print (ppr v)
      waitCommand

waitCommand :: REPL ()
waitCommand = do
  maybeLine <- REPL $ {- lift $ -} lift $ MyInputT $ HL.getInputLine "Sparcl> "
  case maybeLine of
    Nothing ->
      liftIO $ putStrLn "Quitting..."
    Just s -> parseCommand commandSpec procExp s
