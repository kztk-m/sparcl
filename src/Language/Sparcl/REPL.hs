{-# OPTIONS_GHC -fprint-potential-instances #-}

module Language.Sparcl.REPL where

import Language.Sparcl.Module
import Language.Sparcl.Eval
import Language.Sparcl.Value
import Language.Sparcl.Exception 
import Language.Sparcl.Core.Syntax
import Language.Sparcl.Typing.TCMonad
import Language.Sparcl.Typing.Typing
import Language.Sparcl.Typing.Type
import Language.Sparcl.Renaming (renameExp, runRenaming, NameTable, OpTable) 

import Language.Sparcl.Desugar
import Language.Sparcl.Class

import Language.Sparcl.Surface.Parsing 
import Language.Sparcl.Command

import qualified System.Console.Haskeline as HL

import Data.IORef 
import qualified Control.Monad.Reader as Rd
import Control.Monad.IO.Class 
import Control.Monad.Trans (MonadTrans, lift)
import Control.Monad (join, liftM2) 

import Control.DeepSeq

import qualified Data.Map as M
import qualified Data.Set as S 

import Language.Sparcl.Pretty
import qualified Text.PrettyPrint.ANSI.Leijen as D

import Data.List (isPrefixOf)

import Data.Char (isSpace)

import Control.Exception (IOException, SomeException, evaluate)
import Control.Monad.Catch

import System.Directory (getCurrentDirectory, getHomeDirectory)
import qualified System.FilePath as FP ((</>))

import qualified Language.Haskell.Interpreter as Hint

-- import Data.Coerce 

data Conf =
  Conf { confSearchPath  :: [FilePath],
         confLoadPath    :: FilePath, 
         confCurrentDir  :: FilePath, 
         confVerbosity   :: Int,
         confLastLoad    :: Maybe FilePath,
         confTC          :: TypingContext,
         confNameTable   :: IORef NameTable,
         confOpTable     :: IORef OpTable,
         confTypeTable   :: IORef TypeTable, 
         confSynTable    :: IORef SynTable,
         confValueTable  :: IORef ValueTable
       }

-- To avoid orphan instances
newtype MyInputT m a = MyInputT { runMyInputT :: HL.InputT m a }
  deriving (Functor, Applicative, Monad, MonadIO, HL.MonadException, MonadTrans)

instance HL.MonadException m => MonadThrow (MyInputT m) where
  throwM = HL.throwIO

instance HL.MonadException m => MonadCatch (MyInputT m) where
  catch = HL.catch 

-- FIXME: I am not sure the following implementation is OK or not.
instance (HL.MonadException m) => MonadMask (MyInputT m) where
  mask k = HL.controlIO $ \(HL.RunIO run) -> liftIO $ mask' $ \restore ->
    run $ k (\y -> join $ liftIO $ restore $ run y)  
    where
      mask' = mask @IO

  uninterruptibleMask k = HL.controlIO $ \(HL.RunIO run) -> liftIO $ uninterruptibleMask' $ \restore ->
    run $ k (\y -> join $ liftIO $ restore $ run y)  
    where
      uninterruptibleMask' = uninterruptibleMask @IO

  generalBracket before after comp =
    HL.controlIO $ \(HL.RunIO run) -> fmap (uncurry $ liftM2 (,)) $ 
                     generalBracket' (run before)
                             (\ma me -> run (do { a <- ma; e <- c2c me; after a e}))
                             (\ma -> run (ma >>= comp))
    where
      c2c :: forall mm b. Monad mm => ExitCase (mm b) -> mm (ExitCase b)
      c2c (ExitCaseSuccess mb)  = do
        b <- mb
        return (ExitCaseSuccess b) 
      c2c (ExitCaseException e) = return (ExitCaseException e)
      c2c ExitCaseAbort         = return ExitCaseAbort
      
      generalBracket' :: IO a -> (a -> ExitCase b -> IO c) -> (a -> IO b) -> IO (b, c)
      generalBracket' = generalBracket 
  

newtype REPL a = REPL { unREPL :: Rd.ReaderT Conf (Hint.InterpreterT (MyInputT IO)) a }
  deriving (Functor, Applicative, Monad, MonadIO,
            Rd.MonadReader Conf,
            MonadThrow, MonadCatch, MonadMask) 

instance Hint.MonadInterpreter REPL where
  fromSession s = REPL $ lift (Hint.fromSession s)
  modifySessionRef s f = REPL $ lift (Hint.modifySessionRef s f)
  runGhc c = REPL $ lift (Hint.runGhc c)
  

runREPL :: HL.Settings IO -> Conf -> REPL a -> IO a
runREPL setting conf comp = do
  let rethrow :: (MonadThrow m, Exception e) => m (Either e a) -> m a 
      rethrow m = m >>= either throwM return  
  HL.runInputT setting $ runMyInputT $ rethrow $ Hint.runInterpreter $ Rd.runReaderT (unREPL $ resetModule >> comp) conf
  
  


instance Has KeyLoadPath FilePath REPL where
  ask _ = Rd.asks confLoadPath 

instance Has KeySearchPath [FilePath] REPL where
  ask _ = Rd.asks confSearchPath 

instance Has KeyVerb Int REPL where
  ask _ = Rd.asks confVerbosity

instance Local KeyVerb Int REPL where
  local _ f =
    Rd.local (\conf -> conf { confVerbosity = f (confVerbosity conf) })

instance Has KeyName NameTable REPL where
  ask _ = do
    ref <- Rd.asks confNameTable
    liftIO $ readIORef ref
    
instance Modify KeyName NameTable REPL where
  modify _ f = do
    ref <- Rd.asks confNameTable
    liftIO $ modifyIORef ref f 

instance Local KeyName NameTable REPL 

instance Has KeyOp OpTable REPL where
  ask _ = do
    ref <- Rd.asks confOpTable
    liftIO $ readIORef ref

instance Modify KeyOp OpTable REPL where
  modify _ f = do
    ref <- Rd.asks confOpTable
    liftIO $ modifyIORef ref f
instance Local KeyOp OpTable REPL


instance Has KeyType TypeTable REPL where
  ask _ = liftIO . readIORef =<< Rd.asks confTypeTable

instance Local KeyType TypeTable REPL 

instance Modify KeyType TypeTable REPL where
  modify _ f = liftIO . flip modifyIORef f =<< Rd.asks confTypeTable


instance Has KeySyn SynTable REPL where
  ask _ = liftIO . readIORef =<< Rd.asks confSynTable

instance Modify KeySyn SynTable REPL where
  modify _ f = liftIO . flip modifyIORef f =<< Rd.asks confSynTable

instance Local KeySyn SynTable REPL


instance Has KeyValue ValueTable REPL where
  ask _ = liftIO . readIORef =<< Rd.asks confValueTable

instance Modify KeyValue ValueTable REPL where
  modify _ f = liftIO . flip modifyIORef f =<< Rd.asks confValueTable

instance Local KeyValue ValueTable REPL


instance Has KeyTC TypingContext REPL where
  ask _ = Rd.asks confTC
  


    
-- Verbosity is not implemented yet. 
type VerbosityLevel = Int

initConf :: IO Conf
initConf = do
  tinfo <- initTypingContext
  refNt <- newIORef M.empty
  refOt <- newIORef M.empty
  refSt <- newIORef M.empty
  refTt <- newIORef M.empty
  refVt <- newIORef M.empty
  
  return $ Conf { confSearchPath = ["."],
                  confLoadPath   = ".sparcl", 
                  confCurrentDir = ".", 
                  confVerbosity = 0,
                  confLastLoad = Nothing,
                  confTC         = tinfo,
                  confNameTable  = refNt,
                  confOpTable    = refOt,
                  confTypeTable  = refTt, 
                  confSynTable   = refSt,
                  confValueTable = refVt
                }
  
localLastLoad :: FilePath -> REPL r -> REPL r 
localLastLoad fp m = do
  Rd.local (\conf -> conf { confLastLoad = Just fp }) m 
  --liftIO $ modifyIORef ref $ \conf -> conf { confLastLoad = Just fp }
  

-- getConf :: REPL Conf
-- getConf = do
--   ref <- ask
--   liftIO $ readIORef ref 


replCompletion :: IORef NameTable -> HL.CompletionFunc IO
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
          names <- fmap M.keys $ readIORef cref
          return $ map HL.simpleCompletion $ filter (str `isPrefixOf`) $ commands curr ++ makeNameStrings names

        makeNameStrings :: [SurfaceName] -> [String]
        makeNameStrings ns =
          [ s | Bare (User s) <- ns ] ++
          [ s | (_, s) <- qualified ] ++
          [ m ++ "." ++ s | (m, s) <- qualified ] 
          where
            qualified = [ (m,n) | Qual (ModuleName m) (User n) <- ns ] 


        commands :: String -> [String]
        commands s
          | all (not . isSpace) s
            && not (null s)
            && last s == ':' = commandStrings
          | otherwise        = [] 

        commandStrings = [ s | NoArgCommand s _ _ <- commandSpec ]
                         ++ [ s | StringCommand s _ _ _ <- commandSpec ]
                                            
    
    -- check whether the input is in the form of "... daol:" 
    checkLoadMode :: String -> Maybe (String, String, String)
    checkLoadMode = check . parse . reverse
      where
        -- split "foo  bar baz" to "foo", "  ", "bar baz"
        parse s = let (w1, rest) = span (not . isSpace) s
                      (sp, w2)   = span isSpace rest
                  in (w1, sp, w2)

        check (w1, sp, w2)
          | isLoadPrefix w1 && not (null sp) = Just (w1, sp, w2)
          | otherwise                        = Nothing

        isLoadPrefix []  = False
        isLoadPrefix [_] = False
        isLoadPrefix str = str `isPrefixOf` ":load" 
        

startREPL :: VerbosityLevel -> Maybe [FilePath] -> Maybe FilePath -> IO ()
startREPL vl searchPath inputFile = do
  conf <- initConf
  currentDir <- getCurrentDirectory
  let sp = case searchPath of
             Nothing  -> [currentDir]
             Just fps -> fps 
  let conf' = conf { confVerbosity = vl, confSearchPath = sp, confCurrentDir = currentDir }
  homedir <- getHomeDirectory
  let historyFilePath = homedir FP.</> ".sparcl_history"
  let setting = HL.setComplete (replCompletion $ confNameTable conf') HL.defaultSettings
                { HL.historyFile = Just historyFilePath }
  let comp = case inputFile of
        Just fp -> procLoad fp
        Nothing -> waitCommand
  runREPL setting conf' $ do
    -- hsSp <- Hint.get Hint.searchPath 
    -- Hint.set [ Hint.searchPath Hint.:= hsSp ]
    comp 

commandSpec :: [CommandSpec (REPL ())]
commandSpec = [
  NoArgCommand  ":quit"    (return ())  (D.text "Quit REPL."),
  StringCommand ":load"      procLoad     "FILEPATH"  (D.text "Load a program."),
  NoArgCommand  ":reload"    procReload   (D.text "Reload the last program."),
--  StringCommand ":verbosity" propVerbosity "[0-3]" (D.text "Change the current verbosity."),
  NoArgCommand  ":help"      procHelp     (D.text "Show this help."),
  StringCommand ":type"      procType     "EXP" (D.text "Print the expression's type.")  
  ]

procHelp :: REPL ()
procHelp = do
  liftIO $ print $ commandUsage commandSpec
  waitCommand 

checkError :: (MonadCatch m, MonadIO m) => m a -> m a -> m a
checkError m f =
  m `catch` (\(e :: RunTimeException) -> do
                   liftIO $ putStrLn (show e)
                   f )
    `catch` (\(e :: StaticException) -> do
                   liftIO $ putStrLn (show e)
                   f )
    `catch` (\(e :: IOException) -> do
                  liftIO $ putStrLn (show e)
                  f)
    `catch` (\(e :: SomeException) -> do
                   liftIO $ putStrLn "Unexpected exception is thrown." 
                   liftIO $ putStrLn (show e)
                   f) 

tryExec :: (MonadCatch m, MonadIO m) => m a -> m (Maybe a)
tryExec m =
  checkError (fmap Just m) (return Nothing) 



setModule :: ModuleInfo Value -> REPL ()
setModule m = do
  modify (key @KeyName)  $ M.unionWith S.union (miNameTable m)
  modify (key @KeyOp)    $ M.union (miOpTable m)
  modify (key @KeyType)  $ M.union (miTypeTable m)
  modify (key @KeySyn)   $ M.union (miSynTable m)
  modify (key @KeyValue) $ M.union (miValueTable m) 

  -- if miModuleName m == baseModule
  --   then Hint.setImports [miHsFile m ]
  --   else Hint.loadModules [miHsFile m]

  debugPrint 1 $ text "Module:" <+> ppr (miModuleName m) <+> text "has been loaded."
  debugPrint 1 $ vcat $ map (\(n, t) -> fillBreak 8 (ppr n <+> text ":") <+> align (ppr t)) (M.toList $ miTypeTable m)
  debugPrint 3 $ text "  " <>
    align (vcat [
              fillBreak 8 (text "names:")    <+> align (pprMap $ M.map S.toList $ miNameTable m),
              fillBreak 8 (text "ops:")      <+> align (pprMap $ miOpTable m),
              fillBreak 8 (text "types")     <+> align (pprMap $ miTypeTable m),
              fillBreak 8 (text "synonyms:") <+> align (pprMap $ miSynTable m) ,
              fillBreak 8 (text "values:")   <+> align (pprMap $ miValueTable m) ])


resetModule :: REPL ()
resetModule = do
  set (key @KeyName)  $ M.empty
  set (key @KeyOp)    $ M.empty
  set (key @KeyType)  $ M.empty
  set (key @KeySyn)   $ M.empty
  set (key @KeyValue) $ M.empty 

--  Hint.reset
  
--  modifyTables $ const initTables
  -- ref <- ask
  -- liftIO $ modifyIORef ref $ \conf -> conf { confTables = initTables } 
  local (key @KeyVerb) (const 0) $ setModule baseModuleInfo
        
  
            
           

procLoad :: String -> REPL ()
procLoad fp = do
  -- searchPath <- getSearchPath
  -- tinfo <- getTInfo
  currentDir <- Rd.asks confCurrentDir 
  let fp' = currentDir FP.</> trimSpace fp
  localLastLoad fp $ do 
    res <- checkError (fmap Just $ runM $ readModule fp' (\env bind -> M.toList $ runEval (evalUBind env bind)))
                      (return Nothing) 
    case res of
      Nothing  -> waitCommand
      Just m -> do
        resetModule
        setModule m 
        waitCommand

  where
    trimSpace :: String -> String
    trimSpace [] = []
    trimSpace (c:s) | isSpace c = trimSpace s
    trimSpace ('"':s) = findDQ s
    trimSpace s       = trimTrailingSpace s

    trimTrailingSpace :: String -> String 
    trimTrailingSpace = reverse . dropWhile isSpace . reverse

    findDQ :: String -> String 
    findDQ [] = rtError $ D.text "No matching quote."
    findDQ ('"':_) = []
    findDQ (c:s)   = c:findDQ s
     

procReload :: REPL ()
procReload = do
  lastLoad <- Rd.asks confLastLoad 
  case lastLoad of
    Nothing -> do
      liftIO $ putStrLn "Command :load has not been performed yet. Do nothing."
      waitCommand
    Just fp -> procLoad fp 

procType :: String -> REPL ()
procType str = do
  -- tbl <- confTables <$> getConf
  -- let definedNames = tDefinedNames tbl
  -- let opTable      = tOpTable conf 
  -- let tinfo        = confTyInfo conf
  -- let typeTable    = confTypeTable conf
  -- let synTable     = confSynTable conf
  -- let vl = confVerbosity conf
  
  -- res <- liftIO $ checkError (do e <- parseAndDesugarExp vl definedNames opTable str
  --                                t <- typeCheckExp tinfo typeTable synTable e
  --                                return (Just t)) (return Nothing)

  res <- tryExec $ do
    (_, ty) <- readExp str
    return ty
  
  case res of
    Nothing -> waitCommand
    Just ty -> do
      liftIO $ print (ppr ty)
      waitCommand 
                                 
                                 
  
-- parseAndDesugarExp :: VerbosityLevel -> [QName] -> OpTable -> String -> IO OLExp
readExp ::
  (Has KeyVerb Int m,
   Has KeyName NameTable m,
   Has KeyOp   OpTable m,
   Has KeyTC   TypingContext m,
   Has KeyType  TypeTable m,
   Has KeySyn   SynTable m, 
   MonadIO m) => String -> m (Exp Name, Ty) 
readExp str = do
  nameTable <- ask (key @KeyName)
  opTable   <- ask (key @KeyOp)

  debugPrint 1 $ text "Parsing expression..."
  parsedExp       <- either (staticError . D.text) return $ parseExp' "<*repl*>" str
  debugPrint 1 $ text "Parsing Ok."
  debugPrint 1 $ text "Renaming expression..."
  (renamedExp, _) <- either nameError return $ runRenaming nameTable opTable (renameExp 0 M.empty parsedExp)
  debugPrint 1 $ text "Renaming Ok."


  tinfo <- ask (key @KeyTC)

  typeTable <- ask (key @KeyType)
  synTable  <- ask (key @KeySyn) 

  debugPrint 1 $ text "Type checking expression..."
  debugPrint 3 $ text "under:" <+> align (vcat [text "tyenv: " <+> align (pprMap typeTable),
                                                text "synenv:" <+> align (pprMap synTable) ])
  
  -- liftIO $ setEnvs tinfo typeTable synTable   
  (typedExp, ty) <- liftIO $ runTCWith tinfo typeTable synTable $ inferExp renamedExp 
  debugPrint 1 $ text "Type checking Ok."

  debugPrint 1 $ text "Desugaring expression..."
  desugaredExp <- liftIO $ runTC tinfo $ runDesugar $ desugarExp typedExp
  debugPrint 1 $ text "Desugaring Ok."
  debugPrint 2 $ text "Desugared:" </> align (ppr desugaredExp)

  desugaredExp' <- liftIO $ evaluate desugaredExp
  ty'         <- liftIO $ evaluate ty
  return (desugaredExp', ty')
  where
    nameError (loc, d) = staticError $ nest 2 $ vcat [ppr loc, d]
  
-- -- typeCheckExp :: TInfo -> TypeTable -> SynTable -> OLExp -> IO Ty
-- typeCheckExp :: (HasTInfo m, HasTypeTable m, HasSynTable m, MonadIO m) => OLExp -> m Ty
-- typeCheckExp exp = do
--   tinfo <- getTInfo
--   tt <- getTypeTable
--   st <- getSynTable
--   liftIO $ setEnvs tinfo tt st     
-- --  t <- fmap (either staticError id) $ runTC tinfo $ inferExp exp
--   t <- liftIO $ runTC tinfo $ inferExp exp 
--   liftIO $ evaluate t

-- evalExp :: ValueTable -> OLExp -> IO Value
evalExp :: (Has KeyVerb Int m, Has KeyValue ValueTable m, MonadIO m) => Exp Name -> m Value 
evalExp e = do
  env <- ask (key @KeyValue) -- getValueTable
  liftIO $ evaluate $ force $ runEval (evalU env e)


procExp :: String -> REPL ()
procExp ""  = waitCommand 
procExp str = do
  -- conf <- getConf 
  -- let definedNames = confDefinedNames conf 
  -- let opTable      = confOpTable conf
  -- let tinfo        = confTyInfo conf
  -- let valueTable   = confValueTable conf
  -- let typeTable    = confTypeTable conf
  -- let synTable     = confSynTable conf
  -- let vl = confVerbosity conf
  
  -- res <- liftIO $ checkError (do e  <- parseAndDesugarExp vl definedNames opTable str
  --                                _  <- typeCheckExp tinfo typeTable synTable e
  --                                v  <- evalExp valueTable e 
  --                                return (Just v)) (return Nothing)
  res <- tryExec $ do
    (e, _) <- readExp str
    evalExp e 
  
  case res of
    Nothing -> waitCommand
    Just v -> do
      liftIO $ print (ppr v)
      waitCommand 
  

waitCommand :: REPL ()
waitCommand = do  
  maybeLine <- REPL $ lift $ lift $ MyInputT $ HL.getInputLine "Sparcl> "
  case maybeLine of
    Nothing -> do
      liftIO $ putStrLn "Quitting..."
    Just s -> parseCommand commandSpec procExp s

