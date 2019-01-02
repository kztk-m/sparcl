module Language.Sparcl.REPL where

import Language.Sparcl.Module
import Language.Sparcl.Untyped.Eval
import Language.Sparcl.Untyped.Desugar.Syntax
import Language.Sparcl.Typing.TC
import Language.Sparcl.Typing.Typing 

import Language.Sparcl.Untyped.Desugar

import Language.Sparcl.Untyped.Parsing 

import qualified System.Console.Haskeline as HL

import Data.IORef 
import Control.Monad.Reader

import Control.DeepSeq

import qualified Data.Map as M 

import Language.Sparcl.Pretty
import qualified Text.PrettyPrint.ANSI.Leijen as D

import Data.Function (on)
import Data.List (isPrefixOf, sortBy, groupBy)

import Control.Arrow (first)
import Data.Char (isSpace)

import Control.Exception (IOException, SomeException, catch, evaluate)

import System.Directory (getCurrentDirectory, getHomeDirectory)
import System.FilePath  ((</>))


--

type CommandName = String
type Description = D.Doc 
data CommandSpec a
  = NoArgCommand  CommandName  a                    Description
  | StringCommand CommandName  (String -> a) String Description

data CommandTrie a
  = Exec   String (String -> a)
  | Choice (M.Map Char (CommandTrie a))

commandUsage :: [CommandSpec a] -> Doc
commandUsage spec = D.align $ D.vsep $ map pprCommand spec 
  where
    pprCommand (NoArgCommand c _ d) =
      D.nest 4 (D.text c D.<$> d)
    pprCommand (StringCommand c _ a d) =
      D.nest 4 (D.text c D.<+> D.text a D.<$> d) 

parseCommand :: [CommandSpec a] -> (String -> a) -> String -> a
parseCommand spec cont initStr = go initTrie initStr
  where
    initTrie = makeTrie spec

    go (Exec [] f)  str = f $ dropWhile isSpace str
    go (Exec _red f) []  = f []
    go (Exec (r:red) f) (c:cs) | r == c = go (Exec red f) cs
    go (Exec _red f) (c:cs) | isSpace c = f $ dropWhile isSpace cs
    go (Exec _ _) _ = cont initStr 
    go (Choice mp) (c:cs) = case M.lookup c mp of
      Just tr -> go tr cs
      Nothing -> cont initStr 
    go _ _ = cont initStr

    makeTrie :: [CommandSpec a] -> CommandTrie a
    makeTrie spec = h (groupByFirstChar $ sortBy (compare `on` fst) $ map normalize spec)
      where
        groupByFirstChar = groupBy ((==) `on` head' . fst)
          where
            head' []    = Nothing
            head' (x:_) = Just x 
        
        normalize (NoArgCommand s f _)    = (s, const f)
        normalize (StringCommand s f _ _) = (s, f)

        h [[(s,f)]] = Exec s f -- there is only one choice for the first letter. 
        h xss = Choice $ M.fromList $
                map (\xs@((a:_,_):_) -> (a, h (groupByFirstChar $ map (first tail) xs))) xss 

------------------------

data Conf =
  Conf { confSearchPath :: [FilePath],
         confCurrentDir :: FilePath, 
         confVerbosity  :: Int,
         confLastLoad   :: Maybe FilePath,
         confTyInfo     :: TInfo,
         confOpTable      :: OpTable,
         confDefinedNames :: [QName],
         confTypeTable    :: TypeTable,
         confSynTable     :: SynTable,
         confValueTable   :: ValueTable
       }

type REPL = ReaderT (IORef Conf) (HL.InputT IO) 


-- Verbosity is not implemented yet. 
type VerbosityLevel = Int

initConf :: IO Conf
initConf = do
  tinfo <- initTInfo
  return $ Conf { confSearchPath = [],
                  confCurrentDir = ".", 
                  confVerbosity = 0,
                  confLastLoad = Nothing,
                  confTyInfo = tinfo,
                  confOpTable = M.empty,
                  confDefinedNames = [],
                  confTypeTable = M.empty,
                  confSynTable = M.empty,
                  confValueTable = M.empty }

setLastLoad :: FilePath -> REPL ()
setLastLoad fp = do
  ref <- ask
  liftIO $ modifyIORef ref $ \conf -> conf { confLastLoad = Just fp }
  

getConf :: REPL Conf
getConf = do
  ref <- ask
  liftIO $ readIORef ref 


replCompletion :: IORef Conf -> HL.CompletionFunc IO
replCompletion cref (curr, rest) =
  case checkLoadMode curr of
    Just (prefix, sp, r) -> do
      (s, cs) <- HL.completeFilename (reverse r, rest)
      return (s ++ reverse (prefix ++ sp), cs)
    Nothing ->
      completeIDs (curr, rest)
  where
    completeIDs :: HL.CompletionFunc IO
    completeIDs (curr, rest) =
      HL.completeWord Nothing " \t\n\r" f (curr, rest)
      where
        f :: String -> IO [HL.Completion]
        f str = do
          names <- confDefinedNames <$> readIORef cref
          return $ map HL.simpleCompletion $ filter (str `isPrefixOf`) $ commands curr ++ makeNameStrings names

        makeNameStrings :: [QName] -> [String]
        makeNameStrings ns =
          [ s | BName (NormalName s) <- ns ] ++
          [ s | (_, s) <- qualified ] ++
          [ moduleNameToStr m ++ "." ++ s | (m, s) <- qualified ] 
          where
            qualified = [ (m,n) | QName m (NormalName n) <- ns ] 


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
  cref <- newIORef conf'
  homedir <- getHomeDirectory
  let historyFilePath = homedir </> ".sparcl_history"
  let setting = HL.setComplete (replCompletion cref) HL.defaultSettings
                { HL.historyFile = Just historyFilePath }
  let comp = case inputFile of
        Just fp -> procLoad fp
        Nothing -> waitCommand
  HL.runInputT setting $ runReaderT (setModule baseModuleInfo >> comp) cref 

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

checkError :: IO a -> IO a -> IO a
checkError m f =
  m `catch` (\(e :: RunTimeException) -> do
               putStrLn (show e) >> f )
    `catch` (\(e :: StaticException) -> do
                putStrLn (show e) >> f )
    `catch` (\(e :: IOException) -> 
               putStrLn (show e) >> f)
    `catch` (\(e :: SomeException) -> do
               putStrLn "Unexpected exception is thrown." 
               putStrLn (show e)
               f) 

setModule :: ModuleInfo -> REPL ()
setModule m = do
  ref <- ask
  liftIO $ modifyIORef ref $ \ci -> ci {
    confDefinedNames = miDefinedNames m ++ confDefinedNames ci,
    confOpTable      = M.union (miOpTable m)    (confOpTable ci),
    confTypeTable    = M.union (miTypeTable m)  (confTypeTable ci),
    confSynTable     = M.union (miSynTable m)   (confSynTable ci),
    confValueTable   = M.union (miValueTable m) (confValueTable ci) }
  liftIO $ putStrLn $ "Module: " ++ moduleNameToStr (miModuleName m) ++ " has been loaded."


resetModule :: REPL ()
resetModule = do 
  ref <- ask
  liftIO $ modifyIORef ref $ \conf -> conf {
    confDefinedNames = [],
    confOpTable    = M.empty,
    confTypeTable  = M.empty,
    confSynTable   = M.empty, 
    confValueTable = M.empty  }
  setModule baseModuleInfo
        
  
            
           

procLoad :: String -> REPL ()
procLoad fp = do
  conf <- getConf
  let searchPath = confSearchPath conf
  let tinfo      = confTyInfo conf
  let currentDir = confCurrentDir conf
  let fp' = currentDir </> trimSpace fp 
  res <- liftIO $ checkError (fmap Just $ runM searchPath tinfo $ readModule fp') (return Nothing)
  case res of
    Nothing  -> waitCommand
    Just m -> do
      setLastLoad fp 
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
  conf <- getConf
  let lastLoad = confLastLoad conf
  case lastLoad of
    Nothing -> do
      liftIO $ putStrLn "Command :load has not been performed yet. Do nothing."
      waitCommand
    Just fp -> procLoad fp 

procType :: String -> REPL ()
procType str = do
  conf <- getConf
  let definedNames = confDefinedNames conf 
  let opTable      = confOpTable conf 
  let tinfo        = confTyInfo conf
  let typeTable    = confTypeTable conf
  let synTable     = confSynTable conf
  let vl = confVerbosity conf
  
  res <- liftIO $ checkError (do e <- parseAndDesugarExp vl definedNames opTable str
                                 t <- typeCheckExp tinfo typeTable synTable e
                                 return (Just t)) (return Nothing)
  case res of
    Nothing -> waitCommand
    Just ty -> do
      liftIO $ print (ppr ty)
      waitCommand 
                                 
                                 
  
parseAndDesugarExp :: VerbosityLevel -> [QName] -> OpTable -> String -> IO OLExp
parseAndDesugarExp vl definedNames opTable str = do
  exp  <- either (staticError . D.text) return $ parseExp str
  exp' <- runDesugar ["<interactive>"] definedNames opTable (desugarLExp exp)
  when (vl >= 1) $
    print $ D.dullwhite (D.text "[DEBUG]") D.<+>
            D.nest 2 (D.text "Desugarred exp:" D.</> D.align (ppr exp'))
  evaluate exp' 
  
typeCheckExp :: TInfo -> TypeTable -> SynTable -> OLExp -> IO Ty
typeCheckExp tinfo tt st exp = do
  liftIO $ setEnvs tinfo tt st     
  t <- fmap (either staticError id) $ runTC tinfo $ inferExp exp 
  evaluate t

evalExp :: ValueTable -> OLExp -> IO Value
evalExp env e = 
  evaluate $ force $ runEval (evalU env e)


procExp :: String -> REPL ()
procExp ""  = waitCommand 
procExp str = do
  conf <- getConf 
  let definedNames = confDefinedNames conf 
  let opTable      = confOpTable conf
  let tinfo        = confTyInfo conf
  let valueTable   = confValueTable conf
  let typeTable    = confTypeTable conf
  let synTable     = confSynTable conf
  let vl = confVerbosity conf
  
  res <- liftIO $ checkError (do e  <- parseAndDesugarExp vl definedNames opTable str
                                 _  <- typeCheckExp tinfo typeTable synTable e
                                 v  <- evalExp valueTable e 
                                 return (Just v)) (return Nothing)
  case res of
    Nothing -> waitCommand
    Just v -> do
      liftIO $ print (ppr v)
      waitCommand 
  

waitCommand :: REPL ()
waitCommand = do  
  maybeLine <- lift $ HL.getInputLine "Sparcl> "
  case maybeLine of
    Nothing -> do
      liftIO $ putStrLn "Quitting..."
    Just s -> parseCommand commandSpec procExp s

