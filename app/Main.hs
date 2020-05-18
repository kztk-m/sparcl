module Main where

import           Language.Sparcl.REPL  (VerbosityLevel, startREPL)
import           System.Console.GetOpt
import           System.Environment

data OptConf = OptConf { optSearchPath     :: Maybe [FilePath],
                         optInputFile      :: Maybe FilePath,
                         optVerbosityLevel :: VerbosityLevel,
                         optHelpMode       :: Bool }

initOptConf :: OptConf
initOptConf = OptConf { optSearchPath = Nothing,
                        optInputFile  = Nothing,
                        optVerbosityLevel = 0,
                        optHelpMode = False }

options :: [ OptDescr (OptConf -> OptConf) ]
options =
  [ Option ['v'] ["verbosity"] (OptArg optV "VERBOSITY") "Set the verbosity level to VERBOSITY.",
    Option ['h'] ["help"]      (NoArg optH) "Show this help message."
  ]
  where
    optV m c = c { optVerbosityLevel = maybe 1 read m }
    optH c = c { optHelpMode = True }

helpMessage :: IO ()
helpMessage = do
  prog <- getProgName
  let header =
        unlines [ "An interactive environment for Sparcl.",
                  "Usage: " ++ prog ++ " OPTIONS [FILENAME]" ]
  putStrLn (usageInfo header options)



parseArgs :: IO (Maybe OptConf)
parseArgs = do
  args <- getArgs
  case getOpt Permute options args of
    (os, rest, []) ->
      return $ Just $ foldr (.) id os (makeInit rest)
    (_, _, errs) -> do
      putStrLn (concat errs)
      helpMessage
      return Nothing
  where
    makeInit (f:_) = initOptConf { optInputFile = Just f }
    makeInit _     = initOptConf


main :: IO ()
main = do
  res <- parseArgs
  case res of
    Just oc ->
      if optHelpMode oc then
        helpMessage
      else
        startREPL (optVerbosityLevel oc) (optSearchPath oc) (optInputFile oc)
    Nothing -> return ()
