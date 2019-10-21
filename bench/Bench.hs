import           Control.Exception               (evaluate)
import           Control.Monad.Catch             (MonadCatch, MonadThrow)
import           Control.Monad.IO.Class
import           Control.Monad.Reader

import           Text.Printf

import           Language.Sparcl.Class
import           Language.Sparcl.DebugPrint
import           Language.Sparcl.Exception
import           Language.Sparcl.Module          (ModuleInfo (..),
                                                  baseModuleInfo)
import           Language.Sparcl.Pretty          hiding ((<$>))
import           Language.Sparcl.Renaming
import           Language.Sparcl.Surface.Parsing
import           Language.Sparcl.Surface.Syntax  (Module (..))
import           Language.Sparcl.Typing.TCMonad
import           Language.Sparcl.Typing.Typing


import qualified System.Clock                    as Clock


{-# SPECIALIZE bench :: String -> Int -> M a -> M a #-}
bench :: forall m a. MonadIO m => String -> Int -> m a -> m a
bench str trials m = do
  !s <- liftIO $ Clock.getTime Clock.Monotonic
  !res <- replicateM trials (withTime m)
  !e <- liftIO $ Clock.getTime Clock.Monotonic

  let diff :: Double = fromIntegral (Clock.toNanoSecs (Clock.diffTimeSpec e s)) / (10 ** 6) -- in seconcs

  liftIO $ putStrLn $ printf "Elapsed (%s): %2.4f ms" str (diff / fromIntegral trials)

  let ts = map snd res
  let tt = sum ts
  let mean :: Double = fromInteger tt / fromIntegral trials / (10 ** 6) -- in seconds
  let var  :: Double = fromInteger (sum [ (a * fromIntegral trials - tt)^(2 :: Integer) | a <- ts ]) / (fromIntegral trials ** 3) / (10 ** 12)

  liftIO $ putStrLn $ printf "mean: %2.4f ms / var: %2.4f ms^2" mean var

  return (last $ map fst res)
  where
    withTime :: m a -> m (a, Integer)
    withTime comp = do
      s <- liftIO $ Clock.getTime Clock.Monotonic
      !r <- comp
      e <- liftIO $ Clock.getTime Clock.Monotonic

      let diff = Clock.toNanoSecs (Clock.diffTimeSpec e s)
      return (r, diff)






newtype M a = M (ReaderT TypingContext IO a)
  deriving (Functor, Applicative, Monad, MonadIO, MonadReader TypingContext, MonadCatch, MonadThrow)


instance Has KeyTC TypingContext M where
  ask _ = Control.Monad.Reader.ask

instance Local KeyTC TypingContext M where
  local _ = Control.Monad.Reader.local

instance Has KeyDebugLevel Int M where
  ask _ = return 0

runM :: M a -> IO a
runM (M m) = do
  tc <- initTypingContext
  runReaderT m tc

checkType :: FilePath -> Int -> IO ()
checkType fp trials = runM $ do
  s <- liftIO $ readFile fp
  Module currentModule _exports _imports decls <- either (staticError . text) return $ parseModule fp s

  -- For simplificity, we ignore imports here

  let nameTable = miNameTable baseModuleInfo
  let opTable   = miOpTable   baseModuleInfo

  let nameError (l, d) = staticError (nest 2 (ppr l </> d))

  (renamedDecls, tyDecls, synDecls, _newNames, _newOpTable) <-
    liftIO $ either nameError return $ runRenaming nameTable opTable $ renameTopDecls currentModule decls

  let tyEnv = miTypeTable baseModuleInfo
  let conEnv = miConTable baseModuleInfo
  let synEnv = miSynTable baseModuleInfo

  let comp = do
        (_typedDecls, nts, _dataDecls', _typeDecls', _newCTypeTable, _newSynTable) <-
          runTCWith conEnv tyEnv synEnv $ inferTopDecls renamedDecls tyDecls synDecls
        liftIO $ evaluate nts

  _ <- comp
  resetBench

  liftIO $ putStrLn $ take 80 (cycle "-")

  nts' <- bench ("Typing (" ++ fp ++ ")") trials comp

  -- forM_ nts' $ \(n, t) -> do
  --   liftIO $ print $ ppr n <+> text ":" <+> ppr t
  reportBench
  liftIO $ putStrLn $ "Processed: " ++ show (length nts') ++ " definitions."

  liftIO $ putStrLn $ take 80 (cycle "-")
  liftIO $ putStrLn ""

  return ()

main :: IO ()
main = do
  checkType "./Examples/F.sparcl"       1000
  checkType "./Examples/GV_func.sparcl" 1000
  checkType "./Examples/App1.sparcl"    10000
  checkType "./Examples/App10.sparcl"   10000
