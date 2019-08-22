module Language.Sparcl.DebugPrint
  (
    debugPrint,
    KeyDebugLevel,
  ) where

import           Language.Sparcl.Class
import           Control.Monad.IO.Class
import           Control.Monad (when)
import           System.IO (stderr)
import           Language.Sparcl.Pretty          hiding ((<$>))

data KeyDebugLevel 

debugPrint :: (Has KeyDebugLevel Int m, MonadIO m) => Int -> Doc -> m ()
debugPrint n s = do 
  vlevel      <- ask (key @KeyDebugLevel)
  when (vlevel >= n) $ 
    liftIO $ displayIO stderr $ renderPretty 0.8 80 $
      dullcyan $ text ("[DEBUG " ++ show n ++ "]") <+> align s <> line
    
