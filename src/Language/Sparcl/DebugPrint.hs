module Language.Sparcl.DebugPrint
  (
    debugPrint,
    KeyDebugLevel,
  ) where

import           Control.Monad          (when)
import           Control.Monad.IO.Class
import           Language.Sparcl.Class
import           Language.Sparcl.Pretty hiding ((<$>))
import           System.IO              (stderr)

data KeyDebugLevel

debugPrint :: (Has KeyDebugLevel Int m, MonadIO m) => Int -> Doc -> m ()
debugPrint n s = do
  vlevel      <- ask (key @KeyDebugLevel)
  when (vlevel >= n) $
    liftIO $ displayIO stderr $ renderPretty 0.9 120 $
      dullcyan $ text ("[D" ++ show n ++ "]") <+> align s <> line

