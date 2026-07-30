module Language.Sparcl.DebugPrint (
  debugPrint,
  MonadDebug (..),
) where

import Control.Monad (when)
import Control.Monad.IO.Class
import Control.Monad.Reader (ReaderT)
import Control.Monad.Trans (lift)

import Language.Sparcl.Pretty hiding ((<$>))
import System.IO (stderr)

class (Monad m) => MonadDebug m where
  askDebugLevel :: m Int

instance (MonadDebug m) => MonadDebug (ReaderT r m) where
  askDebugLevel = lift askDebugLevel

debugPrint :: (MonadIO m, MonadDebug m) => Int -> Doc -> m ()
debugPrint n s = do
  vlevel <- askDebugLevel
  when (vlevel >= n) $
    liftIO $
      hPutDocWith stderr 120 0.9 $
        dullcyan $
          text ("[D" ++ show n ++ "]") <+> align s <> line
