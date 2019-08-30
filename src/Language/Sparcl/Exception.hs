module Language.Sparcl.Exception where

import           Control.Exception      (Exception, throw)
import           Language.Sparcl.Pretty as D

newtype CannotHappen = CannotHappen Doc

cannotHappen :: Doc -> a
cannotHappen d = throw (CannotHappen d)

instance Show CannotHappen where
  show (CannotHappen d) =
    show (D.nest 2 $ D.text "Panic! `Cannot Happen' happened:" D.</> d)
instance Exception CannotHappen

newtype RunTimeException = RunTimeException Doc

instance Show RunTimeException where
  show (RunTimeException d) =
    show (D.text "Runtime Error:" D.</> D.nest 2 d)

instance Exception RunTimeException

rtError :: Doc -> a
rtError d = throw (RunTimeException d)

newtype StaticException = StaticException Doc

instance Show StaticException where
  show (StaticException d) =
    show (D.red (D.text "ERROR!")
          D.<> D.line D.<> d)

instance Exception StaticException

staticError :: Doc -> a
staticError d = throw (StaticException d)

