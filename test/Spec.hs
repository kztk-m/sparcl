{-# LANGUAGE TemplateHaskell, QuasiQuotes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# OPTIONS_GHC -fno-defer-out-of-scope-variables -fno-defer-type-errors #-}

import Language.Sparcl.Runtime
import Language.Sparcl.Base

import Language.Sparcl.TH


-- [sparcl| def f = 1 |]
[sparclf|./examples/t1.sparcl|]
[sparclf|./examples/s2l.sparcl|]

 
deriving instance Show(Nat)
 
main :: IO ()
main =
  print q0 
