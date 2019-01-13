{-# LANGUAGE DataKinds #-}

module Language.Sparcl.Pass where

data Pass = Parsing | Renaming | TypeCheck
