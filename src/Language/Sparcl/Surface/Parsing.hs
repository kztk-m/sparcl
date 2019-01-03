module Language.Sparcl.Surface.Parsing (
  parseExp, parseModule, parseDecl,
  parseExpTest, parseDeclTest, parseModuleTest

  ) where

import Language.Sparcl.Surface.Syntax

import Language.Sparcl.Surface.Lexer
import Language.Sparcl.Surface.Parser
import Language.Sparcl.SrcLoc

import qualified Control.Monad.Fail as Fail

parseExp :: String -> Either String LExp
parseExp s = runAlex s pExp 

parseModule :: FilePath -> String -> Either String Module
parseModule fp s = runAlex s (setFilePath fp >> pModule) 

parseDecl :: String -> Either String [Loc TopDecl]
parseDecl s = runAlex s pDecls

toIO :: Either String a -> IO a
toIO m = case m of
  Left s  -> Fail.fail s
  Right a -> return a 

parseExpTest :: String -> IO LExp
parseExpTest = toIO . parseExp

parseDeclTest :: String -> IO [Loc TopDecl]
parseDeclTest = toIO . parseDecl 

parseModuleTest :: FilePath -> String -> IO Module
parseModuleTest fp = toIO . parseModule fp 
