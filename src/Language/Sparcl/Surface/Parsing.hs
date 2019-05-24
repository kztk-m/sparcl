module Language.Sparcl.Surface.Parsing (
  parseExp, parseExp', parseModule, parseDecl
  ) where

-- import Language.Sparcl.Surface.Syntax

-- import Language.Sparcl.Surface.Lexer
-- import Language.Sparcl.Surface.Parser

import Language.Sparcl.Surface.Parser.Exp (parseExp, parseExp', parseModule, parseDecl)
-- import Language.Sparcl.SrcLoc
-- import Language.Sparcl.Pass

-- import qualified Control.Monad.Fail as Fail

-- parseExp :: String -> Either String (LExp 'Parsing)
-- parseExp s = runAlex s pExp 

-- parseExp' :: FilePath -> String -> Either String (LExp 'Parsing)
-- parseExp' fp s = runAlex s (setFilePath fp >> pExp) 

-- parseModule :: FilePath -> String -> Either String (Module 'Parsing)
-- parseModule fp s = runAlex s (setFilePath fp >> pModule) 

-- parseDecl :: String -> Either String (Decls 'Parsing (Loc (TopDecl 'Parsing)))
-- parseDecl s = runAlex s pDecls

-- toIO :: Either String a -> IO a
-- toIO m = case m of
--   Left s  -> Fail.fail s
--   Right a -> return a 

