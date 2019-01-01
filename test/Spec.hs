-- import Language.Sparcl.Untyped.Syntax
-- import Language.Sparcl.Untyped.Parsing
-- import Language.Sparcl.Untyped.Desugar as Desugar
-- import Language.Sparcl.Untyped.Desugar.Syntax as Desugar
import Language.Sparcl.Module 

-- import Language.Sparcl.Untyped.Eval 
-- import qualified Data.Map as M 

-- import Language.Sparcl.Typing.TC
-- import Language.Sparcl.Typing.Typing 

-- import Language.Sparcl.SrcLoc
import Language.Sparcl.Pretty 
-- import Language.Sparcl.Name

main :: IO ()
main = do
  m <- runM ["."] $ readModule "./examples/t2.sparcl"
  -- p <- parseDeclTest s
  -- putStrLn "Parsed" 
  -- prettyPutLn p
  -- putStrLn "-- --------------------" 
  -- (p', _, _, _, _) <- desugarTest ["Main"] [] M.empty $ desugarTopDecls p
  -- putStrLn "Desugared" 
  -- prettyPutLn p'

  -- putStrLn "-- --------------------"

  -- let tenv = M.fromList [ (conTrue, boolTy), (conFalse, boolTy) ]
  -- let (nts, _) = runTC (initTInfo tenv M.empty) $
  --                inferDecls p' 

  -- print nts 
  
  -- env <- evalTest $ do 
  --   evalUDecls emptyEnv p'
  --   -- evalU env (noLoc $ Desugar.Var $ BName (NormalName "q0"))
  -- print (pprEnv env) 
  print (pprMap $ miTypeTable m)
  print (pprMap $ miValueTable m)
