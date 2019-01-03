module Language.Sparcl.Value where

import Language.Sparcl.Pretty 
import qualified Text.PrettyPrint.ANSI.Leijen as D

import qualified Data.Map as M
import Control.DeepSeq 

import Control.Monad.Reader

import Language.Sparcl.Literal
import Language.Sparcl.Name
import Language.Sparcl.Exception 


data Value = VCon QName [Value]
           | VBang Value
           | VLit Literal
           | VFun (Value -> Eval Value) 
           | VRes (Heap -> Eval Value) (Value -> Eval Heap) 

type Eval = Reader Int 

type ValueTable = M.Map QName Value 
type Env = M.Map QName Value

instance NFData Value where
  rnf (VCon c vs) = rnf (c, vs)
  rnf (VBang v)   = rnf v
  rnf (VLit l)    = rnf l
  rnf (VFun _)    = ()
  rnf (VRes _ _)  = ()
  

instance Pretty Value where
  pprPrec _ (VCon c []) = ppr c 
  pprPrec k (VCon c vs) = parensIf (k > 9) $ 
    ppr c D.<+> D.hsep [ pprPrec 10 v | v <- vs ]

  pprPrec k (VBang e) = parensIf (k > 9) $
    D.text "!" D.<+> pprPrec 9 e 
  pprPrec _ (VLit l) = ppr l
  pprPrec _ (VFun _) = D.text "<function>"
  pprPrec _ (VRes _ _) = D.text "<reversible computation>"


-- type Eval = ReaderT Int (Either String)

extendsEnv :: [(QName, Value)] -> Env -> Env
extendsEnv nvs env = foldr (uncurry extendEnv) env nvs 
   
lookupEnv :: QName -> Env -> Eval Value
lookupEnv n env = case M.lookup n env of
  Nothing -> rtError $ D.text "Undefined variable:" D.<+> ppr n
                       D.</> D.text "Searched through: " D.<+>
                       ppr [ k | k <- M.keys env ]
    -- -- if nothing, we treat the variable were reversible one. 
    -- return $ VRes (lookupEnvR n) (return . singletonEnv n)
  Just v  -> return v

singletonEnv :: QName -> Value -> Env
singletonEnv = M.singleton 

extendEnv :: QName -> Value -> Env -> Env
extendEnv q v env = M.insert q v env 

unionEnv :: Env -> Env -> Env
unionEnv env1 env2 = M.union env1 env2 

emptyEnv :: Env
emptyEnv = M.empty 

pprEnv :: Env -> Doc
pprEnv env =
  D.sep [ ppr k D.<+> D.text "=" D.<+> ppr v
        | (k, v) <- M.toList env ] 

runEval :: Eval a -> a
runEval a = runReader a 0 

evalTest :: Eval a -> IO a
evalTest a = return $ runReader a 0 
  -- case runReaderT a 0 of
  --   Left  s -> Fail.fail s
  --   Right v -> return v 

type Addr = Int 
type Heap = M.Map Addr Value 

newAddr :: (Addr -> Eval a) -> Eval a
newAddr f = do
  i <- ask
  local (+1) $ f i 

newAddrs :: Int -> ([Addr] -> Eval a) -> Eval a
newAddrs n f = do
  i <- ask
  local (+n) $ f [i..i+n-1]


lookupHeap :: Addr -> Heap -> Eval Value 
lookupHeap n heap = case M.lookup n heap of
  Nothing -> rtError $ D.text "Undefined addr"
  Just v  -> return v

extendHeap :: Addr -> Value -> Heap -> Heap
extendHeap = M.insert 

unionHeap :: Heap -> Heap -> Heap
unionHeap = M.union

emptyHeap :: Heap
emptyHeap = M.empty 

removeHeap :: Addr -> Heap -> Heap
removeHeap x h = M.delete x h

removesHeap :: [Addr] -> Heap -> Heap
removesHeap xs h = foldl (\h x -> removeHeap x h) h xs 

singletonHeap :: Addr -> Value -> Heap 
singletonHeap = M.singleton 


    

