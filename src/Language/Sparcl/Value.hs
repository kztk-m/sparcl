module Language.Sparcl.Value where

import           Language.Sparcl.Pretty    as D

import           Control.DeepSeq
import qualified Data.Map                  as M

import           Control.Monad.Reader

import           Language.Sparcl.Exception
import           Language.Sparcl.Literal
import           Language.Sparcl.Name

import           Control.Monad.Fail
import           Control.Monad.Fix         (MonadFix (..))

data Value = VCon !Name ![Value]
           | VLit !Literal
           | VFun !(Value -> Eval Value)
           | VRes !(Heap -> Eval Value) !(Value -> Eval Heap)

newtype Eval a = MkEval (Reader Int a) deriving (Functor, Applicative, Monad, MonadReader Int, MonadFix)

runEval :: Eval a -> a
runEval (MkEval a) = runReader a 0

instance MonadFail Eval where
  fail = cannotHappen . D.text

type ValueTable = M.Map Name Value
type Env = M.Map Name Value

instance NFData Value where
  rnf (VCon c vs) = rnf (c, vs)
  rnf (VLit l)    = rnf l
  rnf (VFun _)    = ()
  rnf (VRes _ _)  = ()


instance Pretty Value where
  pprPrec _ (VCon c vs) | Just _ <- checkNameTuple c =
    D.tupled (map (pprPrec 0) vs)
  pprPrec _ (VCon c []) = ppr c
  pprPrec k (VCon c vs) = parensIf (k > 9) $
    ppr c D.<+> D.hsep [ pprPrec 10 v | v <- vs ]

  pprPrec _ (VLit l) = ppr l
  pprPrec _ (VFun _) = D.text "<function>"
  pprPrec _ (VRes _ _) = D.text "<reversible computation>"


-- type Eval = ReaderT Int (Either String)

extendsEnv :: [(Name, Value)] -> Env -> Env
extendsEnv nvs env = foldr (uncurry extendEnv) env nvs

lookupEnv :: Name -> Env -> Eval Value
lookupEnv n env = case M.lookup n env of
  Nothing -> rtError $ D.text "Undefined variable:" D.<+> ppr n
                       D.</> D.text "Searched through: " D.<+>
                       ppr (M.keys env)
    -- -- if nothing, we treat the variable were reversible one.
    -- return $ VRes (lookupEnvR n) (return . singletonEnv n)
  Just v  -> return v

singletonEnv :: Name -> Value -> Env
singletonEnv = M.singleton

extendEnv :: Name -> Value -> Env -> Env
extendEnv = M.insert

unionEnv :: Env -> Env -> Env
unionEnv = M.union

emptyEnv :: Env
emptyEnv = M.empty

pprEnv :: Env -> Doc
pprEnv env =
  D.sep [ ppr k D.<+> D.text "=" D.<+> ppr v
        | (k, v) <- M.toList env ]

evalTest :: Eval a -> IO a
evalTest a = return $ runEval a
  -- case runReaderT a 0 of
  --   Left  s -> Fail.fail s
  --   Right v -> return v

type Addr = Int
type Heap = M.Map Addr Value

pprHeap :: Heap -> Doc
pprHeap heap =
  D.encloseSep (D.text "{") (D.text "}") (D.comma D.<> D.space) $
    [ ppr k D.<+> D.text "=" D.<+> ppr v
      | (k, v) <- M.toList heap ]

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
  Nothing -> rtError $ D.text "Undefined addr" D.<+> D.ppr n D.<+> D.text "in" D.<+> pprHeap heap
  Just v  -> return v

extendHeap :: Addr -> Value -> Heap -> Heap
extendHeap = M.insert

unionHeap :: Heap -> Heap -> Heap
unionHeap = M.union

emptyHeap :: Heap
emptyHeap = M.empty

removeHeap :: Addr -> Heap -> Heap
removeHeap = M.delete

removesHeap :: [Addr] -> Heap -> Heap
removesHeap xs heap = foldl (flip removeHeap) heap xs

singletonHeap :: Addr -> Value -> Heap
singletonHeap = M.singleton

