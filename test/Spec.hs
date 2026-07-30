{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE NoMonomorphismRestriction #-}

import Test.Hspec

import Control.Arrow ((***))
import Control.Exception (evaluate)
import Control.Monad (forM_)
import Data.Functor (void)
import Data.List (partition)
import qualified Data.Map as M
import System.Directory (doesDirectoryExist, listDirectory)
import System.FilePath ((</>))

import Language.Sparcl.Eval (evalUBind)
import Language.Sparcl.Exception (RunTimeException, StaticException)
import Language.Sparcl.Module
import Language.Sparcl.Name
import Language.Sparcl.Typing.TCMonad (TypingContext, initTypingContext)
import Language.Sparcl.Value (Value (..), eqCheck, runEval)

recursivelyListDirectories :: FilePath -> IO [FilePath]
recursivelyListDirectories dir = do
  entries <- listDirectory dir
  (dirs, files) <-
    fmap
      ((map fst *** map fst) . partition snd)
      (mapM (\fp -> do b <- doesDirectoryExist fp; pure (fp, b)) entries)
  fs <- concat <$> mapM recursivelyListDirectories dirs
  pure (map (dir </>) files ++ fs)

staticError :: Selector StaticException
staticError = const True

runtimeError :: Selector RunTimeException
runtimeError = const True

load :: TypingContext -> FilePath -> IO ()
load tc fp = do
  _ <- evaluate =<< runLoader ["."] 0 tc (readModule fp (\_ _ -> pure []))
  pure ()

loadEval :: TypingContext -> FilePath -> IO (M.Map Name Value)
loadEval tc fp = do
  res <- evaluate =<< runLoader ["."] 0 tc (readModule fp (\env bind -> pure $ M.toList $ runEval (evalUBind env bind)))
  pure $ mcValueTable (miModuleContext res)

checkSame :: (Ord a, Show a) => M.Map a Value -> a -> a -> Expectation
checkSame vt n1 n2 =
  case (M.lookup n1 vt, M.lookup n2 vt) of
    (Just v1, Just v2) -> (v1, v2) `shouldSatisfy` (\(v1', v2') -> eqCheck v1' v2' == Just True)
    (m1, m2) ->
      expectationFailure $
        (case m1 of Nothing -> "undefined name: " ++ show n1 ++ ". "; _ -> "")
          <> (case m2 of Nothing -> "undefined name: " ++ show n2 ++ ". "; _ -> "")

checkTrue :: (Ord a, Show a) => M.Map a Value -> a -> Expectation
checkTrue vt n =
  case M.lookup n vt of
    Just v -> v `shouldSatisfy` ((== Just True) . eqCheck (VCon conTrue []))
    _ -> expectationFailure $ "undefined name: " ++ show n

mkName :: String -> Name
mkName n = Original (ModuleName "Main") (User n) (Bare (User n))

main :: IO ()
main = hspec $ do
  files <- runIO $ recursivelyListDirectories "./Examples"
  let nfiles = ["./TestCases/IllTyped1.sparcl"]
  tc <- runIO initTypingContext
  describe "typechecker" $ do
    forM_ files $ \fp -> it ("accepts file " ++ fp) $ do
      load tc fp `shouldReturn` ()
    forM_ nfiles $ \fp -> it ("should not accept file " ++ fp) $ do
      load tc fp `shouldThrow` staticError

  describe "evaluator" $ do
    forM_ ["./TestCases/RuntimeError1.sparcl", "./TestCases/RuntimeError2.sparcl"] $ \fp ->
      it ("should raise runtime error " ++ fp) $ do
        void (loadEval tc fp) `shouldThrow` runtimeError

    loadEval tc "./Examples/Fib.sparcl" `before` do
      it "satisfies bwd fib (fwd fib 3) == 3 in Fib.sparcl" $ \vt -> do
        checkSame vt (mkName "n0") (mkName "n0'")
      it "satisfies bwd fibI (fwd fibI 3) == 3 in Fib.sparcl" $ \vt -> do
        checkSame vt (mkName "n1") (mkName "n1'")

    loadEval tc "./Examples/ArithmeticCoding.sparcl" `before` do
      it "satisfies check = True in ArithmeticCoding.sparcl" $ \vt -> do
        checkTrue vt (mkName "check")

    loadEval tc "./Examples/LZ77.sparcl" `before` do
      it "satisfies input = input' in LZ77.sparcl" $ \vt -> do
        checkSame vt (mkName "inputList") (mkName "inputList'")

    loadEval tc "./Examples/AddLSB.sparcl" `before` do
      it "satisfies n4 = sub73 in AddLSB.sparcl" $ \vt -> do
        checkSame vt (mkName "n4") (mkName "sub73")