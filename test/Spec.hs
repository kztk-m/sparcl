{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE NoMonomorphismRestriction #-}

import Test.Hspec

import Control.Arrow ((***))
import Control.Exception (evaluate)
import Control.Monad (forM_)
import Data.Functor (void)
import Data.List (partition, sort)
import qualified Data.Map as M
import System.Directory (doesDirectoryExist, listDirectory)
import System.FilePath ((</>))

import Language.Sparcl.Eval (evalUBind)
import Language.Sparcl.Exception (RunTimeException, StaticException)
import Language.Sparcl.Module
import Language.Sparcl.Name
import Language.Sparcl.Typing.Instance (V (..), unifyPure)
import Language.Sparcl.Multiplicity (Multiplicity (..))
import Language.Sparcl.Pretty (prettyShow)
import Language.Sparcl.Typing.TCMonad (TC, TypingContext, execTCWith, initTypingContext, newMetaKind, newMetaTy, newMetaTyVar, newMetaTyWithKind, unify)
import Language.Sparcl.Typing.Typing (instantiateQ, quantify)
import Language.Sparcl.Typing.Type
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
mkName = mkNameIn "Main"

mkNameIn :: String -> String -> Name
mkNameIn m n = Original (ModuleName m) (User n) (Bare (User n))

-- | Checks @tK = tK'@ for each @tK@ given.
checkExpected :: FilePath -> String -> [String] -> SpecWith (M.Map Name Value)
checkExpected fp m ns =
  forM_ ns $ \n ->
    it ("satisfies " ++ n ++ " = " ++ n ++ "' in " ++ fp) $ \vt ->
      checkSame vt (mkNameIn m n) (mkNameIn m (n ++ "'"))

tNames :: Int -> [String]
tNames n = ["t" ++ show i | i <- [1 .. n]]

-- * Unit tests of binary type applications and their unification
--
-- Stage V1 of the notes (higher-kinded classes). The cases that can be
-- written in programs since stage V3 are tested by samples instead
-- (Examples/KindHigherKinded.sparcl, Nonexamples_Illtyped/Kind*.sparcl);
-- the remaining ones test internal functions directly.

nameEither :: Name
nameEither = nameInBase (User "Either")

nameC :: Name
nameC = nameInBase (User "C")

boolT, intT :: Ty
boolT = TyCon nameTyBool []
intT = TyCon nameTyInt []

nameMaybe :: Name
nameMaybe = nameInBase (User "Maybe")

tyArrKi :: Kind
tyArrKi = arrKi typeKi typeKi

-- | The kind table of the unit tests: the built-in kinds, and Either, Maybe
--   and a class C without parameters.
testKinds :: TypeTable
testKinds =
  M.union (mcTypeTable (miModuleContext baseModuleInfo)) $
    M.fromList
      [ (nameEither, arrKi typeKi tyArrKi)
      , (nameMaybe, tyArrKi)
      , (nameC, typeKi)
      ]

-- | Runs a type-checking computation in a fresh context (no errors left
--   by earlier tests) with the kinds of 'testKinds'.
runTCFresh :: TypingContext -> TC a -> IO a
runTCFresh tc = execTCWith tc M.empty testKinds M.empty M.empty M.empty

unificationSpec :: TypingContext -> Spec
unificationSpec tc = describe "binary type applications (unit tests)" $ do
  it "builds TyCon c [a, b] as TyApp (TyApp (TyConst c) a) b, and matches it back" $ do
    TyCon nameEither [boolT, intT] `shouldBe` TyApp (TyApp (TyConst nameEither) boolT) intT
    splitTyCon (TyApp (TyApp (TyConst nameEither) boolT) intT) `shouldBe` Just (nameEither, [boolT, intT])

  it "does not decompose an instance-argument function type: ?f ?b ~ ({{C}} -> Bool) fails" $
    runTCFresh tc (do f <- newMetaTyWithKind tyArrKi; b <- newMetaTy; unify (TyApp f b) (TyInstFun (TyCon nameC []) boolT))
      `shouldThrow` staticError

  it "fails the occurs check for ?f ?a ~ ?f ?b ?c" $
    runTCFresh tc
      ( do
          f <- newMetaTyWithKind tyArrKi
          [a, b, c] <- mapM (const newMetaTy) [1 :: Int .. 3]
          unify (TyApp f a) (TyApp (TyApp f b) c)
      )
      `shouldThrow` staticError

  describe "unifyPure (instance search)" $ do
    it "unifies ?f ?a with Either Bool Int" $ do
      (f, a) <- runTCFresh tc ((,) <$> newMetaTyWithKind tyArrKi <*> newMetaTy)
      let res = unifyPure testKinds [] True (TyApp f a) (TyCon nameEither [boolT, intT])
      fmap (map (\(v, t) -> (isMetaOf f v, isMetaOf a v, t))) res
        `shouldBe` Just [(False, True, intT), (True, False, TyCon nameEither [boolT])]

    it "does not decompose a function type" $ do
      (f, b) <- runTCFresh tc ((,) <$> newMetaTyWithKind tyArrKi <*> newMetaTy)
      fmap length (unifyPure testKinds [] True (TyApp f b) (intT *-> boolT)) `shouldBe` Nothing

    it "fails the occurs check for ?f ?a ~ ?f ?b ?c" $ do
      f <- runTCFresh tc (newMetaTyWithKind tyArrKi)
      [a, b, c] <- runTCFresh tc (mapM (const newMetaTy) [1 :: Int .. 3])
      fmap length (unifyPure testKinds [] True (TyApp f a) (TyApp (TyApp f b) c)) `shouldBe` Nothing

    it "binds only to an expression of the same kind" $ do
      f <- runTCFresh tc (newMetaTyWithKind (arrKi tyArrKi typeKi))
      a <- runTCFresh tc (newMetaTyWithKind tyArrKi)
      fmap length (unifyPure testKinds [] True (TyApp f a) (TyCon nameMaybe [intT])) `shouldBe` Nothing
  where
    isMetaOf (TyMetaV m) (VM m') = m == m'
    isMetaOf _ _ = False

-- * Unit tests of kinds (stage V2-1 of the notes; kinds are not checked yet)

kindSpec :: TypingContext -> Spec
kindSpec tc = describe "kinds (unit tests)" $ do
  let tbl = mcTypeTable (miModuleContext baseModuleInfo)
      nameMany = nameInBase (User "Many")
      tyArr = arrKi typeKi typeKi
  it "gives the kinds of built-in type constructors" $ do
    kindOf tbl (TyConst nameMany) `shouldBe` arrKi multKi tyArr
    kindOf tbl (TyCon nameMany [TyMult Omega]) `shouldBe` tyArr
    kindOf tbl (TyConst nameTyRev) `shouldBe` tyArr
    kindOf tbl (TyCon nameTyRev [intT]) `shouldBe` typeKi
  it "computes the kinds of tuple constructors from their names" $ do
    kindOf tbl (TyConst (nameTyTuple 3)) `shouldBe` arrKi typeKi (arrKi typeKi tyArr)
    kindOf tbl (TyCon (nameTyTuple 2) [intT, boolT]) `shouldBe` typeKi
    kindOf tbl (TyCon (nameTyWTuple 2) [intT]) `shouldBe` tyArr
  it "takes the kinds of variables and metas from themselves" $ do
    let f = BoundTv (mkName "f") tyArr
    kindOf tbl (TyApp (TyVar f) intT) `shouldBe` typeKi
    m <- runTCFresh tc (newMetaTyWithKind tyArr)
    kindOf tbl m `shouldBe` tyArr
    kindOf tbl (TyApp m boolT) `shouldBe` typeKi
  it "gives Type to function types and Multiplicity to multiplicities" $ do
    kindOf tbl (intT *-> boolT) `shouldBe` typeKi
    kindOf tbl (TyInstFun (TyCon nameC []) boolT) `shouldBe` typeKi
    kindOf tbl (TyMult One) `shouldBe` multKi
  it "prints kinds with a right-associative arrow" $ do
    prettyShow (arrKi tyArr typeKi) `shouldBe` "(Type -> Type) -> Type"
    prettyShow (arrKi multKi tyArr) `shouldBe` "Multiplicity -> Type -> Type"

-- * Unit tests of kinds in instantiation and generalization (stage V2-2 of
--   the notes; kind inference and checking of written types are tested by
--   samples since stage V3)

kindCheckSpec :: TypingContext -> Spec
kindCheckSpec tc = describe "kinds in instantiation and generalization (unit tests)" $ do
  let binderKinds (TyForAll vs _) = map tyVarKind vs
      binderKinds _ = []

  it "instantiates a binder with a meta of its kind" $ do
    let p = BoundTv (mkName "p") multKi
    TyQual _ t <- runTCFresh tc $ instantiateQ (TyForAll [p] (TyQual [] (TyVar p)))
    case t of
      TyMetaV m -> metaKind m `shouldBe` multKi
      _ -> expectationFailure "not a meta"

  it "generalizes a meta to a binder of its kind, defaulting kind metas to Type" $ do
    t <- runTCFresh tc $ do
      m <- newMetaTyVar multKi
      quantify [m] (TyQual [] (TyMetaV m))
    binderKinds t `shouldBe` [multKi]
    t' <- runTCFresh tc $ do
      k <- newMetaKind
      m <- newMetaTyVar k
      quantify [m] (TyQual [] (TyMetaV m))
    binderKinds t' `shouldBe` [typeKi]

main :: IO ()
main = hspec $ do
  files <- runIO $ recursivelyListDirectories "./Examples"
  nfiles <- runIO $ recursivelyListDirectories "./Nonexamples_Illtyped"
  tc <- runIO initTypingContext
  describe "typechecker" $ do
    forM_ (sort files) $ \fp -> it ("should accept file " ++ fp) $ do
      load tc fp `shouldReturn` ()
    forM_ (sort nfiles) $ \fp -> it ("should not accept file " ++ fp) $ do
      load tc fp `shouldThrow` staticError

  unificationSpec tc
  kindSpec tc
  kindCheckSpec tc

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

    -- type classes
    forM_
      [ ("ClassEq.sparcl", "Main", tNames 9)
      , ("ClassOrd.sparcl", "Main", tNames 6)
      , ("ClassMultiParam.sparcl", "Main", tNames 6)
      , ("ClassInvertible.sparcl", "Main", tNames 9)
      , ("ClassRevClauses.sparcl", "Main", tNames 3)
      , ("ClassCyclic.sparcl", "Main", tNames 4)
      , ("ClassModC.sparcl", "Examples.ClassModC", tNames 4)
      , ("ClassTrailingWhere.sparcl", "Main", tNames 2)
      , ("ClassInstPatAnnotated.sparcl", "Main", tNames 3)
      , ("ClassMethodWithoutParam.sparcl", "Main", tNames 2)
      , ("ClassInstArgInList.sparcl", "Main", tNames 2)
      , ("HigherRankLetCase.sparcl", "Main", ["t6", "t7"])
      , -- a class application written with a synonym
        ("KindSynonym.sparcl", "Main", ["t1"])
      , ("KindHigherKinded.sparcl", "Main", tNames 7)
      , ("ClassFunctor.sparcl", "Main", tNames 7)
      , ("ClassHigherKinded.sparcl", "Main", tNames 5)
      ]
      $ \(f, m, ns) ->
        loadEval tc ("./Examples" </> f) `before` checkExpected f m ns