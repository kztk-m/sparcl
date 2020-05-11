module Language.Sparcl.Base where

import           Language.Sparcl.Runtime

import           Data.Function           (on)
import           Data.Ratio              (Rational)
import qualified Data.Ratio              ((%))


newtype Un a = U a

liftFunc :: (a -> b) -> a -> R b
liftFunc f a = return (f a)

liftFunc2 :: (a -> b -> c) -> a -> R (b -> R c)
liftFunc2 f = liftFunc (liftFunc . f)

(+) :: Int -> R (Int -> R Int)
(+) = liftFunc2 (Prelude.+)

(-) :: Int -> R (Int -> R Int)
(-) = liftFunc2 (Prelude.-)

(*) :: Int -> R (Int -> R Int)
(*) = liftFunc2 (Prelude.*)

(%) :: Int -> R (Int -> R Rational)
(%) = liftFunc2 ((Data.Ratio.%) `on` fromIntegral)

(+%) :: Rational -> R (Rational -> R Rational)
(+%) = liftFunc2 (Prelude.+)

(-%) :: Rational -> R (Rational -> R Rational)
(-%) = liftFunc2 (Prelude.-)

(*%) :: Rational -> R (Rational -> R Rational)
(*%) = liftFunc2 (Prelude.*)

(/%) :: Rational -> R (Rational -> R Rational)
(/%) = liftFunc2 (Prelude./)

eqInt :: Int -> R (Int -> R Bool)
eqInt = liftFunc2 (==)

eqChar :: Char -> R (Char -> R Bool)
eqChar = liftFunc2 (==)

eqRational :: Rational -> R (Rational -> R Bool)
eqRational = liftFunc2 (==)

leInt :: Int -> R (Int -> R Bool)
leInt = liftFunc2 (<=)

leChar :: Char -> R (Char -> R Bool)
leChar = liftFunc2 (<=)

leRational :: Rational -> R (Rational -> R Bool)
leRational = liftFunc2 (<=)


ltInt :: Int -> R (Int -> R Bool)
ltInt = liftFunc2 (<)

ltChar :: Char -> R (Char -> R Bool)
ltChar = liftFunc2 (<)

ltRational :: Rational -> R (Rational -> R Bool)
ltRational = liftFunc2 (<)


