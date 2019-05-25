module Language.Sparcl.Base where

import Language.Sparcl.Runtime

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

eqInt :: Int -> R (Int -> R Bool)
eqInt = liftFunc2 (==)

eqChar :: Char -> R (Char -> R Bool)
eqChar = liftFunc2 (==)

ltInt :: Int -> R (Int -> R Bool)
ltInt = liftFunc2 (<)

ltChar :: Char -> R (Char -> R Bool)
ltChar = liftFunc2 (<)
