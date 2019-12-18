module Lib where

--import Data.Function (fix)
import Data.List (unfoldr)

fix :: (a -> a) -> a
fix f = x where x = f x

---

fact :: Integer -> Integer
fact 0 = 1
fact n = n * fact (n - 1)

fact' :: Integer -> Integer
fact' = fix $ \rec n -> case n of
  0 -> 1
  n -> n * rec (n - 1)

nmlist :: Integer -> Integer -> [Integer]
nmlist n m | n > m     = []
           | n == m    = [n]
           | otherwise = n : nmlist (n + 1) m

nmlist' :: Integer -> Integer -> [Integer]
nmlist' = fix $ \rec n m -> case () of
  () | n > m     -> []
     | n == m    -> [n]
     | otherwise -> n : nmlist (n + 1) m

nmlist'' n m = unfoldr f n where
  f x | x > m     = Nothing
      | otherwise = Just (x, x + 1)

---

prod :: Num a => [a] -> a
prod []     = 1
prod (x:xs) = x * prod xs

prod' :: Num a => [a] -> a
prod' = fix $ \rec l -> case l of
  []     -> 1
  (x:xs) -> x * rec xs

prodU :: Num a => ([a] -> a) -> [a] -> a
prodU rec []     = 1
prodU rec (x:xs) = x * rec xs

foldU :: Monoid a => ([a] -> a) -> [a] -> a
foldU rec []     = mempty
foldU rec (x:xs) = x <> rec xs
