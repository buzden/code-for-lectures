module Lib where

import Data.Function (fix)

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
