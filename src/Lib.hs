module Lib where

fact :: Integer -> Integer
fact 0 = 1
fact n = n * fact (n - 1)

nmlist :: Integer -> Integer -> [Integer]
nmlist n m | n > m     = []
           | n == m    = [n]
           | otherwise = n : nmlist (n + 1) m
