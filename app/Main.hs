module Main where

import Lib

main :: IO ()
main = ioFunc >> (Prelude.putStrLn $ show $ stFunc)
