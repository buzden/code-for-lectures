{-# LANGUAGE FlexibleContexts #-}

module Main where

import Control.Monad (when)
import Lib
import Prelude hiding (putStrLn)
import qualified Prelude (putStrLn)

--- Function

data Error = DivByZero
  deriving (Show)

f :: (MonadError Error m, PrintConsole m)
  => Integer -> m ()
f x = do
  when (x == 0) $ throwError DivByZero
  putStrLn $ "100/x is " ++ (show $ 100 `div` x)

g :: (MonadError Error m, PrintConsole m,
      MonadReader Integer m) => m ()
g = do
  x <- ask
  when (x == 0) $ throwError DivByZero
  putStrLn $ "100/x is " ++ (show $ 100 `div` x)

--- Runs

ioFunc :: IO ()
ioFunc = f 5

rsFunc :: Either Error [String]
rsFunc = getResOut $ f 5

rsrFunc :: Either Error [String]
rsrFunc = getResROut g 5

--- Entry point

main :: IO ()
main = ioFunc >> (Prelude.putStrLn $ show $ rsFunc)
