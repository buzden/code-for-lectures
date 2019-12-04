{-# LANGUAGE FlexibleContexts #-}

module Main where

import Control.Monad (when)
import Control.Monad.Reader (runReaderT)
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
g = ask >>= f

--- Runs

ioFunc :: IO ()
ioFunc = f 5

rsFunc :: Either Error [String]
rsFunc = unRes $ f 5

rsrGunc :: Either Error [String]
rsrGunc = unFer g 5

ioGunc :: IO ()
ioGunc = g

rsrGunc' :: Integer -> Either Error [String]
rsrGunc' = unRes . runReaderT g

--- Entry point

main :: IO ()
main = do
  ioFunc
  Prelude.putStrLn . show $ rsFunc
  Prelude.putStrLn . show $ rsrGunc
  ioGunc
