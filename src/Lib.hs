{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}

module Lib where

import Control.Monad (when)
import Prelude hiding (putStrLn)
import qualified Prelude (putStrLn)

--- Classes

class Monad m => MonadError e m where
  throwError :: e -> m a

class Monad m => PrintConsole m where
  putStrLn :: String -> m ()

--- IO instances

instance Show e => MonadError e IO where
  throwError = error . show

instance PrintConsole IO where
  putStrLn = Prelude.putStrLn

--- Non-IO instances

---- State type

newtype State a = State (Either Error ([String], a))

getStateOut :: State a -> Either Error [String]
getStateOut (State (Left e))        = Left e
getStateOut (State (Right (ss, _))) = Right ss

instance Functor State where
  fmap f (State ei) = State $ fmap (fmap f) ei

instance Applicative State where
  pure x = State $ Right ([], x)

instance Monad State where
  State (Left e)        >>= _ = State $ Left e
  State (Right (sl, a)) >>= f = case f a of
    State (Right (sr, b)) -> State $ Right (sl ++ sr, b)
    State er@(Left _)     -> State er

---- Nice State-aware instances

instance MonadError Error State where
  throwError = State . Left

instance PrintConsole State where
  putStrLn s = State $ Right ([s], ())

--- Function

data Error = DivByZero
  deriving (Show)

f :: (MonadError Error m, PrintConsole m)
  => Integer -> m ()
f x = do
  when (x == 0) $ throwError DivByZero
  putStrLn $ "100/x is " ++ (show $ 100 `div` x)

--- Runs

ioFunc :: IO ()
ioFunc = f 5

stFunc :: Either Error [String]
stFunc = getStateOut $ f 5
