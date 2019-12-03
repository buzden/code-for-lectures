module Lib where

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

newtype State a = State {
  getState :: Either Error ([String], a) }

instance Functor State where
  fmap f (State ei) = State $ fmap (fmap f) ei

instance Applicative State where
  pure x = State $ Right ([], x)

instance Monad State where
  st@(State (Left _))     >>= _ = st
  (State (Right (sl, a))) >>= f = case f a of
    Right (sr, b) -> State $ Right (sl ++ sr, b)
    er@(Left e)   -> State er

---- Nice State-aware instances

instance MonadError e (State (Either e a)) where
  throwError = State . Left

instance PrintConsole (State (Either e [String])) where
  putStrLn s = State $ Right ([s], ())

--- Function

data Error = DivByZero

f :: (MonadError Error m, PrintConsole m)
  => Integer -> m ()
f x = do
  when (x == 0) $ throwError DivByZero
  putStrLn $ "100/x is " ++ (show $ 100 / x)

--- Runs

ioFunc :: IO ()
ioFunc = f 5

stFunc :: Either Error [String]
stFunc = getState $ f 5
