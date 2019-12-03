{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}

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

newtype State e a = State (Either e ([String], a))

getStateOut :: State e a -> Either e [String]
getStateOut (State (Left e))        = Left e
getStateOut (State (Right (ss, _))) = Right ss

instance Functor (State e) where
  fmap f (State ei) = State $ fmap (fmap f) ei

instance Applicative (State e) where
  pure x = State $ Right ([], x)
  State (Left e)  <*> _               = State $ Left e
  _               <*> State (Left e)  = State $ Left e
  State (Right p) <*> State (Right q) = State $ Right $ p <*> q

instance Monad (State e) where
  State (Left e)        >>= _ = State $ Left e
  State (Right (sl, a)) >>= f = case f a of
    State (Right (sr, b)) -> State $ Right (sl ++ sr, b)
    State er@(Left _)     -> State er

---- Nice State-aware instances

instance MonadError e (State e) where
  throwError = State . Left

instance PrintConsole (State e) where
  putStrLn s = State $ Right ([s], ())
