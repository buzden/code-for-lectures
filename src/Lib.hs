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

---- Res type

newtype Res e a = Res (Either e ([String], a))

getResOut :: Res e a -> Either e [String]
getResOut (Res (Left e))        = Left e
getResOut (Res (Right (ss, _))) = Right ss

instance Functor (Res e) where
  fmap f (Res ei) = Res $ fmap (fmap f) ei

instance Applicative (Res e) where
  pure x = Res $ Right ([], x)
  Res (Left e)  <*> _             = Res $ Left e
  _             <*> Res (Left e)  = Res $ Left e
  Res (Right p) <*> Res (Right q) = Res $ Right $ p <*> q

instance Monad (Res e) where
  Res (Left e)        >>= _ = Res $ Left e
  Res (Right (sl, a)) >>= f = case f a of
    Res (Right (sr, b)) -> Res $ Right (sl ++ sr, b)
    Res er@(Left _)     -> Res er

---- Nice Res-aware instances

instance MonadError e (Res e) where
  throwError = Res . Left

instance PrintConsole (Res e) where
  putStrLn s = Res $ Right ([s], ())

