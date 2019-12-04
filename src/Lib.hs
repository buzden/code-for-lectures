{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE FunctionalDependencies #-}

module Lib where

import Control.Monad.Reader (ReaderT(ReaderT))
import Prelude hiding (putStrLn)
import qualified Prelude (putStrLn)

--- Classes

class Monad m => MonadError e m where
  throwError :: e -> m a

class Monad m => PrintConsole m where
  putStrLn :: String -> m ()

class Monad m => MonadReader r m | m -> r where
  ask :: m r

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

---- ResR type

newtype ResR e r a = ResR (r -> Either e ([String], a))

getResROut :: ResR e r a -> r -> Either e [String]
getResROut (ResR rei) r = case rei r of
  Left e        -> Left e
  Right (ss, _) -> Right ss

instance Functor (ResR e r) where
  fmap f (ResR rei) = ResR $ fmap (fmap (fmap f)) rei

instance Applicative (ResR e r) where
  pure x = ResR . const $ Right ([], x)
  ResR reil <*> ResR reir = ResR $ \r -> case (reil r, reir r) of
    (Left e , _)       -> Left e
    (_      , Left e)  -> Left e
    (Right p, Right q) -> Right $ p <*> q

instance Monad (ResR e r) where
  ResR rei >>= f = ResR $ \r -> case rei r of
    Left e        -> Left e
    Right (sl, a) -> let ResR fs = f a in case fs r of
      Right (sr, b) -> Right (sl ++ sr, b)
      er@(Left _)   -> er

instance MonadError e (ResR e r) where
  throwError = ResR . const . Left

instance PrintConsole (ResR e r) where
  putStrLn s = ResR . const $ Right ([s], ())

instance MonadReader r (ResR e r) where
  ask = ResR $ \r -> Right ([], r)

---

instance MonadReader Integer IO where
  ask = Prelude.putStrLn "Please enter the number" >> readLn

---

instance Monad m => MonadReader r (ReaderT r m) where
  ask = ReaderT $ \r -> pure r

instance MonadError e m => MonadError e (ReaderT r m) where
  throwError = ReaderT . const . throwError

instance PrintConsole m => PrintConsole (ReaderT r m) where
  putStrLn = ReaderT . const . putStrLn

---

--instance Monad m => PrintConsole (StateT [String] m) where
--  putStrLn s = update (++ [s])
