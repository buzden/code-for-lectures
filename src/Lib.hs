{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}

module Lib where

import Control.Monad.Except (ExceptT(ExceptT))
import Control.Monad.Reader (ReaderT(ReaderT))
import Control.Monad.State (StateT, modify)
import Control.Monad.Trans.Class (MonadTrans, lift)
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

unRes :: Res e a -> Either e [String]
unRes (Res (Left e))        = Left e
unRes (Res (Right (ss, _))) = Right ss

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

---- Fer type

newtype Fer e r a = Fer (r -> Either e ([String], a))

unFer :: Fer e r a -> r -> Either e [String]
unFer (Fer rei) r = case rei r of
  Left e        -> Left e
  Right (ss, _) -> Right ss

instance Functor (Fer e r) where
  fmap f (Fer rei) = Fer $ fmap (fmap (fmap f)) rei

instance Applicative (Fer e r) where
  pure x = Fer . const $ Right ([], x)
  Fer reil <*> Fer reir = Fer $ \r -> case (reil r, reir r) of
    (Left e , _)       -> Left e
    (_      , Left e)  -> Left e
    (Right p, Right q) -> Right $ p <*> q

instance Monad (Fer e r) where
  Fer rei >>= f = Fer $ \r -> case rei r of
    Left e        -> Left e
    Right (sl, a) -> let Fer fs = f a in case fs r of
      Right (sr, b) -> Right (sl ++ sr, b)
      er@(Left _)   -> er

instance MonadError e (Fer e r) where
  throwError = Fer . const . Left

instance PrintConsole (Fer e r) where
  putStrLn s = Fer . const $ Right ([s], ())

instance MonadReader r (Fer e r) where
  ask = Fer $ \r -> Right ([], r)

---

instance MonadReader Integer IO where
  ask = Prelude.putStrLn "Please enter the number" >> readLn

instance Monad m => MonadError e (ExceptT e m) where
  throwError = ExceptT . pure . Left

---

instance Monad m => MonadReader r (ReaderT r m) where
  ask = ReaderT $ \r -> pure r

instance {-# OVERLAPPABLE #-} (MonadError e m, MonadTrans t, Monad (t m)) => MonadError e (t m) where
  throwError = lift . throwError

instance {-# OVERLAPPABLE #-} (PrintConsole m, MonadTrans t, Monad (t m)) => PrintConsole (t m) where
  putStrLn = lift . putStrLn

instance {-# OVERLAPPABLE #-} (MonadReader r m, MonadTrans t, Monad (t m)) => MonadReader r (t m) where
  ask = lift ask

---

instance Monad m => PrintConsole (StateT [String] m) where
  putStrLn s = modify (++ [s])
