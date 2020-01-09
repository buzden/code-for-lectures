{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE KindSignatures #-}

module Lib where

import Data.Kind (Type)

prepend :: forall (a :: *). a -> [a] -> [a]
prepend x xs = x:xs

prepend' :: forall (a :: Type). a -> [a] -> [a]
prepend' x xs = x:xs
