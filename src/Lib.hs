{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE KindSignatures #-}

module Lib where

prepend :: forall (a :: *). a -> [a] -> [a]
prepend x xs = x:xs
