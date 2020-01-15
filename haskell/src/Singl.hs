{-# LANGUAGE DataKinds, KindSignatures, PolyKinds, TypeOperators, TypeFamilies #-}

module Singl where

import Data.Singletons (Demote, Sing, SingKind, fromSing, withSomeSing)
import Data.Singletons.Decide ((:~:))
import Prelude hiding (Eq, (==))

class Eq a where
  type (x::a) == (y::a) :: Bool

  (%==) :: Sing (x::a) -> Sing (y::a) -> Sing (x == y)

  eqRefl :: Sing (x::a) -> x == x :~: True
  eqSymm :: Sing (x::a) -> Sing (y::a) -> x == y :~: y == x
  eqTran :: Sing (x::a) -> Sing (y::a) -> Sing (z::a)
         -> x == y :~: True -> y == z :~: True -> x == z :~: True

(==) :: (SingKind m, Eq m) => Demote m -> Demote m -> Bool
x == y = withSomeSing x $ \sX ->
           withSomeSing y $ \sY ->
             fromSing (sX %== sY)
