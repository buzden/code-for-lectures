{-# LANGUAGE DataKinds, KindSignatures, PolyKinds, TypeOperators, TypeFamilies #-}
{-# LANGUAGE GADTs, UndecidableInstances #-}

module Singl where

import Data.Singletons (Demote, Sing, SingKind, fromSing, withSomeSing)
import Data.Singletons.Decide ((:~:)(..))
import Data.Singletons.Prelude.Bool
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

--- Instance ---

data List a = Nil | Cons a (List a)

data instance Sing (xs :: List a) where
    SNil  :: Sing Nil
    SCons :: Sing x -> Sing xs -> Sing (Cons x xs)

instance Eq a => Eq (List a) where
  type Nil       == Nil       = True
  type Nil       == Cons _ _  = False
  type Cons _ _  == Nil       = False
  type Cons x xs == Cons y ys = x == y && xs == ys

  SNil       %== SNil       = STrue
  SNil       %== SCons _ _  = SFalse
  SCons _ _  %== SNil       = SFalse
  SCons x xs %== SCons y ys = x %== y %&& xs %== ys

  eqRefl SNil         = Refl
  eqRefl (SCons x xs) = case (eqRefl x, eqRefl xs) of
    (Refl, Refl) -> Refl

  eqSymm SNil SNil = Refl
  eqSymm SNil (SCons _ _) = Refl
  eqSymm (SCons _ _) SNil = Refl
  eqSymm (SCons x xs) (SCons y ys) = case (eqSymm x y, eqSymm xs ys) of
    (Refl, Refl) -> Refl

  eqTran SNil SNil SNil Refl Refl = Refl
  eqTran xs ys zs p q = undefined
