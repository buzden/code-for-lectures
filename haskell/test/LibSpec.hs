{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ExplicitForAll #-}

module LibSpec where

import Data.Proxy
import Lib
import Test.Hspec
import Test.Hspec.QuickCheck (modifyMaxDiscardRatio, prop)
import Test.QuickCheck

eqLaws :: forall a. (Eq a, Arbitrary a, Show a) => Proxy a -> Spec
eqLaws _ = describe "Eq typeclass" do

  describe "== operation" do

    prop "== reflexivity" $ \(x::a) ->
      x == x

    prop "== symmetry" $ \(x::a) (y::a) ->
      (x == y) === (y == x)

    modifyMaxDiscardRatio (*10^6) .
      prop "== transitivity" $ \(x::a) (y::a) (z::a) ->
        x == y && y == z ==> x == z

  describe "/= operation" do

    prop "equals to not ==" $ \(x::a) (y::a) ->
      (x == y) === not (x /= y)

ordLaws :: forall a. (Ord a, Arbitrary a, Show a) => Proxy a -> Spec
ordLaws _ = describe "Ord typeclass" do

  describe "< operation" do

    prop "< anti-reflexivity" $ \(x::a) ->
      not (x < x)

    prop "< anti-symmetry" $ \(x::a) (y::a) ->
      x < y ==> not (y < x)

    prop "< transitivity" $ \(x::a) (y::a) (z::a) ->
      x < y && y < z ==> x < z

  describe "<= operation" do

    prop "is < or ==" $ \(x::a) (y::a) ->
      (x <= y) === (x < y || x == y)

  describe "> operation" do

    prop "is not <" $ \(x::a) (y::a) ->
      (x > y) === (y < x)

  describe ">= operation" do

    prop "is > or =" $ \(x::a) (y::a) ->
      (x >= y) === (x > y || x == y)

spec :: Spec
spec = do

  describe "Int type" do
    let prx = Proxy :: Proxy Int

    eqLaws prx
    ordLaws prx

  describe "Semigroup" do

    it "associates" pending -- . property $ \a b c ->

  describe "Monoid" do

    it "left identity" pending -- . property $ \b ->

    it "right identity" pending -- . property $ \a ->

  describe "Functor" do

    it "preserves id" pending -- . property $ \f ->
