{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ExplicitForAll #-}

module LibSpec where

import Data.Proxy
import Lib
import Test.Hspec
import Test.Hspec.QuickCheck (modifyMaxDiscardRatio)
import Test.QuickCheck

eqProperties :: forall a. (Eq a, Arbitrary a, Show a) => Proxy a -> Spec
eqProperties _ = describe "Eq typeclass" do

  describe "== operation" do

    it "== reflexivity" . property $ \(x :: a) ->
      x == x

    it "== symmetry" . property $ \(x :: a) (y :: a) ->
      (x == y) === (y == x)

    modifyMaxDiscardRatio (*10^6) . it "== transitivity" . property $ \(x :: a) (y :: a) (z :: a) ->
      x == y && y == z ==> x == z

  describe "/= operation" do

    it "equals to not ==" . property $ \(x :: a) (y :: a) ->
      (x == y) === not (x /= y)

ordProperties :: forall a. (Ord a, Arbitrary a, Show a) => Proxy a -> Spec
ordProperties _ = describe "Ord typeclass" do

  describe "< operation" do

    it "< anti-reflexivity" . property $ \(x :: a) ->
      not (x < x)

    it "< anti-symmetry" . property $ \(x :: a) (y :: a) ->
      x < y ==> not (y < x)

    it "< transitivity" . property $ \(x :: a) (y :: a) (z :: a) ->
      x < y && y < z ==> x < z

  describe "<= operation" do

    it "<= is < or ==" . property $ \(x :: a) (y :: a) ->
      (x <= y) === (x < y || x == y)

  describe "> operation" do

    it "> is not <" . property $ \(x :: a) (y :: a) ->
      (x > y) === (y < x)

  describe ">= operation" do

    it ">= is > or =" . property $ \(x :: a) (y :: a) ->
      (x >= y) === (x > y || x == y)

spec :: Spec
spec = do

  describe "Int type" do
    let prx = Proxy :: Proxy Int

    eqProperties prx
    ordProperties prx

  describe "Semigroup" do

    it "associates" pending -- . property $ \a b c ->

  describe "Monoid" do

    it "left identity" pending -- . property $ \b ->

    it "right identity" pending -- . property $ \a ->

  describe "Functor" do

    it "preserves id" pending -- . property $ \f ->
