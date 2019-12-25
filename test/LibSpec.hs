{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE ScopedTypeVariables #-}

module LibSpec where

import Data.Proxy
import Lib
import Test.Hspec
import Test.QuickCheck

eqProperties :: (Eq a, Arbitrary a) => Proxy a -> Spec
eqProperties _ = describe "Eq typeclass" do

  describe "== operation" do

    it "== reflexivity" . property $ \(x :: a) ->
      x == x `shouldBe` True

    it "== symmetry" . property $ \(x :: a) (y :: a) ->
      x == y ==> y == x `shouldBe` True

  describe "/= operation" do

    it "equals to not ==" . property $ \(x :: a) (y :: a) ->
      x == y ==> not (x /= y) `shouldBe` True

spec :: Spec
spec = do

  describe "Semigroup" do

    it "associates" pending -- . property $ \a b c ->

  describe "Monoid" do

    it "left identity" pending -- . property $ \b ->

    it "right identity" pending -- . property $ \a ->

  describe "Functor" do

    it "preserves id" pending -- . property $ \f ->
