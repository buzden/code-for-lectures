{-# LANGUAGE BlockArguments #-}

module LibSpec where

import Lib
import Test.Hspec
import Test.QuickCheck

spec :: Spec
spec = do

  describe "Semigroup" do

    it "associates" pending -- . property $ \a b c ->

  describe "Monoid" do

    it "left identity" pending -- . property $ \b ->

    it "right identity" pending -- . property $ \a ->

  describe "Functor" do

    it "preserves id" pending -- . property $ \f ->
