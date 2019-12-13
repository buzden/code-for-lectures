{-# LANGUAGE BlockArguments #-}

module LibSpec where

import Lib
import Test.Hspec
import Test.QuickCheck

spec :: Spec
spec = do

  describe "Factorial function" do

    it "calculates right answer" . property $ \(NonNegative n) ->
      fact n === product [1 .. n]

    it "two variants are same" . property $ \(NonNegative n) ->
      fact n === fact' n

  describe "N-M-List function" do

    it "calculates right answer" . property $ \n m ->
      nmlist n m === [n .. m]

    it "two variants are same" pending
