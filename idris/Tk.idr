module Tk

import Data.So

interface Eq a where
  (==) : a -> a -> Bool

  eqReflexivity  : (x : a) -> So (x == x)
  eqSymmetricity : (x, y : a) -> x == y = y == x
  eqTransitivity : (x, y, z : a) -> So (x == y) -> So (y == z) -> So (x == z)

  (/=) : a -> a -> Bool

  eqIsNotNeq : (x, y : a) -> x == y = not (x /= y)

interface Tk.Eq a => Ord a where
  (<) : a -> a -> Bool

  ltAntireflexivity : (x : a) -> So (not $ x < x)
  ltAntisymmetry : (x, y : a) -> x < y = not (y < x)
  ltTransitivity : (x, y, z : a) -> So (x < y) -> So (y < z) -> So (x < z)

  (<=) : a -> a -> Bool

  lteIsLtOrE : (x, y : a) -> x <= y = (x < y || x == y)

  (>) : a -> a -> Bool

  ltInverseOfGt : (x, y : a) -> x < y = y > x

  (>=) : a -> a -> Bool

  gteIsGtOrE : (x, y : a) -> x >= y = (x > y || x == y)
