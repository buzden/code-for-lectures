module Tk

import public Data.So

%default total
%access public export

infix 6 ==., /=.

interface Equ a where
  (==.) : a -> a -> Bool

  eqReflexivity  : (x : a) -> So (x ==. x)
  eqSymmetricity : (x, y : a) -> So (x ==. y) -> So (y ==. x)
  eqTransitivity : (x, y, z : a) -> So (x ==. y) -> So (y ==. z) -> So (x ==. z)

  (/=.) : a -> a -> Bool
  x /=. y = not $ x ==. y

  neqIsNotEq : (x, y : a) -> x ==. y = not (x /=. y)

infix 6 <., <=., >., >=.

interface Equ a => Ordu a where
  (<.) : a -> a -> Bool

  ltAntireflexivity : (x : a) -> So (not $ x <. x)
  ltAntisymmetry : (x, y : a) -> So (x <. y) -> So (not $ y <. x)
  ltTransitivity : (x, y, z : a) -> So (x <. y) -> So (y <. z) -> So (x <. z)

  (<=.) : a -> a -> Bool
  x <=. y = x <. y || x ==. y

  lteIsLtOrE : (x, y : a) -> x <=. y = (x <. y || x ==. y)

  (>.) : a -> a -> Bool
  x >. y = not $ x <. y

  gtInverseOfLt : (x, y : a) -> So (x <. y) -> So(y >. x)

  (>=.) : a -> a -> Bool
  x >=. y = not $ x <=. y

  gteIsGtOrE : (x, y : a) -> x >=. y = (x >. y || x ==. y)
