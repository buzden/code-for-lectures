module Tk

import public Data.So

%default total
%access public export

infix 6 ==., /=.

interface Equ a where
  (==.) : a -> a -> Bool

  eqRefl  : (x : a) -> So (x ==. x)
  eqSymm  : (x, y : a) -> x ==. y = y ==. x
  eqTrans : (x, y, z : a) -> So (x ==. y) -> So (y ==. z) -> So (x ==. z)

  (/=.) : a -> a -> Bool
  x /=. y = not $ x ==. y

  neqIsNotEq : (x, y : a) -> x ==. y = not (x /=. y)

infix 6 <., <=., >., >=.

interface Equ a => Ordu a where
  (<.) : a -> a -> Bool

  ltArefl : (x : a) -> So (not $ x <. x)
  ltAsymm : (x, y : a) -> So (x <. y) -> So (not $ y <. x)
  ltTrans : (x, y, z : a) -> So (x <. y) -> So (y <. z) -> So (x <. z)

  (<=.) : a -> a -> Bool
  x <=. y = x <. y || x ==. y

  lteIsLtOrE : (x, y : a) -> x <=. y = (x <. y || x ==. y)

  (>.) : a -> a -> Bool
  x >. y = y <. x

  gtInverseOfLt : (x, y : a) -> x <. y = y >. x

  (>=.) : a -> a -> Bool
  x >=. y = y <=. x

  gteIsGtOrE : (x, y : a) -> x >=. y = (x >. y || x ==. y)
