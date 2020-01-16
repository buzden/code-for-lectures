module ListTk

import Tk

(&&) : So p -> So q -> So (p && q)
Oh && Oh = Oh

soSplit : So (p && q) -> (So p, So q)
soSplit {p=True} Oh = (Oh, Oh)

Equ a => Equ (List a) where
  []      ==. []      = True
  (x::xs) ==. (y::ys) = x ==. y && xs ==. ys
  _       ==. _       = False

  eqReflexivity []      = Oh
  eqReflexivity (x::xs) = eqReflexivity x && eqReflexivity xs

  eqSymmetricity []      []      = Refl
  eqSymmetricity []      (x::xs) = Refl
  eqSymmetricity (x::xs) []      = Refl
  eqSymmetricity (x::xs) (y::ys) = rewrite eqSymmetricity x y in
                                   rewrite eqSymmetricity xs ys in
                                   Refl

  eqTransitivity []      []       []     _ _ = Oh
  eqTransitivity (x::xs) (y::ys) (z::zs) p q with (soSplit p, soSplit q)
    | ((rxy, rxys), (ryz, ryzs)) = eqTransitivity x y z rxy ryz && eqTransitivity xs ys zs rxys ryzs

  neqIsNotEq []      []      = Refl
  neqIsNotEq []      (x::xs) = Refl
  neqIsNotEq (x::xs) []      = Refl
  neqIsNotEq (x::xs) (y::ys) with (x ==. y && xs ==. ys)
    | True  = Refl
    | False = Refl

Ordu a => Ordu (List a) where
  []     <. (_::_) = True
  []     <. []     = False
  (_::_) <. []     = False
  (x::_) <. (y::_) = x <. y

  ltAntireflexivity []     = Oh
  ltAntireflexivity (x::_) = ltAntireflexivity x

  ltAntisymmetry []     [] _     = Oh
  ltAntisymmetry []     (_::_) _ = Oh
  ltAntisymmetry (x::_) (y::_) p = ltAntisymmetry x y p

  ltTransitivity []     (_::_) (_::_) _ _ = Oh
  ltTransitivity (x::_) (y::_) (z::_) p q = ltTransitivity x y z p q

  lteIsLtOrE _ _ = Refl

  gtInverseOfLt _ _ = Refl

  gteIsGtOrE n m = rewrite eqSymmetricity n m in Refl
