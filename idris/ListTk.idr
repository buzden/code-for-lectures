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

  eqRefl []      = Oh
  eqRefl (x::xs) = eqRefl x && eqRefl xs

  eqSymm []      []      = Refl
  eqSymm []      (_::_)  = Refl
  eqSymm (_::_)  []      = Refl
  eqSymm (x::xs) (y::ys) = rewrite eqSymm x y in
                           rewrite eqSymm xs ys in
                           Refl

  eqTrans []      []       []     _ _ = Oh
  eqTrans (x::xs) (y::ys) (z::zs) p q with (soSplit p, soSplit q)
    | ((rxy, rxys), (ryz, ryzs)) = eqTrans x y z rxy ryz && eqTrans xs ys zs rxys ryzs

  neqIsNotEq xs ys with (xs ==. ys)
    | True  = Refl
    | False = Refl

Ordu a => Ordu (List a) where
  []     <. (_::_) = True
  _      <. []     = False
  (x::_) <. (y::_) = x <. y

  ltArefl []     = Oh
  ltArefl (x::_) = ltArefl x

  ltAsymm []     []     _ = Oh
  ltAsymm []     (_::_) _ = Oh
  ltAsymm (x::_) (y::_) p = ltAsymm x y p

  ltTrans []     (_::_) (_::_) _ _ = Oh
  ltTrans (x::_) (y::_) (z::_) p q = ltTrans x y z p q

  lteIsLtOrE _ _ = Refl

  gtInverseOfLt _ _ = Refl

  gteIsGtOrE n m = rewrite eqSymm n m in Refl
