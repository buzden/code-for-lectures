module NatTk

import Tk

Equ Nat where
  Z     ==. Z     = True
  (S n) ==. (S m) = n ==. m
  _     ==. _     = False

  eqRefl Z     = Oh
  eqRefl (S n) = eqRefl n

  eqSymm Z     Z     = Refl
  eqSymm Z     (S _) = Refl
  eqSymm (S _) Z     = Refl
  eqSymm (S n) (S m) = eqSymm n m

  eqTrans Z     Z     Z     Oh Oh = Oh
  eqTrans (S i) (S j) (S k) p  q  = eqTrans i j k p q

  neqIsNotEq n m with (n ==. m)
    | True  = Refl
    | False = Refl

Ordu Nat where
  Z     <. (S _) = True
  (S n) <. (S m) = n <. m
  Z     <. Z     = False
  (S _) <. Z     = False

  ltArefl Z     = Oh
  ltArefl (S k) = ltArefl k

  ltAsymm Z     Z     _ = Oh
  ltAsymm Z     (S _) _ = Oh
  ltAsymm (S k) (S j) p = ltAsymm k j p

  ltTrans Z     (S _) (S _) Oh _ = Oh
  ltTrans (S i) (S j) (S k) p  q = ltTrans i j k p q

  lteIsLtOrE _ _ = Refl

  gtInverseOfLt _ _ = Refl

  gteIsGtOrE n m = rewrite eqSymm n m in Refl
