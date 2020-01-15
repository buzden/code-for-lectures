module NatTk

import Tk

Equ Nat where
  Z     ==. Z     = True
  (S n) ==. (S m) = n ==. m
  _     ==. _     = False

  eqReflexivity Z     = Oh
  eqReflexivity (S n) = eqReflexivity n

  eqSymmetricity Z     Z     = Refl
  eqSymmetricity Z     (S _) = Refl
  eqSymmetricity (S _) Z     = Refl
  eqSymmetricity (S n) (S m) = eqSymmetricity n m

  eqTransitivity Z     Z     Z   Oh Oh = Oh
  eqTransitivity (S i) (S j) (S k) p q = eqTransitivity i j k p q

  neqIsNotEq n m with (n ==. m) proof p
    | True  = Refl
    | False = Refl

Ordu Nat where
  Z     <. (S _) = True
  (S n) <. (S m) = n <. m
  Z     <. Z     = False
  (S _) <. Z     = False

  ltAntireflexivity Z     = Oh
  ltAntireflexivity (S k) = ltAntireflexivity k

  ltAntisymmetry Z     Z     _ = Oh
  ltAntisymmetry Z     (S k) _ = Oh
  ltAntisymmetry (S k) Z     p = p
  ltAntisymmetry (S k) (S j) p = ltAntisymmetry k j p

  ltTransitivity Z     (S Z) (S$S _) Oh Oh = Oh
  ltTransitivity Z     (S j) (S k)   Oh q  = Oh
  ltTransitivity (S i) (S j) (S k)   p  q  = ltTransitivity i j k p q

  lteIsLtOrE n m = Refl

  gtInverseOfLt n m = Refl

  gteIsGtOrE n m = rewrite eqSymmetricity n m in Refl
