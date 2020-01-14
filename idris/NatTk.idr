module NatTk

import Tk

Equ Nat where
  Z     ==. Z     = True
  Z     ==. (S _) = False
  (S _) ==. Z     = False
  (S n) ==. (S m) = n ==. m

  eqReflexivity Z     = Oh
  eqReflexivity (S n) = eqReflexivity n

  eqSymmetricity Z     Z    Oh = Oh
  eqSymmetricity (S k) (S m) p = eqSymmetricity k m p

  eqTransitivity Z     Z     Z   Oh Oh = Oh
  eqTransitivity (S i) (S j) (S k) p q = eqTransitivity i j k p q

  eqIsNotNeq n m with (n ==. m) proof p
    | True  = Refl
    | False = Refl
