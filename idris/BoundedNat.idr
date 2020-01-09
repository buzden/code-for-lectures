module BoundedNat

import Data.Fin
import Data.So

%default total

namespace MaybeResult

  atm : (xs : List a) -> (n : Nat) -> Maybe a
  atm []      _     = Nothing
  atm (x::_)  Z     = Just x
  atm (_::xs) (S n) = xs `atm` n

namespace SoLtParam

  ats : (xs : List a) -> (n : Nat) -> {auto ok : So (n `lt` length xs)} -> a
  ats (x::_) Z = x
  ats (_::xs) (S k) {ok} = xs `ats` k
  ats [] Z impossible
  ats [] (S k) impossible

  x0s : Char
  x0s = ['1', '2', '3'] `ats` 0

  x2s : Char
  x2s = ['1', '2', '3'] `ats` 2

  --x3s : Char
  --x3s = ['1', '2', '3'] `ats` 3

namespace SoJustParam

  ltlt : So (n < k) -> So (n `lt` k)
  ltlt {n = Z} {k = Z} so = so
  ltlt {n = Z} {k = (S k)} so = so
  ltlt {n = (S j)} {k = Z} so = so
  ltlt {n = (S j)} {k = (S l)} _ with (choose (j < l))
    ltlt                         _ | Left subso = ltlt subso
    ltlt {n = (S j)} {k = (S l)} _ | Right sso with (compare j l)
      ltlt _ | Right sso | LT = absurd sso

  atss : (xs : List a) -> (n : Nat) -> {auto ok : So (n < length xs)} -> a
  atss xs n {ok} = SoLtParam.ats xs n {ok = ltlt ok}

  x0ss : Char
  x0ss = ['1', '2', '3'] `atss` 0

  x2ss : Char
  x2ss = ['1', '2', '3'] `atss` 2

  --x3ss : Char
  --x3ss = ['1', '2', '3'] `atss` 3

namespace LteParam

  atl : (xs : List a) -> (n : Nat) -> {auto ok : LT n (length xs)} -> a
  atl (x::_) Z = x
  atl (_::xs) (S n) {ok = (LTESucc _)} = xs `atl` n

  x0l : Char
  x0l = ['1', '2', '3'] `atl` 0

  x2l : Char
  x2l = ['1', '2', '3'] `atl` 2

  --x3l : Char
  --x3l = ['1', '2', '3'] `atl` 3

namespace CumstomWithLte

  data BoundedNat : Nat -> Type where
    MkBoundedNat : (n : Nat) -> {auto ok : LT n b} -> BoundedNat b

  atb : (xs : List a) -> (n : BoundedNat (length xs)) -> a
  atb (x::_) (MkBoundedNat Z) = x
  atb (_::xs) (MkBoundedNat (S n) {ok = (LTESucc _)}) = xs `atb` MkBoundedNat n
  atb [] (MkBoundedNat n) impossible

  x0b : Char
  x0b = ['1', '2', '3'] `atb` MkBoundedNat 0

  x2b : Char
  x2b = ['1', '2', '3'] `atb` MkBoundedNat 2

  --x3b : Char
  --x3b = ['1', '2', '3'] `atb` MkBoundedNat 3

namespace FinParam

  atf : (xs : List a) -> Fin (length xs) -> a
  atf (x::_) FZ = x
  atf (_::xs) (FS n) = xs `atf` n

  x0f : Char
  x0f = ['1', '2', '3'] `atf` 0

  x2f : Char
  x2f = ['1', '2', '3'] `atf` 2

  --x3f : Char
  --x3f = ['1', '2', '3'] `atf` 3
