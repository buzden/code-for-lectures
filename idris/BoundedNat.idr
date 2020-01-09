module BoundedNat

import Data.Fin

%default total

--- LTE parameter ---

atl : (xs : List a) -> (n : Nat) -> {auto ok : LT n (length xs)} -> a
atl (x::_) Z = x
atl (_::xs) (S n) {ok = (LTESucc _)} = xs `atl` n

x0l : Char
x0l = ['1', '2', '3'] `atl` 0

x2l : Char
x2l = ['1', '2', '3'] `atl` 2

--x3l : Char
--x3l = ['1', '2', '3'] `atl` 3

--- Custom type with LTE ---

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

--- Fin parameter ---

atf : (xs : List a) -> Fin (length xs) -> a
atf (x::_) FZ = x
atf (_::xs) (FS n) = xs `atf` n

x0f : Char
x0f = ['1', '2', '3'] `atf` 0

x2f : Char
x2f = ['1', '2', '3'] `atf` 2

--x3f : Char
--x3f = ['1', '2', '3'] `atf` 3
