module Example.Qtt.Zero

import Control.Monad.State

import Data.List
import Data.List.Quantifiers

import Data.Maybe

import Syntax.WithProof

%default total

-------------------------
--- Bounded arguments ---
-------------------------

namespace BoundedArgumentW

  total
  head : (l : List a) -> NonEmpty l => a
  head (x::_) = x

namespace BoundedArgumentW_auto

  total
  head : (l : List a) -> {auto _ : NonEmpty l} -> a
  head (x::_) = x

namespace BoundedArgument0_auto

  total
  head : (l : List a) -> {auto 0 _ : NonEmpty l} -> a
  head (x::_) = x

namespace BoundedArgument0

  total
  head : (l : List a) -> (0 _ : NonEmpty l) => a
  head (x::_) = x

------------------------------------
--- Meta-parameters in the "the" ---
------------------------------------

namespace TheUsage

  f : (MonadState Int m, MonadState Nat m, Monad m) => m Integer
  f = put (the Int 0) *> natToInteger <$> get

  Monad m => MonadState a (StateT (a, b) m) where
    get = Builtin.fst <$> get
    put x = put (x, !(snd <$> get))

  Monad m => MonadState b (StateT (a, b) m) where
    get = snd <$> get
    put x = put (!(Builtin.fst <$> get), x)

  f_mono : State (Int, Nat) Integer
  f_mono = f

  f_run : ((Int, Nat), Integer)
  f_run = runState (1, 2) f

---------------------------
--- Proof-carrying code ---
---------------------------

namespace SubsetAsLib

  data Subset : (type : Type)
             -> (pred : type -> Type)
             -> Type
    where
      Element : (value : type)
             -> (0 prf : pred value)
             -> Subset type pred

namespace SubsetAsRecord

  public export
  record Subset type pred where
    constructor Element
    value : type
    0 prf : pred value

namespace FiltersDPair

  filt : (p : a -> Bool) -> List a -> List (x : a ** p x = True)
  filt p [] = []
  filt p (x::xs) = case @@ p x of
    (True  ** prf) => (x ** prf) :: filt p xs
    (False ** _)   => filt p xs

namespace FiltersSubset

  filt : (p : a -> Bool) -> List a -> List $ Subset a (\x => p x = True)
  filt p [] = []
  filt p (x::xs) = case @@ p x of
    (True  ** prf) => Element x prf :: filt p xs
    (False ** _)   => filt p xs

-----------------------
--- Match on erased ---
-----------------------

pushIn : (xs : List a) -> (0 _ : All p xs) -> List $ Subset a p
pushIn []      []      = []
pushIn (x::xs) (p::ps) = Element x p :: pushIn xs ps

---------------------
--- Parametricity ---
---------------------

namespace WithoutAsq

  id : a -> a
  id x = x

namespace WithForall

  id : forall a. a -> a
  id x = x

namespace WithWType

  id : {a : Type} -> a -> a
  id x = x

  nonid : {a : Type} -> a -> a
  nonid {a=Int}    x = x + 1
  nonid {a=String} x = x ++ "a"
  nonid x = x

namespace With0Type

  id : {0 a : Type} -> a -> a
  id x = x

--------------------------------------
--- Need to not to have at runtime ---
--------------------------------------

namespace NotAtRuntime

  -- data Nat = Z | S Nat

  namespace Hiding

    data BNat : Nat -> Type where
      BZ : BNat 0
      B0 : BNat n -> BNat (2*n)
      B1 : BNat n -> BNat (1 + 2*n)

    (+) : BNat n -> BNat m -> BNat (n + m)

    toNat' : {n : Nat} -> BNat n -> Subset Nat (\k => k = n)
    toNat' x = Element n Refl

    toNat : BNat n -> Subset Nat (\k => k = n)
    toNat BZ     = Element 0 Refl
    toNat (B0 x) = let Element s prf = toNat x in
                   Element (2*s) rewrite prf in Refl
    toNat (B1 x) = let Element s prf = toNat x in
                   Element (1 + 2*s) rewrite prf in Refl

  namespace Exposing

    data BNat : Nat -> Type where
      BZ : BNat 0
      B0 : {n : Nat} -> BNat n -> BNat (2*n)
      B1 : {n : Nat} -> BNat n -> BNat (1 + 2*n)

    toNat : BNat n -> Subset Nat (\k => k = n)
    toNat BZ         = Element 0 Refl
    toNat (B0 {n} _) = Element (2*n) Refl
    toNat (B1 {n} _) = Element (1 + 2*n) Refl
