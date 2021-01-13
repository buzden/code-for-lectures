module Example.Qtt.Zero

import Control.Monad.State

import Data.List

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
