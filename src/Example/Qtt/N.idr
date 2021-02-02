module Example.Qtt.N

import Data.Vect

namespace Repetition

  -- repN 0 f x ~ x
  -- repN 1 f x ~ f x
  -- repN 2 f x ~ f . f $ x
  -- repN 3 f x ~ f . f . f $ x

  namespace BadRepetitionS

    public export
    repN : Nat -> (a -> a) -> (a -> a)
    repN Z     f = id
    repN (S n) f = BadRepetitionS.repN n (f . f)

  namespace BadRepetitionX

    public export
    repN : Nat -> (a -> a) -> (a -> a)
    repN Z     f = f
    repN (S n) f = BadRepetitionX.repN n (f . f)

  namespace BadRepetitionZ

    public export
    repN : Nat -> (a -> a) -> (a -> a)
    repN Z     f = f
    repN (S n) f = BadRepetitionZ.repN n f . f

  namespace NiceRepetition

    public export
    repN : Nat -> (a -> a) -> (a -> a)
    repN Z     f = id
    repN (S n) f = NiceRepetition.repN n f . f

  namespace NRepetition

    --public export
    --repN : (n : Nat) -> (n _ : a -> a) -> (a -> a)
    --repN Z     f = id
    --repN (S n) f = NiceRepetition.repN n f . f

namespace Folding

  foldr : (op : a -> b -> b) -> (init : b) -> Vect n a -> b

  --foldr : ((n) op : a -> b -> b) -> (init : b) -> Vect n a -> b

  -- Меру надо знать
  --foldr : ((n) op : a -> (k _ : b) -> b) -> ((k * n) init : b) -> Vect n a -> b
