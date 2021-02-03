module Example.Qtt.Problems

A : Type
B : Type
C : Type

k : A -> (1 _ : B) -> C

mapK : List A -> List $ (1 _ : B) -> C
mapK = map k

zipWith : (a -> b -> c) -> List a -> List b -> List c

-- Should compile when there was a linearity subtyping.
--zipWithK : List A -> List B -> List C
--zipWithK = zipWith k

interface Contravariant f where
  contramap : (a -> b) -> f b -> f a

[F] Contravariant (\c => c -> a) where
  contramap pre f = f . pre

lid : (1 _ : a) -> a
lid x = x

-- Would typecheck when linearity subtyping.
--bang : (a -> b) -> (1 _ : a) -> b
--bang = contramap lid
