module Functorial

interface Functor (f : Type -> Type) where
  map : (a -> b) -> f a -> f b

  mapPreservesId : (m : f a) -> map (\x => x) m = m
  mapComposes : (m : f a) -> (ab : a -> b) -> (bc : b -> c) -> map (bc . ab) m = map bc (map ab m)

Functorial.Functor List where
  map f [] = []
  map f (x::xs) = f x :: Functorial.map f xs

  mapPreservesId []      = Refl
  mapPreservesId (x::xs) = rewrite mapPreservesId xs in Refl

  mapComposes []      f g = Refl
  mapComposes (x::xs) f g = rewrite mapComposes xs f g in Refl
