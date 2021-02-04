module Example.Qtt.Problems

-- This module typechecks only with Idris 2 @fe602caa2, not newer. --

A : Type
B : Type
C : Type

k : A -> (1 _ : B) -> C

-- Typecheks with newer Idris (without linearity subtyping)
--mapK : List A -> List $ (1 _ : B) -> C
--mapK = map k

zipWith : (a -> b -> c) -> List a -> List b -> List c

-- Should compile when there was a linearity subtyping.
zipWithK : List A -> List B -> List C
zipWithK = zipWith k

-- Contra --

namespace InterfaceEdition

  interface Con w where
    constructor MkCon
    con : Nat -> w

  -- Instance первого порядка
  mkCon : (a -> b) -> Con (a -> b)
  mkCon f = MkCon {con = \_ => f}

  -- Would typecheck when linearity subtyping.
  bang : (a -> b) -> (1 _ : a) -> b
  bang f = let cc = mkCon f in con 5

-- Contra (record edition) --

namespace RecordEdition

  record Con w where
    constructor MkCon
    con : Nat -> w       -- `w` в контравариантной позиции

  conn : Con w => Nat -> w
  conn @{x} = con x

  mkCon : (a -> b) -> Con (a -> b)
  mkCon f = MkCon {con = \_ => f}

  -- Would typecheck when linearity subtyping.
  bang : (a -> b) -> (1 _ : a) -> b
  bang f = let cc = mkCon f in conn 5
