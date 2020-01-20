module Logic

notConj : Either (a -> Void) (b -> Void) -> (a, b) -> Void
notConj (Left l)  (a, _) = l a
notConj (Right r) (_, b) = r b

notEx : {p : a -> Type} -> ((x : a ** p x) -> Void) -> (y : a) -> p y -> Void
notEx ne y py = ne (y ** py)

nnnEl : (((a -> Void) -> Void) -> Void) -> (a -> Void)
nnnEl f x = f (\p => absurd $ p x)

nnnLe : (a -> Void) -> (((a -> Void) -> Void) -> Void)
nnnLe f g = g f

depCurr : {p : a -> Type} -> ((x : a ** p x) -> b) -> ((y : a) -> p y -> b)
depCurr f y x = f (y ** x)

depUncurr : {p : a -> Type} -> ((y : a) -> p y -> b) -> ((x : a ** p x) -> b)
depUncurr f (z ** q) = f z q
