module Example.Qtt.Range

import Data.Vect

fromMaybe' : a -> (1 _ : Maybe a) -> a
fromMaybe' _ (Just x) = x
fromMaybe' d Nothing  = d

f : a -> Vect n (Maybe a) -> Vect n a
f x = map (\y => fromMaybe' x y)
