module Data where

import Data.List (intercalate)

data List a = Nil | Cons a (List a)

data BinTree a = BLeaf a | BNode (BinTree a) (BinTree a)

data WideTree a = WLeaf a | WNode (List (WideTree a))

data JsonValue = JsonNull
               | JsonBool   Bool
               | JsonNumber Rational
               | JsonString String
               | JsonArray  [JsonValue]
               | JsonObject [(String, JsonValue)]

filter' :: (a -> Bool) -> [a] -> [a]
filter' _ []     = []
filter' f (x:xs) = if f x then x:tail else tail
  where tail = filter f xs

foldr' :: (a -> b -> b) -> b -> [a] -> b
foldr' _ z []     = z
foldr' f z (x:xs) = f x $ foldr f z xs

jsToStr :: JsonValue -> String
jsToStr JsonNull = "null"
jsToStr (JsonArray vs) =
  "[" ++ (intercalate ", " . map jsToStr $ vs) ++ "]"

foldBT :: (b -> b -> b) -> (a -> b) -> BinTree a -> b
foldBT _  lf (BLeaf a)   = lf a
foldBT nf lf (BNode l r) = nf (foldBT nf lf l) (foldBT nf lf r)

---
data X_IA a = X_IA a (Int -> a) (String -> Int -> a)

filter'' f = foldr (\x tl -> if f x then x:tl else tl) []
