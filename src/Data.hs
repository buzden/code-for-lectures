{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TemplateHaskell, TypeFamilies, DeriveFunctor, DeriveFoldable, DeriveTraversable #-}

module Data where

import Data.List (intercalate)
import Data.Functor.Foldable
import Data.Functor.Foldable.TH (makeBaseFunctor)

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
jsToStr JsonNull         = "null"
jsToStr (JsonBool b)     = show b
jsToStr (JsonNumber n)   = show n
jsToStr (JsonString s)   = s
jsToStr (JsonArray vs)   =
  "[" ++ (intercalate ", " . map jsToStr $ vs) ++ "]"
jsToStr (JsonObject svs) =
  "{" ++ (intercalate "\n" . fmap showPair $ svs) ++ "}"
  where showPair (s, o) = s ++ " : " ++ jsToStr o

foldBT :: (b -> b -> b) -> (a -> b) -> BinTree a -> b
foldBT _  lf (BLeaf a)   = lf a
foldBT nf lf (BNode l r) = nf (foldBT nf lf l) (foldBT nf lf r)

---
data X_IA a = X_IA a (Int -> a) (String -> Int -> a)

filter'' f = foldr (\x tl -> if f x then x:tl else tl) []

-- newtype Fix (f :: * -> *) = Fix (f (Fix f))

f :: [String] -> String
f = snd . foldr (\s (i, r) -> (i + 1, show i ++ " " ++ s ++ "; " ++ r)) (1, "")

---

parseRational :: String -> Maybe Rational
parseRational = undefined

enrat :: JsonValue -> JsonValue
enrat x@JsonNull       = x
enrat x@(JsonBool _)   = x
enrat x@(JsonNumber _) = x
enrat x@(JsonString s) = maybe x JsonNumber $ parseRational s
enrat (JsonArray vs)   = JsonArray $ fmap enrat vs
enrat (JsonObject svs) = JsonObject $ fmap (fmap enrat) svs

---

makeBaseFunctor ''BinTree

showAlg :: Show a => BinTreeF a String -> String
showAlg (BLeafF a)   = show a
showAlg (BNodeF l r) = "{ left: " ++ l ++
                     ", right: " ++ r ++ "}"

depthAlg :: BinTreeF a Integer -> Integer
depthAlg (BLeafF _)   = 1
depthAlg (BNodeF l r) = l + r
