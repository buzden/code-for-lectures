module Data where

data List a = Nil | Cons a (List a)

data BinTree a = BLeaf a | BNode (BinTree a) (BinTree a)

data WideTree a = WLeaf a | WNode (List (WideTree a))

data JsonValue = JsonNull
               | JsonBool   Bool
               | JsonNumber Rational
               | JsonString String
               | JsonArray  [JsonValue]
               | JsonObject [(String, JsonValue)]
