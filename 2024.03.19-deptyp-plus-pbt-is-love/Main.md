---
lang: ru-RU

author: "Денис Буздало́в"
title: "Зависимые типы + property-based testing = \\heart"
date: "19 марта 2024"

aspectratio: 1610

mainfont: "DejaVu Serif"
monofont: "Iosevka Extended:-calt;+IDRS"
#monofont: "Fira Code:+calt;+ss09;+ss03;+cv29;+cv24"
linkstyle: bold

theme: "Singapore"
colortheme: "seahorse"
section-titles: true

header-includes: |
  \usepackage{framed}
  \usepackage{hyperref}
  \usepackage[normalem]{ulem}
  \usepackage[dvipsnames]{xcolor}
  \usepackage{tikzsymbols}
  \usepackage{qrcode}
  \usetikzlibrary{automata,positioning}
  \usetikzlibrary{shapes.multipart,shapes.symbols,shapes.geometric}
  \AtBeginSection{}
  \setbeamertemplate{caption}{\raggedright\insertcaption\par}
  \newcommand{\heart}{\dHeart[.9]}
  \renewcommand{\ULthickness}{1.5pt}
  \titlegraphic{
    \includegraphics[height=.4cm]{.images/cc.png}
    \includegraphics[height=.4cm]{.images/by.png}
  }
  \newcommand{\switchframeon}[3]{\end{frame}\begin{frame}<#1>[label=#2]{#3}}
  \newcommand{\runframefrom}[2]{\end{frame}\againframe<#1>{#2}}
  \tikzset{
    onslide/.code args={<#1>#2}{%
      \only<#1>{\pgfkeysalso{#2}}
    },
    diagonal fill/.style 2 args={
      fill=#2, path picture={
        \fill[#1, sharp corners] (path picture bounding box.south west) -|
                                 (path picture bounding box.north east) -- cycle;
      }
    },
  }

# Those commands with `\end{frame}` in the beginning do now work after the slides with verbatim on them

abstract: |
  Property-based testing — зарекомендовавший себя подход, позволяющий находить баги, практически неподвластные ручному тестированию,
  и при правильном использовании значительно сокращающий затраты на качественное тестирование.
  Для работы подхода нужны генераторы входных данных системы, которую мы тестируем,
  и часто мы можем получить эти генераторы автоматически или задёшево.

  Но что, если у той системы, которую мы хотим тестировать, входные данные очень непростой структуры?
  Например, хитрые графы с хитрыми отношениями вершин или успешно тайпчекающиеся программы?
  Тут на помощь нам могут придти зависимые типы (dependent types).

  В докладе рассмотрим property-based testing вообще, коротко познакомимся с зависимыми типами,
  а также как их сочетание позволяет находить сложные ошибки в сложных системах.

---

# Привет

## О докладе

<!-- idris
import Data.Double.Bounded

import Data.List
import Data.List.Quantifiers
import Data.Maybe
import Data.So

import Hedgehog

%default total
-->

. . .

- Зависимые типы \phantom{+ property-based testing = \heart} \pause
- \phantom{Зависимые типы +} property-based testing \phantom{= \heart} \pause
- \phantom{Зависимые типы} + \phantom{property-based testing = \heart} \pause
- \phantom{Зависимые типы + property-based testing} = \heart \pause

\vfill

- Будет много кода\pause , в основном на Idris

. . .

- Синтаксис почти как Haskell\pause , только лучше \dTongey[1.2]

. . .

- Пробежимся только по верхам\pause , но всё равно будет сложно

. . .

- Сложность будет расти нелинейно\pause , задавайте вопросы по ходу

## Чуточку о синтаксисе

::: columns
:::: column

<!-- idris
namespace MaybeInline {
-->

```idris
data Maybe a = Nothing
             | Just a
```

::::
:::: column

. . .

<!-- idris
 }
namespace MaybeGADT_Style {
-->

```idris
data Maybe : Type -> Type where
  Nothing : Maybe a
  Just    : a -> Maybe a
```

::::
:::

<!-- idris
 }
-->

\pause\vfill

::: columns
:::: column

<!-- idris
%hide List.length
namespace ListLenPlain {
-->

```idris
length : List a -> Nat
length []      = 0
length (_::xs) = 1 + length xs
```

::::
:::: column

. . .

<!-- idris
 }
namespace ListLenNamed {
-->

```idris
length : (xs : List a) -> Nat
length []      = 0
length (_::xs) = 1 + length xs
```

<!-- idris
 }
%unhide List.length
-->

::::
:::

\pause\vfill

<!-- idris
namespace ListElemEqBeg {
-->

```idris
elem : Eq a => a -> List a -> Bool
```

\pause\vspace{-\parskip}

<!-- idris
 }
namespace ListElemEqAft1 {
-->

```idris
elem : a -> Eq a => List a -> Bool                      -- *
```

\pause\vspace{-\parskip}

<!-- idris
 }
namespace ListElemEqAft2 {
-->

```idris
elem : a -> List a -> Eq a => Bool                      -- **
```

<!-- idris
 }
-->

# Зависимые типы

## \only<-2>{Вы же знакомы с полиморфизмом?}\only<3->{Первая \sout{доза} зависимость}

<!-- idris
namespace IdPlain {
-->

```idris
id : a -> a
id x = x
```

. . .

<!-- idris
 }
namespace IdForall {
-->

```idris
id : forall a. a -> a
id x = x
```

<!-- idris
 }
namespace Idimpl {
-->

. . .

::: {.only on=-3}

```idris
id : {0 a : Type} -> a -> a
id x = x
```

:::

<!-- idris
 }
namespace IdimplComment {
-->

::: {.only on=4-}

```idris
id : {0 a : Type} -> a -> a  -- всё ещё параметрична по `a`
id x = x
```

:::

<!-- idris
 }
namespace MyThe {
-->

\pause\pause\vfill

```idris
the : (0 a : Type) -> a -> a
the _ x = x
```

<!-- idris
 }
-->

. . .

::: columns
:::: column

::::: {.uncover on=7-}
```idris
-- Idris
someInt = the Int 5
```
:::::

::::
:::: column

```haskell
-- Haskell
someInt = 5 :: Int
```

::::
:::

## Дальше --- больше

. . .

```idris
SomeStrangeType : Bool -> Type
```
\pause\vspace{-\parskip}
```idris
SomeStrangeType True  = String
SomeStrangeType False = Nat
```

\pause\vfill

<!-- idris
namespace ReturnsNoImplemented {
-->
```idris
returns : (b : Bool) -> SomeStrangeType b
```
\pause\vspace{-\parskip}
::: {.only on=-5}
```idris
returns True  = ?what
returns False = ?what_else
```
:::
<!-- idris
 }
namespace ReturnsPartiallyImplemented {
returns : (b : Bool) -> SomeStrangeType b
-->
::: {.only on=6}
```idris
returns True  = "dependent types are cool"
returns False = ?what_else
```
:::
<!-- idris
 }
namespace ReturnsFullyImplemented {
returns : (b : Bool) -> SomeStrangeType b
-->
::: {.only on=7-}
```idris
returns True  = "dependent types are cool"
returns False = 42
```
:::
<!-- idris
 }
-->

\vfill

::: {.uncover on=8-}

<!-- idris
namespace TakesNotMatched {
-->
```idris
takes : (b : Bool) -> SomeStrangeType b -> Integer
```
\vspace{-\parskip}

:::: {.only on=-8}
```idris
takes flag  val = ?what_type_of_val
```
\vspace{-.6\parskip}\phantom{\texttt{code}}\newline
\phantom{\texttt{code}}
::::

<!-- idris
 }
namespace TakesJustMatched {
takes : (b : Bool) -> SomeStrangeType b -> Integer
-->

:::: {.only on=9}
```idris
takes True  val = ?what_type_of_val_here
takes False val = ?what_type_of_val_there
```
\vspace{-.6\parskip}\phantom{\texttt{code}}
::::

<!-- idris
 }
namespace TakesTrueImplemented {
takes : (b : Bool) -> SomeStrangeType b -> Integer
-->

:::: {.only on=10}
```idris
takes True  str = natToInteger $ length $ str ++ "cool?"
takes False val = ?what_type_of_val_there
```
\vspace{-.6\parskip}\phantom{\texttt{code}}
::::

<!-- idris
 }
namespace TakesFalseMatched {
takes : (b : Bool) -> SomeStrangeType b -> Integer
-->

:::: {.only on=11}
```idris
takes True  str = natToInteger $ length $ str ++ "cool?"
takes False 42  = ?something
takes False val = ?something_else
```
::::

<!-- idris
 }
namespace TakesFullyImplemented {
takes : (b : Bool) -> SomeStrangeType b -> Integer
-->

:::: {.only on=12-}
```idris
takes True  str = natToInteger $ length $ str ++ "cool?"
takes False 42  = -64
takes False val = negate $ natToInteger val
```
::::

<!-- idris
 }
-->

:::

## Ещё дальше --- ещё больше

. . .

<!-- idris
namespace MyVect {
-->

```idris
data Vect : Nat -> Type -> Type where
```
\pause\vspace{-\parskip}
```idris
  Nil  : Vect 0 a
  (::) : a -> Vect n a -> Vect (1+n) a
```

\pause\vfill

::: columns
:::: column
::::: {.uncover on=7-}
```idris
total
```
:::::
::::: {.uncover on=5-}
```idris
head : Vect (1+n) a -> a
```
:::::
::::: {.uncover on=6-}
\vspace{-\parskip}
```idris
head (x::xs) = x
```
:::::
::::
:::: column
```idris
head' : Vect n a -> Maybe a
head' []      = Nothing
head' (x::xs) = Just x
```
::::
:::

\pause\pause\pause\pause\vfill

::::: {.only on=-14}
<!-- idris
infix 6 .<.
-->
```idris
data (.<.) : Nat -> Nat -> Type where
```
\pause\vspace{-\parskip}
```idris
  LTZ : 0 .<. 1+n
```
\pause\vspace{-\parskip}
```idris
  LTS : n .<. m -> 1+n .<. 1+m
```

\pause\vfill

<!-- idris
-- Just to avoid explicit matching on the `LTS _` below
%hint
unLTS : 1+n .<. 1+m -> n .<. m
unLTS (LTS x) = x
-->

::: {.uncover on=14-}
```idris
total
```
\vspace{-\parskip}
:::
```idris
index : (m : Nat) -> Vect n a -> m.<.n => a
```
\pause\vspace{-\parskip}
```idris
index 0     (x::xs) = x
```
\pause\vspace{-\parskip}
```idris
index (S i) (x::xs) = index i xs
```
:::::
::::: {.only on=15-}
\vspace{.15\parskip}
```idris
data Fin : Nat -> Type where     -- натуральные числа,
  FZ : Fin (1+n)                 -- строго меньшие `n`
  FS : Fin n -> Fin (1+n)
```

\vfill

<!-- idris
fromInteger : (x : Integer) -> (x === 0) => Fin (S n)
fromInteger _ = FZ

namespace IndexWithFin {
-->
```idris
total
index : Fin n -> Vect n a -> a
index 0      (x::xs) = x
index (FS i) (x::xs) = index i xs
```
<!-- idris
 }
-->
:::::

<!-- idris
 }
-->

## Прыжок вдаль

. . .

<!-- idris
namespace SortedTree {
export
data SortedBinTree : Type -> Type
data All : (a -> Bool) -> SortedBinTree a -> Type
-->

```idris
data SortedBinTree : Type -> Type where
  Empty : SortedBinTree a
  Node  : (x : a) -> (left, right : SortedBinTree a) ->
```
\vspace{-\parskip}
::: {.uncover on=3-}
:::: {.only on=-4}
```idris
          -- all in left subtree < x, all in right subtree > x
```
::::
:::: {.only on=5-}
```idris
          Ord a => All (< x) left => All (x <) right =>
```
::::
:::
\vspace{-\parskip}
```idris
          SortedBinTree a
```

\vspace{\parskip}

::: {.uncover on=4-}
```idris
data All : (a -> Bool) -> SortedBinTree a -> Type where
```
:::
\vspace{-\parskip}
::: {.uncover on=6-}
```idris
  Empty' : All prop Empty
```
:::
\vspace{-\parskip}
::: {.uncover on=7-}
```idris
  Node'  : forall prop.
```
\vspace{-\parskip}
:::: {.only on=-7}
```idris
           -- what?
```
::::
:::: {.only on=8}
```idris
           -- `x` holds `prop`, ...
```
::::
:::: {.only on=9}
```idris
           -- `x` holds `prop`, all in `l` and `r` holds `prop`
```
::::
:::: {.only on=10-}
```idris
           So (prop x) -> All prop l -> All prop r ->
```
::::
\vspace{-\parskip}
```idris
           All prop $ Node x l r @{o} @{pl} @{pr}
```
:::

<!-- idris
export
toList : SortedBinTree a -> List a
toList Empty = []
toList $ Node x l r = toList l ++ [x] ++ toList r

 }
-->

## Улёт вдаль: целый язык

. . .

<!-- idris
namespace SmallLangExample {

Name : Type
Name = String

data IsIn : Name -> List (Name, a) -> Type where
  MkIsIn : IsJust (lookup n xs) -> IsIn n xs

0 (.found) : IsIn {a} n xs -> a
(.found) $ MkIsIn _ with 0 (lookup n xs)
  _ | Just x = x

record FunSig
data Expr : (funs : List (Name, FunSig)) -> (vars : List (Name, Type)) -> Type -> Type

infix 2 #=
covering
-->

```idris
data Stmts : (funs  : List (Name, FunSig)) ->
             (preV  : List (Name, Type)) ->
             (postV : List (Name, Type)) -> Type where
```

. . .

::: {.uncover on=4-}
```idris
  (.)  : (ty : Type) -> (n : Name) ->
         Stmts funs vars ((n, ty)::vars)
```
:::
::: {.uncover on=5-}
:::: {.only on=-5}
``` {.idris}
  (#=) : (n : Name) ->
         (v : Expr funs vars ?expr_ty) ->
         Stmts funs vars vars
```
::::
:::: {.only on=6-}
```idris
  (#=) : (n : Name) -> (0 lk : n `IsIn` vars) =>
         (v : Expr funs vars lk.found) ->
         Stmts funs vars vars
```
::::
:::
::: {.uncover on=7-}
```idris
  If   : (cond : Expr funs vars Bool) ->
         Stmts funs vars vThen -> Stmts funs vars vElse ->
         Stmts funs vars vars
```
:::
::: {.uncover on=3-}
```idris
  (>>) : Stmts funs preV midV  -> Stmts funs midV postV ->
         Stmts funs preV postV
```
:::

## Улёт вдаль: целый язык

<!-- idris
infix 1 ==>
-->

::: {.uncover on=4-}
```idris
record FunSig where
  constructor (==>)
  From : List Type
  To   : Type
```
:::

\vfill

<!-- idris
covering -- actually, all is total, but I don't want to bother with `assert_total` in types
-->

```idris
data Expr : List (Name, FunSig) -> List (Name, Type) ->
            Type -> Type where
```

. . .

```idris
  C : (x : ty) -> Expr funs vars ty
```

. . .

```idris
  V : (n : Name) -> (0 lk : n `IsIn` vars) =>
      Expr funs vars lk.found
```

\pause\pause

```idris
  F : (n : Name) -> (0 lk : n `IsIn` funs) =>
      All (Expr funs vars) lk.found.From ->
      Expr funs vars lk.found.To
```

## Улёт вдаль: целый язык

\vspace{-\fill}

<!-- idris
namespace AlignHack
                              public export
-->

::: {.uncover on=3-}
:::: small
```idris
                              StdF : List (Name, FunSig)
                              StdF = [ ("+" , [Int, Int] ==> Int)
                                     , ("<" , [Int, Int] ==> Bool)
                                     , ("++", [Int] ==> Int)
                                     , ("||", [Bool, Bool] ==> Bool) ]
```
::::
:::

\vspace{-4\parskip} <!-- magic skills in slide alignment O_O -->

<!-- idris
covering
-->
::: {.only on=-3}
``` {.idris}
program : Stmts [] [] ?
```
:::
::: {.only on=4-}
```idris
program : Stmts StdF [] ?
```
:::

\vspace{-\parskip}

```idris
program = do
  Int. "x"
  "x" #= C 5
```

\pause\vspace{-\parskip}

```idris
  Int. "y"; Bool. "res"
```

\pause\pause\pause\vspace{-\parskip}

```idris
  "y" #= F "+" [V "x", C 1]
```

\pause\vspace{-\parskip}

```idris
  If (F "<" [F "++" [V "x"], V "y"])
```

\vspace{-\parskip}

::: {.only on=-6}
``` {.idris}
     ?then_branch
     ?else_branch
```
\vspace{-2\parskip}\phantom{\texttt{Bool}}\par\phantom{\texttt{Bool}}
:::
::: {.only on=7}
``` {.idris}
     (do "y" #= C 0; "res" #= C False)
     ?else_branch
```
\vspace{-2\parskip}
\phantom{\texttt{code}}\par\phantom{\texttt{code}}
:::
::: {.only on=8-}
```idris
     (do "y" #= C 0; "res" #= C False)
     (do Int. "z"; "z" #= F "+" [V "x", V "y"]
         Bool. "b"; "b" #= F "<" [V "x", C 5]
         "res" #= F "||" [V "b", F "<" [V "z", C 6]])
```
:::

\vfill

## Улёт вдаль: целый язык

```idris
failing "Mismatch between: Int and Bool"
  bad : Stmts StdF [] ?
  bad = do
    Int. "x"; "x" #= C 5
    Bool. "y"; "y" #= F "+" [V "x", C 1]
```

. . .

\vfill

```idris
failing "Mismatch between: [] and [Int]"
  bad : Stmts StdF [] ?
  bad = do
    Int. "x"; "x" #= C 5
    Int. "y"; "y" #= F "+" [V "x"]
```

. . .

\vfill

```idris
failing "Mismatch between: Bool and Int"
  bad : Stmts StdF [] ?
  bad = do
    Int. "x"; "x" #= C 5
    Int. "y"; "y" #= F "+" [C True, V "x"]
```

## Улёт вдаль: целый язык

```idris
failing #"
    Can't find an implementation for IsIn "z" [("x", Int)]"#
  bad : Stmts StdF [] ?
  bad = do
    Int. "x"; "x" #= C 5
    "z" #= V "x"
```

. . .

\vfill

```idris
failing #"
    Can't find an implementation for IsIn "z" [("x", Int)]"#
  bad : Stmts StdF [] ?
  bad = do
    Int. "x"
    "x" #= V "z"
```

<!-- idris
 } -- closing the namespace `SmallLangExample`
-->

# Property-based testing

## Property-based testing

. . .

- Тестирование функции/системы на *произвольном* входе

. . .

- Оценка, а не предугадывание результата

. . .

- Рандомизированная генерация входных значений

. . .

- (Иногда) автоматическая деривация генераторов

. . .

- (Иногда) автоматический shrinking

. . .

- QuickCheck, Hedgehog, Validity, ScalaCheck, ...

## \only<-7>{Property-based testing}\only<8->{А что, если \texttt{reverse = id}?}

<!-- idris
insert : Ord a => a -> List a -> List a
insert = merge . singleton

arbitraryNat : Gen Nat
arbitraryNat = nat $ linear 0 5

arbitraryList : Gen $ List Nat
arbitraryList = list (exponential 0 1000) arbitraryNat

public export
sortedList : Gen $ List Nat
sortedList = foldr (\x, res => x :: map (+x) res) [] <$> arbitraryList

sortedListOk : Property
sortedListOk = withConfidence 1000000000 $ property $ do
  xs <- forAll sortedList
  assert $ sorted xs
  cover 40 "len big enough" $ length xs >= 2
  cover 40 "vals diverse" $ any (>= 2) xs
-->

<!-- idris
namespace InsertWeakProp {
export
-->
::: {.only on=-1}
```idris
insertOk : Property
insertOk = property $ do
  insert 2 [1, 3, 5] === [1, 2, 3, 5]
```
:::

<!-- idris
 }
namespace InsertWeakPropHoly {
-->

<!-- idris
infix 9 `eht`

eht : a -> (0 b : Type) -> (a = b) => b
eht x _ @{Refl} = x
-->

::: {.only on=2}
```idris
insertOk : Property
insertOk = property $ do
  insert ?x ?xs === ?result
```
<!-- idris
    `eht` List Nat
-->
:::

<!-- idris
 }
namespace InsertWeakPropOneForall {
-->

::: {.only on=3}
```idris
insertOk : Property
insertOk = property $ do
  x  <- forAll arbitraryNat
  insert x ?xs === ?result
```
:::

<!-- idris
 }
namespace InsertWeakPropTwoForalls {
-->

::: {.only on=4}
```idris
insertOk : Property
insertOk = property $ do
  x  <- forAll arbitraryNat
  xs <- forAll sortedList
  insert x xs === ?result
```
:::

<!-- idris
 }
namespace InsertSortedProp {
export
-->

::: {.only on=5}
```idris
insertOk : Property
insertOk = property $ do
  x  <- forAll arbitraryNat
  xs <- forAll sortedList
  assert $ sorted $ insert x xs
```
:::

<!-- idris
 }
namespace InsertSortedAndElemProp {
export
-->

::: {.only on=6-}
```idris
insertOk : Property
insertOk = property $ do
  x  <- forAll arbitraryNat
  xs <- forAll sortedList
  assert $ sorted $ insert x xs
  assert $ x `elem` insert x xs
```
:::

<!-- idris
 }
-->

::: {.only on=-5}
\vspace{-\parskip}\phantom{\texttt{code}}
:::
::: {.only on=-3}
\vspace{-\parskip}\phantom{\texttt{code}}
:::
::: {.only on=-2}
\vspace{-\parskip}\phantom{\texttt{code}}
:::

\pause\pause\pause\pause\pause\pause
\vfill

<!--
%hide Prelude.List.reverse

reverse : List a -> List a
reverse = id
-->

<!--
reverseAndConcat : Property
reverseAndConcat = property $ do
  (xs, ys) <- [| (forAll arbitraryList, forAll arbitraryList) |]
  reverse xs ++ reverse ys === reverse (ys ++ xs)
-->

```idris
reverseAndConcat : Property
reverseAndConcat = property $ do
  xs <- forAll arbitraryList
  ys <- forAll arbitraryList
  reverse xs ++ reverse ys === reverse (ys ++ xs)
```

<!-- idris
main : IO ()
main = test
  [ "generators" `MkGroup`
    [ ("sortedListOk", sortedListOk)
    ]
  , "insert" `MkGroup`
    [ ("InsertWeakProp.insertOk", InsertWeakProp.insertOk)
    , ("InsertSortedProp.insertOk", InsertSortedProp.insertOk)
    , ("InsertSortedAndElemProp.insertOk", InsertSortedAndElemProp.insertOk)
    ]
  , "list" `MkGroup`
    [ ("reverseAndConcat", reverseAndConcat)
    ]
  ]
-->

## А что, если `reverse = id`?

::: center
![](.images/bug-revealed-by-hedgehog.png){height=100%}
:::

\switchframeon{-8}{pbt-overview}{\only<-10>{Property-based testing сверху}\only<11->{DepTyCheck (сейчас)}}

::: {.uncover on=-5}
<!-- oh, I gave up normal insertion, endless war with `verbatim` and `\end{frame}` -->
\includegraphics[height=.24\textheight,trim=-8cm 0 0 0]{.images/partial-insert-ok-pic.png}
\vspace{-.24\textheight}
:::

::: center
:::: {=latex}
\tikzset{
  process/.style={
    rectangle,
    draw=black,
    thick,
    text centered,
    fill=Green!30,
    inner sep=8pt,
    minimum width=2cm,
  },
  userprocess/.style={
    process,
    fill=orange!30,
  },
  halfuserprocess/.style={
    process,
    diagonal fill={Green!30}{orange!30},
  },
  externalprocess/.style={
    process,
    fill=gray!80,
  },
  data/.style={
    text centered,
  },
  goes/.style={
    ->,
    >=stealth',
    ultra thick,
    shorten <=5pt,
    shorten >=5pt,
  },
}
\tikzset{every text node part/.style={align=center}} <!-- to make line breaks work in nodes -->

\begin{tikzpicture}[on grid,node distance=2cm]

\small
\uncover<3->{
  \node(generator)[halfuserprocess]{\only<-6>{\texttt{sortedList}}\only<7->{генератор}};
}
\uncover<8->{
  \node(generated)[data, above right = 2cm and 3cm of generator]{сгенерированные\\значения};
  \node(mediator)[userprocess, below right = 2cm and 1cm of generated]{медиатор};
}
\uncover<2->{
\node(input)[data, below = of mediator]{вход};
\node(sut)[userprocess, below right = 1.5cm and 1.5cm of input]{\only<-6>{\texttt{insert}}\only<7->{SUT}};
\node(output)[data, above right = 1.5cm and 1.5cm of sut]{выход};
\path (input) edge[goes] (sut);
\path (sut) edge[goes] (output);
}

\uncover<4->{
  \node(oracle)[onslide=<-10>{userprocess}, onslide=<11->{externalprocess}, above = of output]{\only<-6>{\texttt{sorted}}\only<7->{оракул}};
  \node(verdict)[data, above right = 1cm and 3cm of oracle]{вердикт};
  \node(verdictOut)[right = 2.5cm of verdict]{};
}
\uncover<5->{
  \node(shrinker)[onslide=<-10>{halfuserprocess}, onslide=<11->{externalprocess}, below = 2cm of verdict]{shrinker};
  \node(shrunk)[data, below = 2cm of shrinker]{мин.\\тест};
  \node(shrunkOut)[right = 2.5cm of shrunk]{};
}
\uncover<10->{
  \node(derivator)[process, below of=generator]{дериватор};
}
\uncover<4->{
  \path (output) edge[goes] (oracle);
  \path (oracle) edge[goes] (verdict);
  \path (verdict) edge[goes,draw=Green] node[above,text=Green](verdictOk){ok} (verdictOut);
  \path (verdict) edge[goes,draw=Red] node[right,text=Red](verdictFailed){failed} (shrinker);
}
\uncover<5->{
  \path (shrinker) edge[goes] (shrunk);
  \path (shrunk) edge[goes] (shrunkOut);
}

\uncover<9->{
  \node(type)[data, below right = 2cm and 1cm of derivator]{определение\\типа};
  \path (type) edge[goes,dashed,draw=gray] (generated);

  \node(typeIn)[left = 2.5cm of type]{};
  \path (typeIn) edge[goes] (type);
}
\uncover<10->{
  \path (type) edge[goes] (derivator);
  \path (derivator) edge[goes] (generator);
}

\uncover<3-7>{
  \path (generator) edge[goes] (input);
}
\uncover<4-7>{
  \path (input) edge[goes] (oracle);
}
\uncover<8->{
  \path (generator) edge[goes] (generated);
  \path (generated) edge[goes] (mediator);
  \path (generated) edge[goes] (oracle);
  \path (mediator) edge[goes] (input);
}

\end{tikzpicture}
::::
:::

##

::: center
![](.images/john-hughes-come-on.png){height=90%}
:::

\footnotetext[1]{https://www.youtube.com/watch?v=zi0rHwfiX1Q}

# Единение

## \only<4->{Зависимые типы + p}\only<-3>{P}roperty-based testing

::: {.uncover on=2-}

:::: {.uncover on=4-}
```idris
arbitrarySortedBinTree : Gen $ SortedBinTree Nat
```
::::
\vspace{-\parskip}
:::: {.uncover on=6-}
``` {.idris}
arbitrarySortedBinTree = %runElab deriveGen
```
::::

<!-- idris
namespace SortedListThruArbitrary {
public export
-->
```idris
sortedList : Gen $ List Nat
```
\vspace{-\parskip}

::::: {.uncover on=3-}
:::: {.only on=-4}
```idris
sortedList =
  foldr (\x, res => x :: map (+x) res) [] <$> arbitraryList
```
::::
:::::
<!-- idris

sortedListOk : SortedListThruArbitrary.sortedList = Main.sortedList
sortedListOk = Refl
 }
%hide SortedListThruArbitrary.sortedList
namespace SortedListThruSortedBinTree {
sortedList : Gen $ List Nat
-->

:::: {.only on=5-}
```idris
sortedList = toList <$> arbitrarySortedBinTree
```
::::
:::: {.only on=5-}
\vspace{-\parskip}\phantom{\texttt{code}}
::::

:::

<!-- idris
 }
namespace InsertOkInThePlusChapter {
-->
```idris
insertOk : Property
insertOk = property $ do
  x  <- forAll arbitraryNat
  xs <- forAll sortedList
  assert $ sorted $ insert x xs
```
<!-- idris
 }
-->

## Зависимые типы + property-based testing

- Зависимые типы для описания сложных входных данных

. . .

- Описать тип так, чтобы любое значение подходило

. . .

- Возможность автоматической деривации генератора

. . .

- ...

- Profit!

\runframefrom{8-10}{pbt-overview}

# DepTyCheck \Heart

## DepTyCheck (сейчас)

- Opensource-библиотека для PBT с зависимыми типами

. . .

- Поддерживает деривацию генераторов

. . .

- Гарантии полноты и распределения при деривации

. . .

- Under heavy construction, очень многого ещё нет

\runframefrom{11}{pbt-overview}

## Пример из жизни

. . .

- Диалект Typescript

. . .

- Имеет интерпретатор с JIT и компилятор

. . .

- Свежая промышленная разработка

. . .

- Специфировали подмножество

  . . .

  - Завершающиеся программы

  . . .

  - Циклы, ветвления, присваивания, исключения

  . . .

  - Классы без методов, числа, массивы

. . .

- Наша спецификация

  . . .

  - Описание семантически корректных программ из подмножества

  . . .

  - ~330 строк кода спецификация языка + столько же обвязка

  . . .

  - Частично деривированные, частично рукописные генераторы

## Пример из жизни

::: {.only on=-1}
:::: center
::::: Large
Testing...
:::::
::::
:::

::: {.only on=2-4}
\vfill
:::: {.uncover on=3-}
\vspace{-4.5\parskip}
\includegraphics[height=.65\textheight]{.images/bloody-mess.png}
\vspace{-.65\textheight}
\vspace{4.5\parskip}
::::

```
ASSERTION FAILED: false
IN /.../optimizations/lse.cpp:851: GetEliminationCode
Backtrace [tid=2990599]:
#0 : 0x7f876a1776c0 PrintStack(std::ostream&)
#1 : 0x7f876a177562 debug::AssertionFail(...)
#2 : 0x7f8767185e10 compiler::Lse::GetEliminationCode(...)
#3 : 0x7f8767186a20 compiler::Lse::DeleteInstructions(...)
...
```

\vfill

:::: {.uncover on=4-}
::::: center
:::::: Large
Shrinking...
::::::
:::::
::::
:::

::: {.only on=5-}
```typescript
class C0 {
  x0: boolean
}

function main() : void {
  let x1: C0 = {x0: true}
  while(x1.x0) {
    x1.x0 = x1.x0
    x1.x0 = false
  }
}
```
:::

## Пример из жизни

::: {.only on=-1}
:::: center
::::: Large
Testing...
:::::
::::
:::

::: {.only on=2-3}
\vfill
:::: small
```
Wrong input 0 type 'i32' for inst:
    52.ref  NullCheck  v42, v51 -> (v55, v53)
                                       bc: 0x0000005d
ASSERTION FAILED: CheckType(GetInputType(inst, 0), ...)
IN /.../inst_checker_gen.h:694: VisitNullCheck
ERRNO: 29 (Illegal seek)
Backtrace [tid=3853514]:
#0 : 0x7f46fc7b393c PrintStack(std::ostream&)
#1 : 0x7f46fc7b37de debug::AssertionFail(...)
#2 : 0x7f46fe3760ad compiler::InstChecker::VisitNullCheck(...)
#3 : 0x7f46fe38dae5 compiler::InstChecker::VisitGraph()
#4 : 0x7f46fe35e63e compiler::InstChecker::Run(...)
#5 : 0x7f46fe33c1b2 compiler::GraphChecker::Check()
...
```
::::

\vfill

:::: {.uncover on=3-}
::::: center
:::::: Large
Shrinking...
::::::
:::::
::::
:::

::: {.only on=4-}
```typescript
function main() {
   for(let x2 of [0]) {
     let x3: boolean = false
     for(let x4 of [0]) {
       let x5: int[][] = [[]]
       let fuel1 = 0
     }
   }
   let fuel0 = 0
}
```
:::

## Пример из жизни

::: {.only on=-1}
:::: center
::::: Large
Testing...
:::::
::::
:::

::: {.only on=2-3}
\vfill
:::: small
```
ASSERTION FAILED: block->GetGraph() == GetGraph()
IN /.../optimizer/ir/graph_cloner.h:176: GetClone
Backtrace [tid=2902033]:
#0 : 0x7fe71892b820 PrintStack(std::ostream&)
#1 : 0x7fe71892b6c2 debug::AssertionFail(...)
#2 : 0x7fe71a61ae61 compiler::GraphCloner::GetClone(...)
#3 : 0x7fe71a61162a compiler::GraphCloner::CopyLoop(...)
#4 : 0x7fe71a611839 compiler::GraphCloner::CopyLoop(...)
#5 : 0x7fe71a611173 compiler::GraphCloner::CloneAnalyses(...)
#6 : 0x7fe71a610d1f compiler::GraphCloner::CloneGraph()
#7 : 0x7fe71a5b377c compiler::GraphChecker::GraphChecker(...)
...
```
::::

\vfill

:::: {.uncover on=3-}
::::: center
:::::: Large
Shrinking...
::::::
:::::
::::
:::

::: {.only on=4-}
:::: columns
::::: {.column width=35%}
```typescript
class C0 {
  x0: boolean

  f() : string {
    return ""
  }
}
```
:::::
::::: {.column width=65%}
```typescript
function main() : void {
  let x2: C0 = {x0: true}
  let fuel0 = 1
  while(fuel0 > 0) {
    do {
      fuel0--
      do {
        fuel0--
        let s = x2.f()
      } while(true && (fuel0 > 0))
    } while(true && (fuel0 > 0))
  }
}
```
:::::
::::
:::

## Пример из жизни

::: {.only on=-1}
:::: center
::::: Large
Testing...
:::::
::::
:::

::: {.only on=2-}
\vfill
:::: {.only on=-3}
```
TypeError: Unreachable statement. [<filename>:26:34]
```
::::
:::: {.only on=4-}
```
TypeError: Unreachable statement. [<filename>:3:30]
```
::::

\vfill

:::: {.uncover on=3}
::::: center
:::::: Large
::::::: {.only on=-3}
Shrinking...
:::::::
::::::
:::::
::::
:::: {.uncover on=4-}
```typescript
function main() : void {
  let x1: Int = 1
  while(([false, true])[x1]) {
  }
}
```
::::: {.only on=4-}
\phantom{\Large{Shrinking}}\vspace{.4\parskip}
:::::
::::
:::

## Пример из жизни

- ...и так далее

. . .

- Было найдено 9 подобных ошибок

  - В JIT-, AOT-оптимизаторе, тайпчекере, кодогенераторе

. . .

- Ещё 8 во время написания спецификации

# Напоследок

## Выводы

. . .

- Зависимые типы можно применять для спецификации сложных входных данных!

. . .

- Ошибки у вполне тестированных систем лежат в пересечении множества фич

. . .

- Одна спецификация находит много ошибок

. . .

- Нацеленность не всегда полезна, ошибки могут быть не там, где мы их ожидаем увидеть

. . .

- Property-based testing классный

. . .

- Зависимые типы классные ;-)

. . .

- А вместе -- так совсем улёт

## \only<1>{Если стало интересно}\only<2>{Спасибо!}

::: {=latex}
\hspace*{-.5cm}
\begin{tikzpicture}

\node (presentation) [label={Эта презентация}] at (0, 0) {
  \qrcode[hyperlink, height=3cm]{https://github.com/buzden/slides-of-lectures/blob/master/2024.03.19-deptyp-plus-pbt-is-love.pdf}
};
\node (code) [label={Код со слайдов}, right = 7.85cm of presentation] {
  \qrcode[hyperlink, height=3cm]{https://github.com/buzden/code-for-lectures/tree/master/2024.03.19-deptyp-plus-pbt-is-love}
};
\node (dtc) [label=DepTyCheck, below right = -1cm and 2.3cm of presentation] {
  \qrcode[hyperlink, height=3cm]{https://github.com/buzden/deptycheck}
};

\end{tikzpicture}
:::

\vfill

. . .

::: center
:::: Large
Вопросы?
::::
:::
