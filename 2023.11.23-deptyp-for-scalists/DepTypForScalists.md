---
lang: ru-RU

author: "Денис Буздало́в"
title: "Скалисты уже знают зависимые типы"
subtitle: "Но это не точно"
date: "23 ноября 2023"

aspectratio: 1610

mainfont: "DejaVu Serif"
monofont: "Iosevka Extended:-calt;+IDRS"
#monofont: "Fira Code:+calt;+ss09;+ss03;+cv29;+cv24"
linkstyle: bold

theme: "Singapore"
colortheme: "seahorse"
section-titles: true

#theme: "Boadilla"
#section-titles: false

header-includes:
  - "\\usepackage{framed}"
  - "\\usepackage{hyperref}"
  - "\\font\\nullfont=cmr10"
  - "\\AtBeginSection{}"
  - "\\setbeamertemplate{caption}{\\raggedright\\insertcaption\\par}"
---

# Здравствуйте

## Зависимые типы?

. . .

- Что?

. . .

- В Scala?

. . .

- Зачем может быть нужно?

. . .

- Beyond Scala

## Дисклеймеры

. . .

- Лекция познавательно-развлекательная

. . .

- Слушатели, возможно, Scala знают лучше докладчика

. . .

- Слайды с последовательно появляющимся текстом

. . .

- Некоторые вещи, для упрощения изложения, будут заметаться под ковёр

## О лекции

- Будет много кода

. . .

- Многое будет иллюстрироваться в непривычном синтаксисе

. . .

- Idris --- довольно произвольный выбор

  . . .

  - полноценные нативные зависимые типы
  - достаточно практичный
  - докладчик банально лучше всего с ним знаком ;-)

. . .

- Цель --- понимание концепций слушателями, поэтому вопросы, уточнения в процессе

. . .

- Нету цели унизить Скалу, ни синтаксически, ни в теории типов

. . .

- Привыкание, зависимость, во все тяжкие...

<!-- Заголовок здесь, а не в самом начале, чтобы не вставлялся лишний слайд -->
<!-- idris
import Control.Monad.Eval

import Data.List
import Data.List1
import Data.Validated
import Data.Vect
import Data.So
import Data.String

import System
-->

# Привыкание...

## Синтаксис

. . .

```scala
enum Tree[A]:
  case Leaf(a: A)
  case Node(value: A, to: NonEmptyList[Tree[A]])
```

. . .

\vfill

```idris
data Tree a
  = Leaf a
  | Node a (List1 (Tree a))
```

## Синтаксис

```scala
given Functor[Tree] with
  def map[A, B](fa: Tree[A])(f: A => B): Tree[B] =
    def go(tree: Tree[A]): Eval[Tree[B]] = tree match
      case Leaf(x) => Eval.now(Leaf(f(x)))
      case Node(x, ts) => Eval.defer(
        ts.traverse(go).map(Node(f(x), _))
      )
    go(fa).value
```

. . .

\vfill

```idris
Functor Tree where
  map f = eval . go where
    go : Tree a -> Eval $ Tree b
    go (Leaf x)    = pure $ Leaf $ f x
    go (Node x ts) = defer $ Node (f x) <$> traverse go ts
```

## Синтаксис

```scala
def minimum[A](using Order[A])(tree: Tree[A]): A = tree match
  case Leaf(x)     => x
  case Node(x, ts) => x `min` ts.map(minimum).minimum
```

. . .

\vfill

<!-- idris
namespace List1
  export
  minimum : Ord a => List1 a -> a
  minimum $ x:::xs = minimum $ x::xs
-->

```idris
minimum : Ord a => Tree a -> a
minimum $ Leaf x    = x
minimum $ Node x ts = x `min` minimum (map minimum ts)
```

## Синтаксис

::: columns

:::: column

```scala
case class User(
  name: UserName,
  passport: Passport,
  birthDate: BirthDate)

def u : User = ???
def n : UserName = u.name

case class ValidationError(
  msg: String)
```

::::

. . .

:::: column

<!-- idris
data UserName : Type
data Passport : Type
data BirthDate : Type

namespace BirthDate
  export
  fromString : String -> BirthDate
-->

```idris
record User where
  constructor MkUser
  name      : UserName
  passport  : Passport
  birthDate : BirthDate

u : User
n : UserName
n = u.name

record ValidationError where
  constructor MkValidationError
  msg : String
```

<!-- idris
%hide n
%hide u
-->

::::

:::

## Синтаксис

```scala
def validateUserName(input: String):
  ValidatedNel[ValidationError, UserName] = ???
def validatePassport(input: String):
  ValidatedNel[ValidationError, Passport] = ???
def validateBirthDate(input: String):
  ValidatedNel[ValidationError, BirthDate] = ???
```

. . .

\vfill

```idris
validateUserName :
  String -> ValidatedL ValidationError UserName
validatePassport :
  String -> ValidatedL ValidationError Passport
validateBirthDate :
  String -> ValidatedL ValidationError BirthDate
```

## Синтаксис

```scala
def user: ValidatedNel[ValidationError, User] = (
  validateUserName("Vova"),
  validatePassport("1-1"),
  validateBirthDate("04-02-1942")
).mapN(User.apply)
```

. . .

\vfill

```idris
user : ValidatedL ValidationError User
user = [| MkUser
           (validateUserName "Vova")
           (validatePassport "1-1")
           (validateBirthDate "04-02-1942")
       |]
```

# ...и зависимость

## \only<-2>{Старые знакомые?}\only<3->{Полиморфизм: типы зависят от типов}

. . .

<!-- https://scastie.scala-lang.org/FlL99zOlSEaMAC93osAhGw -->

```scala
def last[A](xs: List[A]): Option[A] = xs match
  case Nil      => None
  case x :: Nil => Some(x)
  case _ :: xs  => last(xs)
```

. . .

. . .

\vfill

``` {=latex}
\begin{onlyenv}<-4>
```

<!-- idris
namespace LastNoA {
-->

```idris
last : List a -> Maybe a
last []      = Nothing
last [x]     = Just x
last (x::xs) = last xs
```

<!-- idris
  }
-->

``` {=latex}
\end{onlyenv}
\begin{onlyenv}<5>
```

<!-- idris
namespace LastForall {
-->

```idris
last : forall a. List a -> Maybe a
last []      = Nothing
last [x]     = Just x
last (x::xs) = last xs
```

<!-- idris
  }
-->

``` {=latex}
\end{onlyenv}
\begin{onlyenv}<6>
```

<!-- idris
namespace LastImpANoType {
-->

```idris
last : {0 a : _} -> List a -> Maybe a
last []      = Nothing
last [x]     = Just x
last (x::xs) = last xs
```

<!-- idris
  }
-->

``` {=latex}
\end{onlyenv}
\begin{onlyenv}<7->
```

<!-- idris
namespace LastImpAType {
-->

```idris
last : {0 a : Type} -> List a -> Maybe a
last []      = Nothing
last [x]     = Just x
last (x::xs) = last xs
```

<!-- idris
  }
-->

``` {=latex}
\end{onlyenv}
```

## \only<-5>{Лёгкая зависимость}\only<6>{Тип зависит от значения}\only<7->{Тип зависит от типа внутри значения}

. . .

``` {=latex}
\begin{onlyenv}<2-3>
```

Пример:

- интерфейс кодировки значения одного типа другим

. . .

- целевой тип определяется способом кодировки

``` {=latex}
\end{onlyenv}
```
. . .


``` {=latex}
\begin{onlyenv}<-7>
```

```scala
trait Encoder[From]:
  type To
  def encode(from: From): To
```

``` {=latex}
\end{onlyenv}
\begin{onlyenv}<8->
```

```scala
trait Encoder[From]:
  type To                                  // <-- type member
  def encode(from: From): To
```

``` {=latex}
\end{onlyenv}
```
. . .

``` {=latex}
\begin{onlyenv}<-7>
```

```scala
def accEncoded[A](using Dec: Encoder[A])
                 (using Semigroup[Dec.To])
                 (x: A, rest: Dec.To): Dec.To =
  Dec.encode(x) |+| rest
```

``` {=latex}
\end{onlyenv}
\begin{onlyenv}<8->
```

```scala
def accEncoded[A](using Dec: Encoder[A])
                 (using Semigroup[Dec.To])
                 (x: A, rest: Dec.To): Dec.To =
  Dec.encode(x) |+| rest   // ^^^^^^      path-dependent type
```

``` {=latex}
\end{onlyenv}
```

\pause\pause\pause\pause
\vfill\vfill

```idris
interface Encoder from where
  0 To : Type
  encode : from -> To
```

. . .

```idris
accEncoded : (dec : Encoder from) => Semigroup (To @{dec}) =>
             from -> To @{dec} -> To @{dec}
accEncoded x rest = encode x <+> rest
```

## Тип зависит от типа внутри значения

<!-- scala
def toList[A](tree: Tree[A]): List[A] = tree match
  case Leaf(x) => List(x)
  case Node(x, ts) => x :: ts.foldMap(toList)
-->

```scala
given [A]: Encoder[Tree[A]] with
  type To = List[A]
  def encode(from: Tree[A]): To = toList(from)
```

``` {=latex}
\begin{uncoverenv}<3->
```

```scala
given AsString[A](using Show[A]): Encoder[Tree[A]] with
  type To = String
  def encode(from: Tree[A]): To = toList(from).show
```

``` {=latex}
\end{uncoverenv}
```

\vfill\vfill

<!-- idris
toList : Tree a -> List a
toList $ Leaf x    = [x]
toList $ Node x ts = x :: foldMap toList ts

%hide Prelude.toList
-->

``` {=latex}
\begin{uncoverenv}<2->
```

```idris
Encoder (Tree a) where
  To = List a
  encode = toList
```

``` {=latex}
\end{uncoverenv}

\begin{uncoverenv}<4->
```

```idris
[AsString] Show a => Encoder (Tree a) where
  To = String
  encode = show . toList
```

``` {=latex}
\end{uncoverenv}
```

## Тип зависит от типа внутри значения

```scala
def aTree: Tree[Int] = Node(5,
  NonEmptyList(Leaf(4),
  List(Leaf(6), Node(7, NonEmptyList(Leaf(8), List())))))
```

``` {=latex}
\begin{uncoverenv}<3->
```

```scala
def aList: List[Int] = accEncoded(aTree, List(0, 1))
```

``` {=latex}
\end{uncoverenv}
\begin{uncoverenv}<5->
```

```scala
def aStr: String = accEncoded(using AsString[Int])(aTree, "01")
```

``` {=latex}
\end{uncoverenv}
```

\vfill\vfill

``` {=latex}
\begin{uncoverenv}<2->
```

```idris
aTree : Tree Nat
aTree = Node 5 $ Leaf 4:::Leaf 6 :: Node 7 (Leaf 8:::[]) :: []
```

``` {=latex}
\end{uncoverenv}
\begin{uncoverenv}<4->
```

```idris
aList : List Nat
aList = accEncoded aTree [0, 1]
```

``` {=latex}
\end{uncoverenv}
\begin{uncoverenv}<6->
```

```idris
aStr : String
aStr = accEncoded @{AsString} aTree "01"
```

``` {=latex}
\end{uncoverenv}
```

## \only<-7>{Вы уже давно это знаете (наверное)}\only<8->{Тип зависит от значения}

. . .

\begin{centering}

Для любого натурального $n$ в пространстве векторов размерности $n$
если $p(x, y)$ --- метрика, над ней выполнено неравенство треугольника

\end{centering}

. . .

\vfill

\begin{centering}

$\forall n \colon \mathbb{N} \cdot \pause
\forall p \colon \mathbb{R}^n \times \mathbb{R}^n \to \mathbb{R} \cdot$ \pause
$p(\cdot, \cdot) \text{~---~метрика} \Longrightarrow\pause\newline
\forall x, y, z \colon \mathbb{R}^n \cdot p(x, y) + p(y, z) \geq p(x, z)$

\end{centering}

. . .

\vfill

\centering{Вектор размерности $n$?}

# Тяжёлые формы

## Вектор размерности \only<-4,7->{$n$\phantom{?}}\only<5-6>{?\phantom{$n$}}

. . .

``` {=latex}
\begin{onlyenv}<-4>
```

Хотим:

- создавать корректно

. . .

- паттерн-матчить уверенно

. . .

- сохранение при преобразованиях (напр. `map`, `traverse`)

``` {=latex}
\end{onlyenv}
```

``` {=latex}
\begin{uncoverenv}<8->
```

``` {=latex}
\begin{onlyenv}<-9,11->
```

```scala
sealed trait Nat
final abstract class Z           extends Nat
final abstract class S[N <: Nat] extends Nat
```

``` {=latex}
\end{onlyenv}
\begin{onlyenv}<10>
```

```scala
// Int
// 0 <: Int
// compiletime.ops.int.S
```

``` {=latex}
\end{onlyenv}
```

``` {=latex}
\end{uncoverenv}
```

``` {=latex}
\begin{onlyenv}<5>
```

```scala
enum List[+A]:
  case Nil
  case Cons(head: A, tail: List[A])
```

``` {=latex}
\end{onlyenv}
\begin{onlyenv}<6>
```

```scala
enum List[+A]:
  case Nil                             extends List[Nothing]
  case Cons(head: A, tail: List[A])    extends List[A]
```

``` {=latex}
\end{onlyenv}
\begin{onlyenv}<7-8>
```

```scala
enum Vect[N <: ???, +A]:
  case Nil                             extends Vect[?, Nothing]
  case Cons(head: A, tail: Vect[N, A]) extends Vect[??? , A]
```

``` {=latex}
\end{onlyenv}
\begin{onlyenv}<9,11->
```

```scala
enum Vect[N <: Nat, +A]:
  case Nil                             extends Vect[Z, Nothing]
  case Cons(head: A, tail: Vect[N, A]) extends Vect[S[N], A]
```

``` {=latex}
\end{onlyenv}
\begin{onlyenv}<10>
```

```scala
enum Vect[N <: Int, +A]:
  case Nil                             extends Vect[0, Nothing]
  case Cons(head: A, tail: Vect[N, A]) extends Vect[S[N], A]
```

``` {=latex}
\end{onlyenv}
```

``` {=latex}
\begin{uncoverenv}<12->
\vfill
```

```scala
extension [A](hd: A)
  def ::[N <: Nat](tl: Vect[N, A]): Vect[S[N], A] = Cons(hd, tl)
```

```scala
object `::`:
  def unapply[N <: Nat, A](v: Vect[S[N], A]): (A, Vect[N, A]) =
    v match { case Cons(x, xs) => (x, xs) }
```

``` {=latex}
\end{uncoverenv}
```

## Вектор размерности $n$\phantom{?}

\vspace{-\fill}\vspace{2\parskip}

\only<1>{Хотим: создавать корректно}

. . .

```scala
type Four = S[S[S[S[Z]]]]
type Five = S[Four]
```

. . .

\vfill

```scala
def aVect5 : Vect[Five, Int] = 1 :: 2 :: 3 :: 4 :: 5 :: Nil
def aVect4 : Vect[Four, Int] = 1 :: 2 :: 3 :: 4 :: Nil
```

. . .

\vfill

```scala
def badVect5 : Vect[Five, Int] = 1 :: 2 :: 3 :: 4 :: Nil
```

. . .

``` {=latex}
\begin{framed}
```

```scala
Found:    Vect[S[S[S[S[Z]]]], Int]
Required: Vect[Five, Int]
```

``` {=latex}
\end{framed}
```

## Вектор размерности $n$\phantom{?}

\vspace{-\fill}\vspace{2\parskip}

\only<1>{Хотим: паттерн-матчить уверенно}

. . .

```scala
//                   def aVect5 = 1 :: 2 :: 3 :: 4 :: 5 :: Nil
```

\vfill

. . .

```scala
def secFif: (Int, Int) = aVect5 match
  case _ :: sec :: _ :: _ :: fif :: Nil => (sec, fif)
```

. . .

\vspace{-\parskip}

```scala
  //   ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  //                          |
  //                      exhaustive pattern matching
```

## Вектор размерности $n$\phantom{?}

\vspace{-\fill}\vspace{2\parskip}

Хотим: сохранение при преобразованиях (напр. `map`, `traverse`)

. . .

\vfill

```scala
given [N <: Nat]: Functor[[A] =>> Vect[N, A]] with
  def map[A, B](v: Vect[N, A])(f: A => B): Vect[N, B] = v match
    case Nil         => Nil
    case Cons(x, xs) => Cons(f(x), xs.map(f))
```

. . .

\vfill

```scala
given [N <: Nat]: Traverse[[A] =>> Vect[N, A]] with
  ...
  def traverse[G[_]: Applicative, A, B]
              (fa: Vect[N, A])(f: A => G[B]): G[Vect[N, B]] =
    fa match
      case Nil         => Nil.pure
      case Cons(x, xs) => (f(x), xs.traverse(f)).mapN(Cons.apply)
```

## Вектор размерности $n$\phantom{?}

\vspace{-\fill}\vspace{2\parskip}

``` {=latex}
\only<1>{%
```
Хотим: сохранение при преобразованиях (напр. `map`, `traverse`)
``` {=latex}
}
```

. . .

```scala
//                   def aVect5 = 1 :: 2 :: 3 :: 4 :: 5 :: Nil
```

. . .

\vfill

``` {=latex}
\begin{onlyenv}<-3>
```

```scala
def secFifStr: (String, String) = aVect5.map(_.show) match
  case mapped => ???
```

``` {=latex}
\end{onlyenv}
\begin{onlyenv}<4->
```

```scala
def secFifStr: (String, String) = aVect5.map(_.show) match
  case _ :: sec :: _ :: _ :: fif :: Nil => (sec, fif)
```

``` {=latex}
\end{onlyenv}
```

\pause\pause
\vfill

```scala
def secFifA[F[_]: Applicative, B](f: Int => F[B]): F[(B, B)] =
  aVect5.traverse(f).map:
    case _ :: sec :: _ :: _ :: fif :: Nil => (sec, fif)
```

## Вектор размерности $n$\phantom{?}

``` {=latex}
\begin{uncoverenv}<3->
```

```scala
type +[N <: Nat, M <: Nat] <: Nat = N match
  case Z    => M
  case S[k] => S[k + M]
```

``` {=latex}
\end{uncoverenv}
\vfill
\begin{onlyenv}<-1>
```

```scala
def concat[A]
          (l: List[A], r: List[A]): List[A] =
  l match
    case Nil         => r
    case x :: xs     => x :: concat(xs, r)
```

``` {=latex}
\end{onlyenv}
\begin{onlyenv}<2-3>
```

```scala
def concat[N <: Nat, M <: Nat, A]
          (l: Vect[N, A], r: Vect[M, A]): Vect[ ??? , A] =
  l match
    case Nil         => r
    case Cons(x, xs) => x :: concat(xs, r)
```

``` {=latex}
\end{onlyenv}
\begin{onlyenv}<4-5>
```

```scala
def concat[N <: Nat, M <: Nat, A]
          (l: Vect[N, A], r: Vect[M, A]): Vect[N + M, A] =
  l match
    case Nil         => r
    case Cons(x, xs) => x :: concat(xs, r)
```

``` {=latex}
\end{onlyenv}
\begin{onlyenv}<6->
```

```scala
extension [N <: Nat, A](l: Vect[N, A])
  def ++[M <: Nat](r: Vect[M, A]): Vect[N + M, A] = l match
    case Nil         => r
    case Cons(x, xs) => x :: (xs ++ r)
```

\vspace{-\parskip}
\phantom{\texttt{code}}

``` {=latex}
\end{onlyenv}
\vfill
```

\uncover<5->{NB: нет зависимости от значения}

<!-- // this should work without the cast, but match type does not reduce well due to https://github.com/lampepfl/dotty/issues/15020 -->

## Вектор размерности $n$\phantom{?}

\vspace{-\fill}\vspace{2\parskip}

```scala
//                  def last[A](xs: List[A]): Option[A] = ???
```

```idris
--                  last : {0 a : Type} -> List a -> Maybe a
```

. . .

\vfill

```scala
// sealed trait Nat

enum Vect[N <: Nat, +A]:
  case Nil                             extends Vect[Z, Nothing]
  case Cons(head: A, tail: Vect[N, A]) extends Vect[S[N], A]
```

. . .

\vfill

<!-- idris
%hide Data.Vect.Vect
%hide Data.Vect.Nil
%hide Data.Vect.(::)
%hide Data.Vect.(++)
%hide Data.Vect.replicate
-->

```idris
-- data Nat = Z | S n

data Vect : Nat -> Type -> Type where
```

. . .

\vspace{-\parskip}

```idris
  Nil  : Vect Z a
  (::) : a -> Vect n a -> Vect (S n) a
```

<!-- idris
aVect5 : Vect 5 Int
aVect5 = [1, 2, 3, 4, 5]
-->

## Вектор размерности $n$\phantom{?}

```scala
// type +[N <: Nat, M <: Nat] <: Nat = N match
//   case Z    => M
//   case S[k] => S[k + M]

def concat[N <: Nat, M <: Nat, A]
          (l: Vect[N, A], r: Vect[M, A]): Vect[N + M, A] =
  l match { case Nil         => r
            case Cons(x, xs) => x :: concat(xs, r) }
```

. . .

\vfill

```idris
-- (+) : Nat -> Nat -> Nat
-- Z   + m = m
-- S n + m = S $ n + m

(++) : Vect n a -> Vect m a -> Vect (n + m) a
[]      ++ ys = ys
(x::xs) ++ ys = x :: (xs ++ ys)
```

# Трещит по швам

## Вектор размерности $n$: level up

``` {=latex}
\begin{uncoverenv}<3->
\begin{uncoverenv}<5,7->
```

``` {=latex}
\begin{onlyenv}<-5>
```

```scala
// sealed trait Nat
// final abstract class Z           extends Nat
// final abstract class S[N <: Nat] extends Nat
```

``` {=latex}
\end{onlyenv}
\begin{onlyenv}<6->
```

```scala
enum NatVal[N <: Nat]:
  case ZV               extends NatVal[Z]
  case SV(n: NatVal[N]) extends NatVal[S[N]]
```

``` {=latex}
\end{onlyenv}
```

``` {=latex}
\end{uncoverenv}
\vfill
\begin{onlyenv}<-3>
```

```scala
def replicate[N <: Nat, A](a: A): Vect[N, A]
```

\vspace{-2\parskip}
\phantom{\texttt{code}}\par\phantom{\texttt{code}}

``` {=latex}
\end{onlyenv}
\begin{onlyenv}<4-5>
```

```scala
def replicate[N <: Nat, A](n: N, a: A): Vect[N, A]
```

\vspace{-2\parskip}
\phantom{\texttt{code}}\par\phantom{\texttt{code}}

``` {=latex}
\end{onlyenv}
\begin{onlyenv}<6-7>
```

```scala
def replicate[N <: Nat, A](n: ???, a: A): Vect[N, A]
```

\vspace{-2\parskip}
\phantom{\texttt{code}}\par\phantom{\texttt{code}}

``` {=latex}
\end{onlyenv}
\begin{onlyenv}<8>
```

```scala
def replicate[N <: Nat, A](n: NatVal[N], a: A): Vect[N, A]
```

\vspace{-2\parskip}
\phantom{\texttt{code}}\par\phantom{\texttt{code}}

``` {=latex}
\end{onlyenv}
\begin{onlyenv}<9->
```

```scala
def replicate[N <: Nat, A](n: NatVal[N], a: A): Vect[N, A] =
  n match { case ZV    => Nil
            case SV(m) => a :: replicate(m, a) }
```

``` {=latex}
\end{onlyenv}
\end{uncoverenv}
```

\vfill\vfill

``` {=latex}
\begin{onlyenv}<2->
```

```idris
replicate : (n : Nat) -> a -> Vect n a
replicate Z     _ = []
replicate (S n) x = x :: replicate n x
```

``` {=latex}
\end{onlyenv}
```

## Вектор размерности $n$: level up

```scala
def fourVal: NatVal[Four] = SV(SV(SV(SV(ZV))))
```

. . .

```scala
def aRep4: Vect[Four, Int] = replicate(fourVal, 9)
```

. . .

```scala
def a9 = aVect5 ++ aRep4
```

. . .

\vfill

```idris
aRep4 : Vect 4 Int
aRep4 = replicate 4 9
```

. . .

```idris
a9 : ?
a9 = aVect5 ++ aRep4
```

## Вектор размерности $n$: level up

<!-- idris
%hide Syntax.PreorderReasoning.Generic.infix.(...)
%hide Syntax.PreorderReasoning.infix.(...)

%hide Main.Vect
%hide Main.Nil
%hide Main.(::)
%hide Main.(++)
%hide Main.replicate

%unhide Data.Vect.Vect
%unhide Data.Vect.Nil
%unhide Data.Vect.(::)
%unhide Data.Vect.(++)
%unhide Data.Vect.replicate

%hide Data.List.replicate
%hide String.replicate
%hide BirthDate.fromString
-->

\vspace{-\fill}\vspace{2\parskip}

```idris
--                       parsePositive ~~ String -> Maybe Nat
--                       getLine       ~~ IO String
```

\vfill

```idris
manageS : String -> IO Integer

useVects : String -> IO String
useVects str = do
  let Just n = parsePositive str
    | Nothing => pure "not a number"
  let xs = replicate n "x"
  ys <- traverse manageS xs
  pure $ show $ xs `zip` ys
```

\vfill

## Вектор размерности $n$: level up

\vspace{-\fill}\vspace{2\parskip}

```idris
--                       parsePositive ~~ String -> Maybe Nat
```

\vfill

``` {=latex}
\begin{uncoverenv}<4->
```

```scala
trait SomeNatVal:
  type N <: Nat
  val value: NatVal[N]
```

``` {=latex}
\end{uncoverenv}
```

\vfill

``` {=latex}
\begin{onlyenv}<2>
```

```scala
def parsePositive[N <: Nat](str: String): Option[NatVal[N]] = ???
```

``` {=latex}
\end{onlyenv}
\begin{onlyenv}<3-4>
```

```scala
def parsePositive(str: String): Option[???] = ???
```

``` {=latex}
\end{onlyenv}
\begin{onlyenv}<5->
```

```scala
def parsePositive(str: String): Option[SomeNatVal] = ???
```

``` {=latex}
\end{onlyenv}
```

\vfill

``` {=latex}
\begin{uncoverenv}<6->
```

```scala
def manageS(str: String): IO[Int] = ???
def useVects(str: String): IO[String] = parsePositive(str) match
  case None    => "not a number".pure
  case Some(n) =>
    val xs = replicate(n.value, "x")
    xs.traverse(manageS).map(ys => zip(xs, ys).show)
```

``` {=latex}
\end{uncoverenv}
```

## Минуточку!

. . .

```scala
trait SomeNatVal:
  type N <: Nat
  val value: NatVal[N]
```

. . .

\vfill

``` {=latex}
\begin{onlyenv}<-3>
```

```scala
def replicate[N <: Nat, A](n: NatVal[N], a: A): Vect[N, A] =
  n match
    case ZV    => Nil
    case SV(m) => a :: replicate(m, a)
```

``` {=latex}
\end{onlyenv}
\begin{onlyenv}<4->
```

```scala
def replicate[A](n: SomeNatVal, a: A): Vect[n.N, A] =
  n.value match
    case ZV    => Nil
    case SV(m) => a :: replicate(SomeNatVal(m), a)
```

``` {=latex}
\end{onlyenv}
```

\pause\pause

``` {=latex}
\begin{framed}
```

```scala
Found:    (Vect.Nil : Vect[Z, Nothing])
Required: Vect[n.N, A]
```

``` {=latex}
\end{framed}
```

# Во все тяжкие

## Экзистенциальный кризис

. . .

``` {=latex}
\begin{center}
```

![](.hwy.png){ height=85% }

``` {=latex}
\end{center}
```

## Как вы индексируете вектора\only<1-3>{?}\only<4->{ размерности $n$?}

. . .

```scala
trait Seq[+A] extends ..., PartialFunction[Int, A], ...
```

. . .

```scala
def lift: Int => Option[A]
```

. . .

\vfill

``` {=latex}
\begin{uncoverenv}<6->
```

<!-- idris
%hide Data.Fin.Fin
-->

```idris
data Fin : Nat -> Type where
  FZ : Fin (S n)
  FS : Fin n -> Fin (S n)
```

``` {=latex}
\end{uncoverenv}
```

``` {=latex}
\begin{uncoverenv}<4->
```

<!-- idris
namespace IndexNat {
-->

``` {=latex}
\begin{onlyenv}<-4>
```

```idris
total
index : Nat -> Vect n a -> Maybe a
```

``` {=latex}
\end{onlyenv}
```

<!-- idris
  }
namespace IndexQu {
-->

``` {=latex}
\begin{onlyenv}<5-6>
```

```idris
total
index : ? -> Vect n a -> a
```

``` {=latex}
\end{onlyenv}
```

<!-- idris
index x = do
  let y = the Unit x
  ?index_qu
  }
-->

``` {=latex}
\begin{onlyenv}<7->
```

```idris
total
index : Fin n -> Vect n a -> a
```

``` {=latex}
\end{onlyenv}
\end{uncoverenv}
```

## Вершина айсберга

<!-- idris
namespace BinTree {
-->

\vspace{-\fill}\vspace{2\parskip}

``` {=latex}
\begin{uncoverenv}<4->
```

```idris
data SortedBinTree : Type -> Type
data All : (a -> Bool) -> SortedBinTree a -> Type
```

``` {=latex}
\end{uncoverenv}
```

\vfill

``` {=latex}
\begin{onlyenv}<2>
```

<!-- idris
namespace Unsorted {
-->

```idris
data BinTree : Type -> Type where
  Empty : BinTree a
  Node  : (x : a) -> (left, right : BinTree a) -> BinTree a
```

\vspace{-\parskip}\phantom{\texttt{code}}

<!-- idris
 }
-->

``` {=latex}
\end{onlyenv}
\begin{onlyenv}<3-4>
```

<!-- idris
namespace UnfinishedSorted {
%hide BinTree.SortedBinTree
-->

```idris
data SortedBinTree : Type -> Type where
  Empty : SortedBinTree a
  Node  : Ord a => (x : a) -> (left, right : SortedBinTree a) ->
          ?left_sorted   => ?right_sorted   => SortedBinTree a
```

<!-- idris
%unhide BinTree.SortedBinTree
 }
-->

``` {=latex}
\end{onlyenv}
\begin{onlyenv}<5->
```

```idris
data SortedBinTree : Type -> Type where
  Empty : SortedBinTree a
  Node  : Ord a => (x : a) -> (left, right : SortedBinTree a) ->
          All (< x) left => All (x <) right => SortedBinTree a
```

``` {=latex}
\end{onlyenv}
\begin{uncoverenv}<6->
```

\vfill

```idris
data All : (a -> Bool) -> SortedBinTree a -> Type where
  Empty' : All prop Empty
  Node'  : (o : Ord a) => {0 prop : a -> Bool} ->
           {0 pl : All (< x) l} -> {0 pr : All (x <) r} ->
           So (prop x) -> All prop l -> All prop r ->
           All prop $ Node x l r @{o} @{pl} @{pr}
```

``` {=latex}
\end{uncoverenv}
```


<!-- idris
 }
-->

## Вершина айсберга

\vspace{-\fill}\vspace{2\parskip}

<!-- idris
namespace BinTree {
-->

```idris
Leaf : Ord a => a -> SortedBinTree a
Leaf x = Node x Empty Empty
```

. . .

\vfill\vfill

```idris
good : SortedBinTree Int
good = Node 4 (Node 2 (Leaf 1) (Leaf 3))
              (Leaf 5)
```

. . .

\vfill

```idris
failing "Can't find an implementation for
         All (\\arg => 5 < arg) (Leaf 4)"
  bad : SortedBinTree Int
  bad = Node 5 (Node 2 (Leaf 1) (Leaf 3))
               (Leaf 4)
```

<!-- idris
 }
-->

# Напоследок

## \only<1>{Если стало интересно}\only<2>{Спасибо!}

::: columns

:::: column

![Literate Idris](.qr/idris-code-qr.png){ width=35% }

![Код на Scala](.qr/scala-code-qr.png){ width=35% }

::::

:::: column

![Idris 2 language](.qr/idris-qr.png){ width=35% }

![Эта презентация](.qr/slides-qr.png){ width=35% }

::::

:::

\vfill

. . .

\centering{\Large{Вопросы?}}
