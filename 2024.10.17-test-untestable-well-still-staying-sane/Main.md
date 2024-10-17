---
lang: ru-RU

author: "Денис Буздало́в"
title: "Хорошо протестировать нетестируемое\\newline и не сойти с ума"
date: |
  \small Heisenbug 2024 Autumn\newline\vspace{-.8\baselineskip}\newline Санкт-Петербург\newline\vspace{-.8\baselineskip}\newline17 октября 2024

aspectratio: 169
fontsize: 10pt

#mainfont: "DejaVu Serif"
mainfont: "Noto Sans"
monofont: "Iosevka Extended:-calt;+IDRS"
#monofont: "Fira Code:+calt;+ss09;+ss03;+cv29;+cv24"
linkstyle: bold

theme: "Singapore"
colortheme: "seahorse"
section-titles: true

header-includes: |
  \makeatletter\renewcommand*\verbatim@nolig@list{}\makeatother
  \usepackage{framed}
  \usepackage{hyperref}
  \usepackage[overlay]{textpos}
  \usepackage[normalem]{ulem}
  \usepackage[dvipsnames]{xcolor}
  \usepackage{tikzsymbols}
  \usepackage{qrcode}
  \usepackage{pifont}
  \def\good{\color{Green}\ding{52}}
  \def\bad{\color{BrickRed}\ding{56}}
  \usetikzlibrary{automata,positioning}
  \usetikzlibrary{shapes.multipart,shapes.symbols,shapes.geometric}
  \AtBeginSection{}
  \setbeamertemplate{caption}{\raggedright\insertcaption\par}
  \newcommand{\heart}{\dHeart[.9]}
  \def\textrightarrow{$\rightarrow$}
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
  \newenvironment{blackbox}%
    {\begin{minipage}{\textwidth-2em}\setbox0\vbox\bgroup\color{white}}%
    {\egroup\fboxsep1em \noindent\colorbox{black}{\usebox0}\end{minipage}}

# Those commands with `\end{frame}` in the beginning do now work after the slides with verbatim on them

---
# Хорошее тестирование

## Что такое *xорошее тестирование*?

<!-- idris
import Deriving.DepTyCheck.Gen

import Hedgehog

%default total

%hide Data.SortedMap.insert
%hide Data.SortedMap.Dependent.insert
%hide Data.SortedSet.insert
-->



<!--
::: center
:::: Large
Что такое *хорошее тестирование*?
::::
:::
-->

. . .

- Находит баги?

. . .

- Покрывает код?

. . .

- Покрывает функциональность/требования?

. . .

- Повышает уверенность?

. . .

- Много тестов?

. . .

- Быстро работает?

. . .

- Легко разрабатывается?

. . .

- Хотя бы присутствует?

## Авиационная байка

\vspace{-\fill}

:::: center
![](.images/tp-754-taxi.png){height=88%}

\vspace{-4\parskip}
`{\tiny Фото: The Aviation Herald}`{=latex}
::::

## Несколько фактов о самолётах

. . .

- второй круг

. . .

- даже если касание шасси

. . .

- торможение шасси и двигателем (реверс)

. . .

- реверс в полёте опасен, это предусмотрено

. . .

- 11 февраля 1978, Pacific Airline 314

. . .

- сертификационное требование:

  ::::center
  посадка \textrightarrow{} реверс \textrightarrow{} выключение \textrightarrow{} прямая тяга \textrightarrow{} взлёт
  ::::

. . .

- Airbus 320, двигатель CFM56, логика:

  \vspace{-3.3\parskip}
  \begin{equation*}
  \begin{split}
  \textrm{команда ухода на второй круг} \\
  \textrm{стойка под двигателем "на земле"}
  \end{split}
  \biggr\}
  \rightarrow{} \textrm{свернуть реверс}
  \end{equation*}

##

:::: center
![](.images/a320-cfm56-reversers.png){width=85%}

\vspace{-4\parskip}
`{\tiny Фото:Report~2022-150, Serious incident to~CS-TNV (Airbus~A320-214) in Copenhagen/Kastrup~(EKCH) on~8-4-2022}`{=latex}
::::
\vspace{-\fill}

## 8 апреля 2022, TAP Air Portugal 754

\vspace{-\fill}\vspace{-2\parskip}

::: {.only on=1}
:::: center
![](.images/tp-754-bounce.png){height=90%}

\vspace{-4\parskip}
`{\tiny Фото:Report~2022-150, Serious incident to~CS-TNV (Airbus~A320-214) in Copenhagen/Kastrup~(EKCH) on~8-4-2022}`{=latex}
::::
:::

::: {.only on=2}
:::: center
![](.images/tp-754-ga.png){height=90%}

\vspace{-4\parskip}
`{\tiny Фото:Report~2022-150, Serious incident to~CS-TNV (Airbus~A320-214) in Copenhagen/Kastrup~(EKCH) on~8-4-2022}`{=latex}
::::
:::

::: {.only on=3}
:::: center
![](.images/tp-754-ga-close.png){height=90%}

\vspace{-4\parskip}
`{\tiny Фото:Report~2022-150, Serious incident to~CS-TNV (Airbus~A320-214) in Copenhagen/Kastrup~(EKCH) on~8-4-2022}`{=latex}
::::
:::

## 8 апреля 2022, TAP Air Portugal 754

- уход на второй круг --- команда, не состояние

. . .

- cross-wind bounce

. . .

- пока команда давалась (0,18 с.), правое шасси было на земле, а левое в воздухе

. . .

- левый двигатель не свернул реверс

. . .

- redundancy: была подсистема, которая сделала auto idle

## Хорошее тестирование?

- софт был корректно сертифицирован

. . .

- 95 миллионов посадок

. . .

- оценки исправления софта --- к 2025

. . .

- изменения в процедуре сертификации

. . .

- такого не найдено в других конфигурациях

## Хорошее тестирование\phantom{?}

::: center
:::: Large
Я утверждаю: одно из свойств *хорошего метода хорошего тестирования* --- ставить тестируемую систему в такие ситуации (и находить такие баги),
о которых автор тестов даже не думал
::::
:::


# Property-based testing

## Property-based testing

. . .

- Тестирование функции/системы на *произвольном* входе

. . .

- Оценка, а не предугадывание результата

. . .

- Рандомизированная генерация входных значений

. . .

- Минимизация контрпримеров (shrinking)

. . .

- (Иногда) автоматическая деривация генераторов и минимизаторов

. . .

- Десятки библиотек под множество языков

  ::: tiny
  Haskell, Erlang, Scala, Python, Coq, Idris,
  C#, C++, Clojure, D, Elixir, Elm, F#, Go, Java, JavaScript, Julia, Kotlin, Nim, OCaml, Prolog, Racket, Ruby, Rust, Swift, TypeScript, ...
  :::

## \only<-4>{Свойство?\phantom{!}}\only<5-8>{Свойство!\phantom{?}}\only<9->{А что, если~~\colorbox[rgb]{.7,.7,.8}{\texttt{insert x xs = x :: xs}}?}

<!-- idris
insert : Ord a => a -> List a -> List a
insert = merge . singleton

arbitraryNat : Gen Nat
arbitraryNat = nat $ linear 0 9

arbitraryNatList : Gen $ List Nat
arbitraryNatList = list (exponential 0 1000) arbitraryNat

public export
sortedNatList : Gen $ List Nat
sortedNatList = foldr (\x, res => x :: map (+x) res) [] <$> arbitraryNatList

sortedNatListOk : Property
sortedNatListOk = withConfidence 1000000000 $ property $ do
  xs <- forAll sortedNatList
  assert $ sorted xs
  cover 40 "len big enough" $ length xs >= 2
  cover 40 "vals diverse" $ any (>= 2) xs
-->

\vspace{-\fill}\vspace{\parskip}

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
export infix 9 `eht`

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
  xs <- forAll sortedNatList
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
  xs <- forAll sortedNatList
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
  xs <- forAll sortedNatList
  assert $ sorted $ insert x xs
  assert $ x `elem` insert x xs
```
:::

<!-- idris
 }
-->

<!-- idris
main_pbt_insert : IO ()
main_pbt_insert = test
  [ "generators" `MkGroup`
    [ ("sortedNatListOk", sortedNatListOk)
    ]
  , "insert" `MkGroup`
    [ ("InsertWeakProp.insertOk", InsertWeakProp.insertOk)
    , ("InsertSortedProp.insertOk", InsertSortedProp.insertOk)
    , ("InsertSortedAndElemProp.insertOk", InsertSortedAndElemProp.insertOk)
    ]
  ]
-->

<!-- idris
namespace BadInsertOk

  export
  insertOk : Property
  insertOk = property $ do
    x  <- forAll arbitraryNat
    xs <- forAll sortedNatList
    assert $ sorted $ x :: xs
    assert $ x `elem` x :: xs

main_bad_insert : IO ()
main_bad_insert = test
  [ "sorted list insertion" `MkGroup`
    [ ("insertOk", BadInsertOk.insertOk)
    ]
  ]

-->

\vspace{\parskip}

::: {.only on=7}
:::: blackbox
::::: {=latex}
\begin{Verbatim}[commandchars=\\\{\}]
━━━ sorted list insertion ━━━
  \textcolor{green}{✓ insertOk passed 100 tests.}
\end{Verbatim}
:::::
::::
:::

::: {.only on=10-}
:::: blackbox
::::: {=latex}
\begin{Verbatim}[commandchars=\\\{\}]
━━━ sorted list insertion ━━━
  \textcolor{red}{✗ insertOk failed after 14 tests.}

    forAll 0 =
      \textcolor{Periwinkle}{1}

    forAll 1 =
      \textcolor{Periwinkle}{[0]}
\end{Verbatim}
:::::
::::
:::

##

::: center
![](.images/john-hughes-can-bus.png){height=90%}
:::

\footnotetext[1]{https://www.youtube.com/watch?v=zi0rHwfiX1Q}

##

::: center
![](.images/john-hughes-come-on.png){height=90%}
:::

\footnotetext[1]{https://www.youtube.com/watch?v=zi0rHwfiX1Q}

## Хорошо применённый property-based testing

\begin{itemize}

\item[\good]\pause одна спецификация находит ошибки в разных местах

\item[\good]\pause высокоуровневая спецификация может находить низкоуровневые проблемы

\item[\good]\pause может найти практически ненаходимое ручным тестированием

\item[\good]\pause находит то, о чём не подозревали, \textit{хороший} метод

\item[\good]\pause сложность тестирования растёт медленнее сложности SUT

\item[\bad]\pause надо уметь выбирать подходящие свойства

\item[\bad]\pause reimplementation trap

\item[\bad]\pause формализация требований, нужен опыт и mindsetting
  \begin{itemize}
  \item[\good]\pause инварианты, модели, метаморфное тестирование, автоматы
  \end{itemize}

\item[\bad]\pause написание генераторов, корректность, полнота, распределения
  \begin{itemize}
  \item[\good]\pause деривация
  \end{itemize}

\end{itemize}

## Деривация?

<!-- idris
namespace PBTDerivation {

-- Please mind, not a real derivator!
deriveGen : a

%hide Main.arbitraryNat
%hide Main.arbitraryNatList
%hide Main.sortedNatList
-->

::: {.uncover on=2-}
```idris
arbitraryNat : Gen Nat
```
:::
\vspace{-\parskip}

::: {.uncover on=3-}
```idris
arbitraryNat = deriveGen
```
:::
\vfill

::: {.uncover on=4-}
```idris
arbitraryNatList : Gen (List Nat)
```
:::
\vspace{-\parskip}

::: {.uncover on=6-}
```idris
arbitraryNatList = deriveGen
```
:::
\vfill

::: {.uncover on=2-}
```idris
sortedNatList : Gen (List Nat)
```
:::
\vspace{-\parskip}

::: {.uncover on=5-}
```idris
sortedNatList =
  foldr (\x, res => x :: map (+x) res) [] <$> arbitraryNatList
```
:::
\vfill

```idris
insertOk : Property
insertOk = property $ do
  x  <- forAll arbitraryNat
  xs <- forAll sortedNatList
  assert $ sorted $ insert x xs
  assert $ x `elem` insert x xs
```

<!-- idris
 }
-->

## Деривация?

:::: Large
::: center
Вот бы можно было выражать свои *намерения* так, чтобы компилятор сам вывел генератор

![](.images/thinking.png){width=20%}
:::
::::


# Зависимые типы

## Списки \uncover<4->{сортированные\only<-8>{?\phantom{!}}\only<9->{!\phantom{?}}}

\vspace{-\fill}\vspace{1.5\parskip}

<!-- idris
namespace SimpleNatList {
-->

::: {.only on=1-4}
```idris
data NatList : Type where
  Nil  : NatList
  (::) : Nat -> NatList -> NatList
```
\vspace{\parskip}
:::

::: {.only on=2-3}
```idris
actuallySorted : NatList
actuallySorted = 1 :: 2 :: 5 :: 9 :: Nil
```
\vspace{\parskip}
:::

::: {.only on=3}
```idris
unsorted : NatList
unsorted = 1 :: 5 :: 2 :: 9 :: 1 :: Nil
```
:::

<!-- idris
 }
namespace DumbSortedNatList {
-->

::: {.only on=5-6}
```idris
data SortedNatList : Type where
  Nil  : SortedNatList
  (::) : Nat -> SortedNatList -> SortedNatList
```
\vspace{-\parskip}

:::: {.only on=6}
```idris
         -- голова должна быть не больше головы хвоста
         -- (если есть)
```
::::
:::

<!-- idris
 }
namespace DumbNamedSortedNatList {
-->

::: {.only on=7-8}
```idris
data SortedNatList : Type where
  Nil  : SortedNatList
  (::) : (x : Nat) -> (xs : SortedNatList) -> SortedNatList
         -- `x` не больше головы `xs` (если есть)
```
\vspace{\parskip}
:::

::: {.only on=8}
```idris
data LTEHead : Nat -> SortedNatList -> Type where
  NoHead   : LTEHead n Nil
  SomeHead : So (n < x) -> LTEHead n (x::xs)
```
:::

<!-- idris
 }
namespace RealSortedNatList {

data SortedNatList : Type
data LTEHead : Nat -> SortedNatList -> Type
-->

::: {.only on=9-}
```idris
data SortedNatList : Type where
  Nil  : SortedNatList
  (::) : (x : Nat) -> (xs : SortedNatList) ->
         LTEHead x xs => SortedNatList
```
\vspace{\parskip}

```idris
data LTEHead : Nat -> SortedNatList -> Type where
  NoHead   : LTEHead n Nil
  SomeHead : So (n < x) -> LTEHead n $ (x::xs) @{_}
```
\vspace{\parskip}
:::

::: {.only on=10-11}
```idris
actuallySorted : SortedNatList
actuallySorted = 1 :: 2 :: 5 :: 9 :: Nil
```
\vspace{\parskip}
:::

::: {.only on=11}
```idris
failing "Can't find an implementation for LTEHead"
  unsorted : SortedNatList
  unsorted = 1 :: 5 :: 2 :: 9 :: 1 :: Nil
```
:::

<!-- idris
%logging "deptycheck" 5
-->

<!-- idris
namespace HedgehogSignature {
-->
::: {.only on=12}
```idris
arbitrarySortedNatList : Gen SortedNatList
```
:::
<!-- idris
 }
-->

<!-- idris
export
-->

::: {.only on=13-}
```idris
arbitrarySortedNatList : Fuel -> Gen MaybeEmpty SortedNatList
```
\vspace{-\parskip}
:::

::: {.only on=14-}
```idris
arbitrarySortedNatList = deriveGen
```
:::

::: {.only on=15-}
```idris
--                       ^^^^^^^^^
--                           \
--                            ---- DepTyCheck
```
:::

<!-- idris
export
toList : SortedNatList -> List Nat
toList []      = []
toList (x::xs) = x :: toList xs

 }
-->

<!-- idris
main_pick_sortedlist : IO ()
main_pick_sortedlist = pick (arbitrarySortedNatList $ limit 100) >>= printLn . map toList
-->

## Списки сортированные!\phantom{?}

::: footnotesize
:::: blackbox
::::: {=latex}
```
     ____    __     _         ___
    /  _/___/ /____(_)____   |__ \
    / // __  / ___/ / ___/   __/ /     Version 0.7.0-0e83d6c7c
  _/ // /_/ / /  / (__  )   / __/      https://www.idris-lang.org
 /___/\__,_/_/  /_/____/   /____/      Type :? for help

Welcome to Idris 2.  Enjoy yourself!
Main> :exec pick (arbitrarySortedNatList $ limit 100) >>= printLn . map toList
Just [56, 57, 74, 76, 89, 92, 95]
Main> :exec pick (arbitrarySortedNatList $ limit 100) >>= printLn . map toList
Just [7, 8, 53, 67, 91, 94, 96, 97]
Main> :exec pick (arbitrarySortedNatList $ limit 100) >>= printLn . map toList
Just [57, 94, 99]
Main>
```
:::::
::::
:::

<!-- Надо ли что-нибудь типа `Vect` и `index` с гарантированным возвратом значения без `Maybe` и всяких exception'ов? -->


# Применим!

## Пример из жизни

. . .

- Диалект Typescript

. . .

- Имеет интерпретатор с JIT и компилятор

. . .

- Свежая промышленная разработка

. . .

- Свойства

  . . .

  - семантически корректные программы должны компилироваться

  . . .

  - среди них завершающиеся программы должны интерпретироваться без неожиданных падений и зацикливаний

  . . .

  - все варианты запуска должны выдавать одинаковый результат

## Как это можно специфицировать

<!-- idris
%hide Language.Reflection.TT.Name
Name : Type
Name = String

data IsIn : Name -> List (Name, a) -> Type where
  MkIsIn : IsJust (lookup n xs) -> IsIn n xs

0 found : IsIn {a} n xs -> a
found $ MkIsIn _ with 0 (lookup n xs)
  _ | Just x = x

record FunSig
data Expr : (funs : List (Name, FunSig)) -> (vars : List (Name, Type)) -> Type -> Type

export infix 2 #=
export covering -- because of `Expr` below
-->

```idris
data Stmts : (functions  : List (Name, FunSig)) ->
             (varsBefore : List (Name, Type)) ->
             (varsAfter  : List (Name, Type)) -> Type where

  (.)  : (ty : Type) -> (n : Name) ->
         Stmts funs vars ((n, ty)::vars)

  (#=) : (n : Name) -> (0 lk : n `IsIn` vars) =>
         (v : Expr funs vars (found lk)) ->
         Stmts funs vars vars

  If   : (cond : Expr funs vars Bool) ->
         Stmts funs vars vThen -> Stmts funs vars vElse ->
         Stmts funs vars vars

  (>>) : Stmts funs preV midV  -> Stmts funs midV postV ->
         Stmts funs preV postV
```

## Как это можно специфицировать

<!-- idris
export infix 1 ==>
export
-->

```idris
record FunSig where
  constructor (==>)
  From : List Type
  To   : Type
```

\vfill

<!-- idris
covering -- actually, all is total, but I don't want to bother with `assert_total` in types
-->

```idris
data Expr : List (Name, FunSig) -> List (Name, Type) ->
            Type -> Type where

  C : (x : ty) -> Expr funs vars ty

  V : (n : Name) -> (0 lk : n `IsIn` vars) =>
      Expr funs vars (found lk)

  F : (n : Name) -> (0 lk : n `IsIn` funs) =>
      All (Expr funs vars) (found lk).From ->
      Expr funs vars (found lk).To
```

## Семантически корректные программы

\vspace{-\fill}

<!-- idris
namespace AlignHack
                              public export
-->
:::: small
```idris
                              StdF : List (Name, FunSig)
                              StdF = [ ("+" , [Int, Int] ==> Int)
                                     , ("<" , [Int, Int] ==> Bool)
                                     , ("++", [Int] ==> Int)
                                     , ("||", [Bool, Bool] ==> Bool) ]
```
::::
\vspace{-4\parskip} <!-- magic skills in slide alignment O_O -->

. . .

<!-- idris
covering
-->
```idris
program : Stmts StdF [] ?
program = do
  Int. "x"
  "x" #= C 5
  Int. "y"; Bool. "res"
  "y" #= F "+" [V "x", C 1]
```
\vspace{-\parskip}
. . .

```idris
  If (F "<" [F "++" [V "x"], V "y"])
     (do "y" #= C 0; "res" #= C False)
     (do Int. "z"; "z" #= F "+" [V "x", V "y"]
         Bool. "b"; "b" #= F "<" [V "x", C 5]
         "res" #= F "||" [V "b", F "<" [V "z", C 6]])
```

\vfill

## Семантически некорректные программы

```idris
failing "Mismatch between: Int and Bool"
  bad : Stmts StdF [] ?
  bad = do
    Int. "x"; "x" #= C 5
    Bool. "y"; "y" #= F "+" [V "x", C 1]
```
\pause\vfill

```idris
failing "Mismatch between: [] and [Int]"
  bad : Stmts StdF [] ?
  bad = do
    Int. "x"; "x" #= C 5
    Int. "y"; "y" #= F "+" [V "x"]
```
\pause\vfill

```idris
failing "Mismatch between: Bool and Int"
  bad : Stmts StdF [] ?
  bad = do
    Int. "x"; "x" #= C 5
    Int. "y"; "y" #= F "+" [C True, V "x"]
```

## Применим

::: {.only on=-1}
:::: center
::::: Large
Testing...
:::::
::::
:::

::: {.only on=2-3}
\vfill
:::: blackbox
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

## Применим

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
::::: blackbox
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
:::::
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

## Применим

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
::::: blackbox
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
:::::
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

## Применим

::: {.only on=-1}
:::: center
::::: Large
Testing...
:::::
::::
:::

::: {.only on=2-}
\vspace{-\fill}\vspace{8\parskip}
:::: {.only on=-3}
::::: blackbox
```
TypeError: Unreachable statement. [<filename>:26:34]
```
:::::
::::
:::: {.only on=4-}
::::: blackbox
```
TypeError: Unreachable statement. [<filename>:3:30]
```
:::::
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
::::
:::

## Применим

- ...и так далее

. . .

- Было найдено 9 подобных ошибок

  - В JIT-, AOT-оптимизаторе, тайпчекере, кодогенераторе

. . .

- Ещё 8 во время написания спецификации

. . .

- Наша спецификация

  . . .

  - Подмножество

    - Завершающиеся программы

    - Циклы, ветвления, присваивания, исключения

    - Классы без методов, числа, массивы

  . . .

  - ~330 строк кода спецификация языка + столько же обвязка

  . . .

  - Частично деривированные, частично рукописные генераторы

## Ещё?

. . .

:::: {.only on=2}
::: center
![](.images/scastie-blank.png){height=85%}
:::
::::

:::: {.only on=3-}
::: center
![](.images/scastie-bug.png){height=85%}
:::
::::


# Напоследок

##

\begin{itemize}

\item\pause Property-based testing
  \vspace{-.5\parskip}
  \begin{itemize}
  \setlength\itemsep{-.5\parskip}
  \item[\good]\pause \textit{хороший} метод
  \item[\bad]\pause требует освоения
  \item[\bad]\pause требует серьёзного взгляда на требования и формализацию
  \item[\good]\pause экономически оправдан для сложных и ответственных систем
  \end{itemize}

\item\pause Зависимые типы
  \vspace{-.5\parskip}
  \begin{itemize}
  \setlength\itemsep{-.5\parskip}
  \item[\good]\pause мощны и выразительны
  \item[\bad]\pause высокий уровень входа
  \item[\bad]\pause нет в мейнстриме (пока?)
  \item[\good]\pause полезны не только в качестве спецификации
  \end{itemize}

\item\pause Они вместе, как это ни удивительно, работают
  \vspace{-.5\parskip}
  \begin{itemize}
  \setlength\itemsep{-.5\parskip}
  \item[\good]\pause позволяют тестировать нетестируемое
  \item[\bad]\pause инструментальная поддержка на зачаточном уровне
  \item[\bad]\pause методы спецификации ещё не отработаны
  \item[\bad]\pause есть проблемы со скоростью работы
  \item[\good]\pause мы только в начале пути
  \end{itemize}

\end{itemize}

## \only<1>{Если стало интересно}\only<2>{Спасибо!}

::: {=latex}
\hspace*{-.5cm}
\begin{tikzpicture}

\node (presentation) [label={Эта презентация}] at (0, 0) {
  \qrcode[hyperlink, height=3cm]%
    {https://github.com/buzden/slides-of-lectures/blob/master/2024.10.17-test-untestable-well-still-staying-sane.heisenbug.pdf}
};
\node (code) [label={Код со слайдов}, right = 7.85cm of presentation] {
  \qrcode[hyperlink, height=3cm]{https://github.com/buzden/code-for-lectures/tree/master/2024.10.17-test-untestable-well-still-staying-sane}
};
\node (dtc) [label={DepTyCheck, примеры}, below right = -1cm and 2.3cm of presentation] {
  \qrcode[hyperlink, height=3cm]{https://github.com/buzden/deptycheck/tree/master/examples}
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

<!-- idris
-- Just to make this be runnable
main : IO ()
main = main_pbt_insert
-->
