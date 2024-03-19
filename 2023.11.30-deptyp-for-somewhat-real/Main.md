---
lang: ru-RU

author: "Денис Буздало́в"
title: "Байки от зависимых типов"
subtitle: "Типов, зависимых от зависимых типов"
date: "30 ноября 2023"

aspectratio: 1610

mainfont: "DejaVu Serif"
monofont: "Iosevka Extended:-calt;+IDRS"
#monofont: "Fira Code:+calt;+ss09;+ss03;+cv29;+cv24"
linkstyle: bold

theme: "Singapore"
colortheme: "seahorse"
section-titles: true

header-includes:
  - "\\usepackage{framed}"
  - "\\usepackage{hyperref}"
  - "\\AtBeginSection{}"
  - "\\setbeamertemplate{caption}{\\raggedright\\insertcaption\\par}"
---

# Привет

## Дисклеймеры

. . .

- Доклад всё ещё познавательно-развлекательный

. . .

- Но никакой жалости к слушателям ;-)

  . . .

  - Код почти только на Idris
  - Более сложные зависимые типы

. . .

- Заметание под ковёр деталей!

. . .

- Никакой полноты представления

<!-- idris
import Control.Monad.State.Interface

import Data.Double.Bounded
import Data.DPair
import Data.List
import Data.List.Quantifiers
import Data.List1
import Data.Vect

import Hedgehog

%default total

%hide Syntax.PreorderReasoning.Generic.infix.(...)
%hide Syntax.PreorderReasoning.infix.(...)

prefix 0 ...

(...) : a -> a
(...) = id
-->

# Mundane use

##

``` {=latex}
\begin{center}
```

![](.brady-mundane-deptyp.jpg){height=85%}

``` {=latex}
\end{center}
```

## Как так получилось?

<!-- idris
record EnvDesc where
  constructor MkEnvDesc
  name : String
  help : String
-->

``` {=latex}
\begin{uncoverenv}<3->
```

```idris
Envs : List EnvDesc
Envs = [ --  <name>          <help>
  MkEnvDesc "EDITOR"        "Editor used in REPL :e command",
  MkEnvDesc "IDRIS2_PREFIX" "Idris2 installation prefix",
  ...
  MkEnvDesc "IDRIS2_PACKAGE_PATH" "Where to look for packages",
  ...
  MkEnvDesc "NO_COLOR"      "Instruct Idris not to print color"]
```

``` {=latex}
\end{uncoverenv}
\vfill
\begin{uncoverenv}<4->
```

<!-- idris
%hide Data.Maybe.IsJust
%hide Data.Maybe.ItIsJust
-->

```idris
data IsJust : Maybe a -> Type where
  ItIsJust : IsJust (Just x)
```

``` {=latex}
\end{uncoverenv}
\vfill
\begin{uncoverenv}<2->
```

```idris
idrisGetEnv : HasIO io => (name : String) ->
  (0 known : IsJust $ find (name ==) $ (.name) <$> Envs) =>
  io (Maybe String)
```

``` {=latex}
\end{uncoverenv}
```

## Как GADT, только вкуснее

\vspace{-\fill}\vspace{\parskip}

```idris
--                        data IsJust : Maybe a -> Type where
--                          ItIsJust : IsJust (Just x)
```

. . .

\vfill


``` {=latex}
\begin{uncoverenv}<2->
```

```scala
enum IsList[A]:
  case ItIsList[A]() extends IsList[List[A]]
```

``` {=latex}
\end{uncoverenv}
\begin{uncoverenv}<4->
```

```scala
def ff[A](using li: IsList[A])(xs : A): Int =
  li match { case ItIsList() => xs.length }
```

``` {=latex}
\end{uncoverenv}
\vfill
\begin{uncoverenv}<3->
```

```idris
data IsList : Type -> Type where
  ItIsList : IsList $ List a
```

``` {=latex}
\end{uncoverenv}
\begin{uncoverenv}<5->
```

```idris
ff : IsList a => a -> Nat
ff @{ItIsList} xs = length xs
```

``` {=latex}
\end{uncoverenv}
```

## Безопасное использование

. . .

\vspace{-\fill}\vspace{\parskip}

```idris
--       idrisGetEnv : HasIO io => (name : String) ->
--         (0 _ : IsJust $ find (name ==) $ (.name) <$> Envs) =>
--         io (Maybe String)
```

\vfill

. . .

<!-- idris
etc : Applicative f => f ()
etc = pure ()

more : Unit
more = ()

interface Something a where
  something : a

Applicative f => Something (f ()) where
  something = pure ()
Something b => Something (a -> b) where
  something = \_ => something

Conf : Type

setEditor, addPackageDir : MonadState Conf io => String -> io ()
splitPaths : String -> List1 String
-->

``` {=latex}
\begin{onlyenv}<3>
```

<!-- idris
namespace PartialUpdateEnv {
-->

```idris
updateEnv : MonadState Conf io => HasIO io => io ()
updateEnv = do
  ... something
  bpath <- idrisGetEnv "EDITOR"
  whenJust bpath setEditor
  ... something more


  ... etc
```

<!-- idris
 }
-->

``` {=latex}
\end{onlyenv}
\begin{onlyenv}<4->
```

```idris
updateEnv : MonadState Conf io => HasIO io => io ()
updateEnv = do
  ... something
  bpath <- idrisGetEnv "EDITOR"
  whenJust bpath setEditor
  ... something more
  pdirs <- idrisGetEnv "IDRIS2_PACKAGE_PATH"
  whenJust pdirs $ traverse_ addPackageDir . splitPaths
  ... etc
```

``` {=latex}
\end{onlyenv}
```

# Отступление: PBT

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

## \only<-8>{Property-based testing}\only<9->{А что, если \texttt{reverse = id}?}

. . .

``` {=latex}
\begin{uncoverenv}<4->
```

```idris
nonNegative : Gen Double
```

``` {=latex}
\end{uncoverenv}
```

<!-- idris
nonNegative = double $ exponential 0 MaxDouble

infix 0 =~=

(=~=) : Monad m => Double -> Double -> TestT m ()
x =~= y = diff x epsEq y where
  epsEq : Double -> Double -> Bool
  epsEq x y = abs (x - y) <= max x y * 10.0e-8
-->

``` {=latex}
\begin{onlyenv}<-2>
```

<!-- idris
namespace WeakSqrtProp {
export
-->

```idris
sqrtOk : Property
sqrtOk = property $ do
  sqrt 4.0 === 2.0
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
namespace WeakSqrtPropExtendedHoly {
-->

```idris
sqrtOk : Property
sqrtOk = property $ do
  x <- forAll ?gen
```

<!-- idris
  let _ = the Double x
-->
\vspace{-\parskip}

```idris
  sqrt 4.0 === 2.0
```

<!-- idris
 }
-->

``` {=latex}
\end{onlyenv}
\begin{onlyenv}<5>
```

<!-- idris
namespace WeakSqrtPropExtended {
-->

```idris
sqrtOk : Property
sqrtOk = property $ do
  x <- forAll nonNegative
  sqrt 4.0 === 2.0
```

<!-- idris
 }
-->

``` {=latex}
\end{onlyenv}
\begin{onlyenv}<6>
```

<!-- idris
namespace HolySqrtProp {
-->

```idris
sqrtOk : Property
sqrtOk = property $ do
  x <- forAll nonNegative
  sqrt x   === ?what
```

<!-- idris
 }
-->

``` {=latex}
\end{onlyenv}
\begin{onlyenv}<7->
```

<!-- idris
namespace NiceSqrtProp {
export
-->

```idris
sqrtOk : Property
sqrtOk = property $ do
  x <- forAll nonNegative
  sqrt x * sqrt x =~= x
```

<!-- idris
 }
-->

``` {=latex}
\end{onlyenv}
```

\pause\pause\pause\pause\pause\pause
\vfill

<!-- idris
someNat : Gen Nat
someNat = nat $ linear 0 9
-->

```idris
someList : Gen $ List Nat
```
<!-- idris
someList = list (exponential 0 100000) someNat
-->

<!--
%hide Prelude.List.reverse

reverse : List a -> List a
reverse = id
-->

```idris
reverseAndConcat : Property
reverseAndConcat = property $ do
  (xs, ys) <- [| (forAll someList, forAll someList) |]
  reverse xs ++ reverse ys === reverse (ys ++ xs)
```

<!-- idris
main : IO ()
main = test
  [ "double" `MkGroup`
    [ ("weak sqrtOk", WeakSqrtProp.sqrtOk)
    , ("nice sqrtOk", NiceSqrtProp.sqrtOk)
    ]
  , "list" `MkGroup`
    [ ("reverseAndConcat", reverseAndConcat)
    ]
  ]
-->

## А что, если `reverse = id`?

``` {=latex}
\begin{center}
```

![](.bug-revealed-by-hedgehog.png){height=100%}

``` {=latex}
\end{center}
```

## \only<1>{Не только функции}\only<2->{Пример: системы с состоянием, базы данных}

\pause\pause

```idris
data DBQuery : Type -> Type where
  NewTable : String ->                DBQuery Unit
  Insert   : String -> List String -> DBQuery Unit
  Lookup   : String ->                DBQuery $ List String
```

. . .

<!-- idris
Show (Exists $ DBQuery)
-->

```idris
query : Gen $ Exists DBQuery
```

. . .

\vfill

<!-- idris
DBQuery res => Eq res
DBQuery res => Show res
-->

```idris
interface StMachine st where
  doStep : DBQuery res -> st -> (st, res)
```

. . .

\vfill

<!-- idris
data ModelState : Type
data RealState  : Type
-->

```idris
StMachine ModelState where
  doStep q s = ?expected_behaviour
```

```idris
StMachine RealState where
  doStep q s = ?call_to_real_db
```

## Пример: системы с состоянием, базы данных

<!-- idris
querySizeRange : Hedgehog.Range Nat
querySizeRange = exponential 0 1000
-->

```idris
conformSeq : (tr1 : StMachine st1) -> (init1 : st1) ->
             (tr2 : StMachine st2) -> (init2 : st2) -> Property
```

. . .

\vspace{-\parskip}

```idris
conformSeq tr1 init1 tr2 init2 = property $ do
  qs <- forAll $ list querySizeRange query
```

. . .

\vspace{-\parskip}

```idris
  conformQs qs init1 init2
  where
    conformQs : List (Exists DBQuery) ->
                st1 -> st2 -> PropertyT ()
```

. . .

\vspace{-\parskip}

```idris
    conformQs []                 _  _  = success
```

. . .

\vspace{-\parskip}

```idris
    conformQs (Evidence _ q::qs) s1 s2 = do
      let (s1', res1) = doStep @{tr1} q s1
      let (s2', res2) = doStep @{tr2} q s2
```

. . .

\vspace{-\parskip}

```idris
      res1 === res2
```

. . .

\vspace{-\parskip}

```idris
      conformQs qs s1' s2'
```

## Пример: системы с состоянием, базы данных

<!-- idris
thrs : Hedgehog.Range Nat
thrs = linear 0 4
-->

```idris
conformPar : (tr1 : StMachine st1) -> (init1 : st1) ->
             (tr2 : StMachine st2) -> (init2 : st2) -> Property
conformPar tr1 init1 tr2 init2 = property $ do
  prefixQs <- forAll $ list querySizeRange query
  parQs <- forAll $ list1 thrs $ list querySizeRange query
```

. . .

\vspace{-\parskip}

```idris
  conformQs prefixQs parQs init1 init2
  where
    conformQs : List (Exists DBQuery) ->
                List1 (List (Exists DBQuery)) ->
                _ -> _ -> _
```

\vspace{-\parskip}

```
    ...
```

##

``` {=latex}
\begin{center}
```

![](.john-hughes-come-on.png){height=90%}

``` {=latex}
\end{center}
```

\footnotetext[1]{https://www.youtube.com/watch?v=zi0rHwfiX1Q}

# DepTyCheck: знакомство

## Сложные входные данные

. . .

- Для компиляторов\pause , например

  - Тайпчекеры

  . . .

  - Оптимизаторы

  . . .

  - Кодогенераторы

. . .

- Для рантаймов типа JVM

  . . .

  - AOT, JIT

. . .

- Драйвера, сервисы, ...

- ...

## Зависимые типы\only<1>{?}\uncover<2->{! Помните?}\only<2->{\phantom{?}}

. . .

```idris
data SortedBinTree : Type -> Type
data All : (a -> Bool) -> SortedBinTree a -> Type

data SortedBinTree : Type -> Type where
  Empty : SortedBinTree a
  Node  : Ord a => (x : a) -> (left, right : SortedBinTree a) ->
          All (< x) left => All (x <) right => SortedBinTree a

data All : (a -> Bool) -> SortedBinTree a -> Type where
  Empty' : All prop Empty
  Node'  : (o : Ord a) => {0 prop : a -> Bool} ->
           {0 pl : All (< x) l} -> {0 pr : All (x <) r} ->
           So (prop x) -> All prop l -> All prop r ->
           All prop $ Node x l r @{o} @{pl} @{pr}
```

<!-- idris
%hide Main.All
-->

## Зависимые типы + property-based testing

- Зависимые типы для формирования сложных входных данных

. . .

- Описать тип так, чтобы любое значение подходило

. . .

- Возможность автоматической деривации генератора

. . .

- ...

- Profit!

## Пример: очень маленький язык

<!-- idris
0 (.found) : IsJust {a} x -> a
(.found) $ ItIsJust {x} = x

Name : Type
Name = String

record FunSig
data Expr : (funs : List (Name, FunSig)) -> (vars : List (Name, Type)) -> Type -> Type

infix 2 #=
-->

```idris
data Stmts : (funs  : List (Name, FunSig)) ->
             (preV  : List (Name, Type)) ->
             (postV : List (Name, Type)) -> Type where
```

. . .

``` {=latex}
\begin{uncoverenv}<3->
```

```idris
  (.)  : (ty : Type) -> (n : Name) ->
         Stmts funs vars ((n, ty)::vars)
```

``` {=latex}
\end{uncoverenv}
\begin{uncoverenv}<4->
\begin{onlyenv}<-4>
```

``` {.idris}
  (#=) : (n : Name) ->
         (v : Expr funs vars ?expr_ty) ->
         Stmts funs vars vars
```

``` {=latex}
\end{onlyenv}
\begin{onlyenv}<5->
```

```idris
  (#=) : (n : Name) -> (0 lk : IsJust $ lookup n vars) =>
         (v : Expr funs vars lk.found) ->
         Stmts funs vars vars
```

``` {=latex}
\end{onlyenv}
\end{uncoverenv}
\begin{uncoverenv}<6->
```

```idris
  If   : (cond : Expr funs vars Bool) ->
         Stmts funs vars vThen -> Stmts funs vars vElse ->
         Stmts funs vars vars
```

``` {=latex}
\end{uncoverenv}
\begin{uncoverenv}<2->
```

```idris
  (>>) : Stmts funs preV midV  -> Stmts funs midV postV ->
         Stmts funs preV postV
```

``` {=latex}
\end{uncoverenv}
```

## Пример: очень маленький язык

``` {=latex}
\begin{uncoverenv}<4->
```

<!-- idris
infix 1 ==>
-->

```idris
record FunSig where
  constructor (==>)
  From : List Type
  To   : Type
```

``` {=latex}
\end{uncoverenv}
\vfill
```

<!-- idris
%default covering -- actually, all is total, but I don't want to bother with `assert_total` in types
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
  V : (n : Name) -> (0 lk : IsJust $ lookup n vars) =>
      Expr funs vars lk.found
```

\pause\pause

```idris
  F : (n : Name) -> (0 lk : IsJust $ lookup n funs) =>
      All (Expr funs vars) lk.found.From ->
      Expr funs vars lk.found.To
```

## Пример: очень маленький язык

\vspace{-\fill}

``` {=latex}
\begin{uncoverenv}<3->
\begin{small}
```

<!-- idris
namespace AlignHack
                              public export
-->

```idris
                              StdF : List (Name, FunSig)
                              StdF = [ ("+" , [Int, Int] ==> Int)
                                     , ("<" , [Int, Int] ==> Bool)
                                     , ("++", [Int] ==> Int)
                                     , ("||", [Bool, Bool] ==> Bool) ]
```

``` {=latex}
\end{small}
\end{uncoverenv}
```

\vspace{-4\parskip} <!-- magic skills in slide alignment O_O -->

``` {=latex}
\begin{onlyenv}<-3>
```

``` {.idris}
program : Stmts [] [] ?
```

``` {=latex}
\end{onlyenv}
\begin{onlyenv}<4->
```

```idris
program : Stmts StdF [] ?
```

``` {=latex}
\end{onlyenv}
```

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

``` {=latex}
\begin{onlyenv}<-6>
```

``` {.idris}
     ?then_branch
     ?else_branch
```

``` {=latex}
\vspace{-2\parskip}\phantom{\texttt{Bool}}\par\phantom{\texttt{Bool}}
\end{onlyenv}
\begin{onlyenv}<7>
```

``` {.idris}
     (do "y" #= C 0; "res" #= C False)
     ?else_branch
```

``` {=latex}
\vspace{-2\parskip}
\phantom{\texttt{code}}\par\phantom{\texttt{code}}
\end{onlyenv}
\begin{onlyenv}<8->
```

```idris
     (do "y" #= C 0; "res" #= C False)
     (do Int. "z"; "z" #= F "+" [V "x", V "y"]
         Bool. "b"; "b" #= F "<" [V "x", C 5]
         "res" #= F "||" [V "b", F "<" [V "z", C 6]])
```

``` {=latex}
\end{onlyenv}
```

\vfill

## Пример: очень маленький язык

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

## Пример: очень маленький язык

```idris
failing "Can't find an implementation for IsJust"
  bad : Stmts StdF [] ?
  bad = do
    Int. "x"; "x" #= C 5
    "z" #= V "x"
```

. . .

\vfill

```idris
failing "Can't find an implementation for IsJust"
  bad : Stmts StdF [] ?
  bad = do
    Int. "x"
    "x" #= V "z"
```

# DepTyCheck: жизнь

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

  - ~330 строк кода, аналогичного `Stmts` и `Expr` + обвязка

  . . .

  - Частично деривированные, частично рукописные генераторы

## Пример из жизни

``` {=latex}
\begin{onlyenv}<-8>
\begin{center}
\Large{\texttt{Testing\uncover<2-4,6-8>{.\uncover<3-4,7-8>{.\uncover<4,8>{.}}}}}
\end{center}
\end{onlyenv}

\begin{onlyenv}<9->

\vfill

\begin{uncoverenv}<10->
\begin{center}
\vspace{-4.5\parskip}
\hspace{-5mm}
\includegraphics[height=.65\textheight]{.bloody-mess.png}
\end{center}
\vspace{-.65\textheight}
\vspace{4.5\parskip}
\hspace{5mm}
\end{uncoverenv}
```

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

``` {=latex}
\vfill
\begin{uncoverenv}<11->
\begin{center}
\Large{\texttt{Shrinking\footnote<11->{пока вручную или внешним инструментом}\uncover<12-14,16-18>{.\uncover<13-14,17-18>{.\uncover<14,18>{.}}}}}
\end{center}
\end{uncoverenv}
\end{onlyenv}
```

## Пример из жизни

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

## Пример из жизни

``` {=latex}
\begin{onlyenv}<-8>
\begin{center}
\Large{\texttt{Testing\uncover<2-4,6-8>{.\uncover<3-4,7-8>{.\uncover<4,8>{.}}}}}
\end{center}
\end{onlyenv}

\begin{onlyenv}<9->
```

\vfill

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

``` {=latex}
\vfill
\begin{uncoverenv}<10->
\begin{center}
\Large{\texttt{Shrinking\uncover<11-13,15-17>{.\uncover<12-13,16-17>{.\uncover<13,17>{.}}}}}
\end{center}
\end{uncoverenv}
\end{onlyenv}
```

## Пример из жизни

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

## Пример из жизни

``` {=latex}
\begin{onlyenv}<-8>
\begin{center}
\Large{\texttt{Testing\uncover<2-4,6-8>{.\uncover<3-4,7-8>{.\uncover<4,8>{.}}}}}
\end{center}
\end{onlyenv}

\begin{onlyenv}<9->
```

\vfill

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

``` {=latex}
\vfill
\begin{uncoverenv}<10->
\begin{center}
\Large{\texttt{Shrinking\uncover<11-13,15-17>{.\uncover<12-13,16-17>{.\uncover<13,17>{.}}}}}
\end{center}
\end{uncoverenv}
\end{onlyenv}
```

## Пример из жизни

::: columns

:::: {.column width=35%}

```typescript
class C0 {
  x0: boolean

  f() : string {
    return ""
  }
}
```

::::

:::: {.column width=65%}

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

::::

:::

## Выводы

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

# Напоследок

## \only<1>{Если стало интересно}\only<2>{Спасибо!}

::: columns

:::: column

``` {=latex}
\begin{center}
```

![](.qr/idris-code-qr.png){ width=35% }

Код со слайдов

``` {=latex}
\end{center}
```

::::

:::: column

``` {=latex}
\begin{center}
```

![](.qr/idris-qr.png){ width=35% }

Idris 2 language

``` {=latex}
\end{center}
```

::::

:::

\vfill

::: columns

:::: column

``` {=latex}
\begin{center}
```

![](.qr/deptycheck-qr.png){ width=35% }

DepTyCheck

``` {=latex}
\end{center}
```

::::

:::: column

``` {=latex}
\begin{center}
```

![](.qr/slides-qr.png){ width=35% }

Эта презентация

``` {=latex}
\end{center}
```

::::

:::

\vfill

. . .

\centering{\Large{Вопросы?}}

