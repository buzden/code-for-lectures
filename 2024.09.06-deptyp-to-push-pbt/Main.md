---
lang: en-EN

author: "Denis Buzdalov"
title: "Dependent Types to Push Corners of the Property-based Testing"
date: "ICFP, TyDe Workshop\\newline\\vspace{-.8\\baselineskip}\\newline 6 September 2024\\newline\\vspace{-.8\\baselineskip}\\newline Milan, Italy"

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
  \usepackage[overlay]{textpos}
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

---

# Intro

## I hope you'll agree that

<!-- idris
import Data.Fin
import Data.List
import Data.List.Quantifiers
import Data.Maybe

import Deriving.DepTyCheck.Gen

import Hedgehog

%default total
-->

<!-- idris
namespace IndentAlignment
-->

- Dependent types are cool

\vspace{-1.5\parskip}

::: small
```idris
    data AtIndex : Fin n -> Vect n a -> a -> Type where
      Here  : AtIndex FZ (x :: xs) x
      There : AtIndex idx xs y -> AtIndex (FS idx) (x::xs) y
```
:::

. . .

\vspace{-2\parskip}\vfill

- Property-based testing is cool too

\vspace{-1.5\parskip}

<!-- idris
    %hide Vect.Dependent.(<*>)
    export
-->
::: small
```idris
    indexInserted : Property
    indexInserted = property $ do
      (n, x)    <- forAll [| (nat (linear 0 100), anyInt64) |]
      (xs, idx) <- forAll [| (vect n anyInt64, fin (linearFin n)) |]
      f         <- apply <$> forAll (function anyInt32)
      insertAt idx (f x) (map f xs) === map f (insertAt idx x xs)
```
:::

<!-- idris
main : IO ()
main = test
  [ "property example" `MkGroup`
    [ ("indexInserted", indexInserted)
    ]
  ]
-->

## What does it mean to be type-driven?

. . .

- We invest in expressing the intent with types

. . .

- We get good things

  - less incorrect implementations
  - more confidence in the code
  - less unneeded code/checks
  - help from compilers and tools
  - ... \pause
  - better and more powerful tests!

## Type-driven property-based testing?\phantom{!}

\vspace{-\fill}

*Being given two sorted lists, function `merge` produces a sorted list*

. . .

\vfill

- Special generator of sorted lists for `List`{.idris}?

\vspace{-\parskip}

<!-- idris
anyList : Gen (List Nat)

namespace SortedListDirectGen
-->
::: small
```idris
   sortedList : Gen (List Nat)
   sortedList = anyList <&> foldr (\x, xs => x :: map (x+) xs) []
```
:::

. . .

- Special wrapper for sorted lists?

\vspace{-\parskip}

<!-- idris
namespace SortedListNewtypeGen
-->
::: small
```idris
   data SortedList = SL (List Nat)
   sortedList : Gen SortedList
```
:::

. . .

- Describe intent in type, derive generator!

## Type-driven property-based testing!\phantom{?}

```idris
mutual
  data SortedList : Type where
    Nil  : SortedList
    (::) : (x : Nat) -> (xs : SortedList) ->
           (0 _ : So $ canPrepend x xs) => SortedList
  canPrepend : Nat -> SortedList -> Bool
  canPrepend n = \case [] => True; x::xs => n < x
```

```idris
anySortedList : Gen SortedList -- derived complete generator
```

. . .

<!-- idris
namespace TypeDrivenMergeSorted {
-->
```idris
toList : SortedList -> List Nat
```
<!-- idris
toList [] = []
toList (x::xs) = x :: toList xs
-->

<!-- idris
Show SortedList where show = show . toList
-->

```idris
mergeSorted : Property
mergeSorted = property $ do
  (xs, ys) <- forAll [| (anySortedList, anySortedList) |]
  assert $ sorted (merge (toList xs) (toList ys))
```
<!-- idris
 }
-->

## Type-driven property-based testing!\phantom{?}

- Surely, you can still make a mistake

. . .

- ...but in a declarative specification

. . .

- Completeness and good distribution by library

. . .

- ...but fine tuning is hard

# Practicality

## Let's try

<!-- Language example, dialect of TS -->

- New language implementation

- Restricted dialect of TypeScript, static strict typing

- Interpreter + JIT; AOT compiler

. . .

- Properties

  - semantically correct programs should be successfully compilable

  . . .

  - among them, halting programs should run and be interpretable without unexpected crashes

  . . .

  - all these running modes should produce the same result

## How specification can look like

<!-- Specification example -->

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

## How specification can look like

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

## Semantically correct program

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
  If (F "<" [F "++" [V "x"], V "y"])
     (do "y" #= C 0; "res" #= C False)
     (do Int. "z"; "z" #= F "+" [V "x", V "y"]
         Bool. "b"; "b" #= F "<" [V "x", C 5]
         "res" #= F "||" [V "b", F "<" [V "z", C 6]])
```

\vfill

## Semantically incorrect programs

```idris
failing "Mismatch between: Int and Bool"
  bad : Stmts StdF [] ?
  bad = do
    Int. "x"; "x" #= C 5
    Bool. "y"; "y" #= F "+" [V "x", C 1]
```

\vfill

```idris
failing "Mismatch between: [] and [Int]"
  bad : Stmts StdF [] ?
  bad = do
    Int. "x"; "x" #= C 5
    Int. "y"; "y" #= F "+" [V "x"]
```

\vfill

```idris
failing "Mismatch between: Bool and Int"
  bad : Stmts StdF [] ?
  bad = do
    Int. "x"; "x" #= C 5
    Int. "y"; "y" #= F "+" [C True, V "x"]
```

## Actual specification

- Using DepTyCheck library

. . .

- Language subset

  - Halting programs
  - Loops, `if`s, assignments, exceptions
  - Classes without arbitrary methods, numbers, arrays

. . .

- Specification "hacks"

  - De Bruijn indices
  - "Continuation-passing style"-like data
  - Specialised polymorphic data types
  - Grouping type indices
  - ...

. . .

- ~330 LOC of specification + same for harness

. . .

- Partially derived, partially hand-written generators

## Actual specification

<!-- Found bug 1 -->

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
\begin{textblock*}{\textwidth}[.1,.45](0mm,8\parsep)
\includegraphics[height=.65\textheight]{.images/bloody-mess.png}
\end{textblock*}
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

## Actual specification

<!-- Found bug 2 (the compiler's one) -->

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

## Actual specification

<!-- Found bug 3 (the big one) -->

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

## Actual specification

- ...and so on

- 9 bugs in typechecker, JIT- and AOT-optimisers, code generator

- 8 more bugs during specification

## What we've (re)learned

<!-- We've repeated John Hughes'es outcomes -->

- Same property can find many different bugs

. . .

- Subtle bugs are in interaction of many features

. . .

- PBT can find bug that are tricky to find manually

. . .

- PBT is cool!

. . .

- Dependent types may be cool for PBT!

<!-- idris
%unhide Language.Reflection.TT.Name
-->

# Adventures of generators

## What are generators anyway?

<!-- Generators are actually inevitably functions -->

<!-- idris
namespace GeneratorsChapter {
namespace GeneratorsAreFunctions {
-->
```idris
data Fin : Nat -> Type
```
<!-- idris
%hide GeneratorsAreFunctions.Fin
-->

. . .

What's a signature for generator of `Fin`{.idris}?

. . .

```idris
finN   : (n : Nat) -> Gen (Fin n)
finAny : Gen (n ** Fin n)
```

\vfill

. . .

```idris
data LT : Nat -> Nat -> Type
```
<!-- idris
%hide GeneratorsAreFunctions.LT
-->

. . .

```idris
ltAny   : Gen (l ** r ** LT l r)
ltLeft  : (r : Nat) -> Gen (l ** LT l r)
ltRight : (l : Nat) -> Gen (r ** LT l r)
ltGiven : (l, r : Nat) -> Gen (LT l r)
```
<!-- idris
 }
-->

## Can generators be empty?

. . .

- QuickCheck says "yes", limited retry

. . .

- Idris Hedgehog says "no", disallowing even filtering

. . .

- We can't afford saying "no", recall
  ```idris
  finN : (n : Nat) -> Gen (Fin n)
  ```

. . .

- Generation spends most of the time in retrying

## Compile-time control of emptiness

<!-- idris
namespace FakeDepTyCheckGen {
%hide Test.DepTyCheck.Gen.Emptiness.Emptiness
-->
```idris
data Emptiness = NonEmpty | MaybeEmptyDeep | MaybeEmpty
data Gen : Emptiness -> Type -> Type
```
<!-- idris
  where Mk : Gen em a -- workaround of a parser bug
 }
%unhide Test.DepTyCheck.Gen.Emptiness.Emptiness
-->

. . .

\vfill

```idris
finN   : (n : Nat) -> Gen MaybeEmpty (Fin n)
finSN  : (n : Nat) -> Gen NonEmpty (Fin (S n))
finAny : Gen NonEmpty (n ** Fin n)
```

## Compile-time control of emptiness

:::: small
::: {.uncover on=2-}
```idris
data GenAlternatives : (notEmpty : Bool) -> Emptiness -> Type -> Type
```
:::
\vspace{-2.5\parskip}
::: {.uncover on=4-}
```idris
data AltsNonEmpty : Bool -> Emptiness -> Type
```
:::
::::

\vfill

<!-- idris
%hide GeneratorsChapter.GenAlternatives
%hide GeneratorsChapter.AltsNonEmpty
-->
```idris
data Gen : Emptiness -> Type -> Type where
  --- ... other stuff ... ---
  OneOf : alem `NoWeaker` em => NotImmediatelyEmpty alem =>
          GenAlternatives True alem a -> Gen em a
```
<!-- idris
%hide GeneratorsChapter.Gen
%hide GeneratorsChapter.OneOf
-->

\pause\pause

```idris
oneOf : alem `NoWeaker` em => AltsNonEmpty altsNe em =>
        GenAlternatives altsNe alem a -> Gen em a
```
<!-- idris
%hide GeneratorsChapter.oneOf
-->

\pause\pause
\vfill

```idris
g1, g2 : Gen MaybeEmpty Nat
g1 = oneOf [empty, elements [0, 1, 2], empty]
g2 = elements [0, 1, 2]
```

<!-- idris
 } -- end of the `GeneratorsChapter` namespace
-->

# Adventures of derivation

## Practical derivation

::: {.only on=2-}

- Complete

. . .

- Total

. . .

- Good distribution

. . .

<!-- idris
namespace IndentAlignment
-->
```idris
    fins : Fuel -> (n : Nat) -> Gen MaybeEmpty (List (Fin n))
```

. . .

- Whole-type derivation

. . .

<!-- idris
namespace IndentAlignment
-->
```idris
    program : Fuel -> (fs : _) -> (vs : _) ->
              Gen MaybeEmpty (vs' ** Stmts fs vs vs')
```

. . .

- Efficient

:::

## Challenges

<!-- idris
namespace DependencyChallenge {
-->

:::: small

::: {.uncover on=5-}
```idris
data X : Nat -> Nat -> Type where
  X45 : X 4 5
  X5m : X 5 m
```
:::

::: {.uncover on=4-}
```idris
data Y : Nat -> Nat -> Type where
  MkY : (n, m : _) -> Y n m
```
:::

\vfill

```idris
data Z : Type where
  Zxy : X n m -> Y n k -> Z
  Zyx : Y n m -> X n k -> Z
```

::: {.uncover on=2-}
```idris
zs : Fuel -> Gen MaybeEmpty Z
```
\vspace{-2.5\parskip} <!-- remove this line, line above and below, thus enabling derivation -->
``` {.idris}
zs = deriveGen
```
:::

::::

::::: {.uncover on=3-}
`\begin{textblock}{.4}(7.5,-11.5)`{=latex}

:::: small
```idris
genX'' : Gen0 (n ** m ** X n m)
genY' : (n:_) -> Gen0 (k ** Y n k)
genZxy : Gen0 Z
genZxy = do
  (n ** m ** x) <- genX''
  (k ** y) <- genY' n
  pure (Zxy x y)

    -- or --

genX' : (n:_) -> Gen0 (m ** X n m)
genY'' : Gen0 (n ** k ** Y n k)
genZxy' : Gen0 Z
genZxy' = do
  (n ** k ** y) <- genY''
  (m ** x) <- genX' n
  pure (Zxy x y)
```
::::

`\end{textblock}`{=latex}

:::::

<!-- idris
 } -- end of `DependencyChallenge` namespace
-->

<!-- ## Challenges -->

<!-- what is an index actually is relative to the derivation task -->

## Challenges

<!-- idris
namespace ComplexOrders {
-->

```idris
f : Nat -> Nat
```
\vspace{-\parskip}
::: {.uncover on=3-}
```idris
g : Fin n -> Fin n
```
:::

\vfill

```idris
data Yn : (n : Nat) -> Fin n     -> Type
```
\vspace{-\parskip}
::: {.uncover on=2-}
```idris
data Yf : (n : Nat) -> Fin (f n) -> Type
```
:::

\vfill

```idris
data Z : Type where
  Z1 : (x : Fin (f n)) -> Yn (f n) x -> Z   -- n, (x ** y)
```
\vspace{-\parskip}
::: {.uncover on=2-}
```idris
  Z2 : (x : Fin (f n)) -> Yf n x     -> Z   -- (n ** x ** y)
```
:::
\vspace{-\parskip}
::: {.uncover on=3-}
```idris
  Z3 : (x : Fin (f n)) -> Yf n (g x) -> Z   -- n, x, y
```
:::
\vspace{-\parskip}
::: {.uncover on=4-}
```idris
  Z4 : (x : Fin n)     -> Yn n (g x) -> Z   -- (n ** x), y
```
:::

<!-- idris
 } -- end of `ComplexOrders` namespace
-->

# The end

## \only<1>{If you're interested}\only<2->{Thank you!}

::: {=latex}
\hspace*{-.5cm}
\begin{tikzpicture}

\node (presentation) [label={This presentation}] at (0, 0) {
  \qrcode[hyperlink, height=3cm]{https://github.com/buzden/slides-of-lectures/blob/master/2024.09.06-deptyp-to-push-pbt.pdf}
};
\node (code) [label={Code from the slides}, right = 7.85cm of presentation] {
  \qrcode[hyperlink, height=3cm]{https://github.com/buzden/code-for-lectures/tree/master/2024.09.06-deptyp-to-push-pbt}
};
\node (dtc) [label={DepTyCheck, examples}, below right = -1cm and 2.3cm of presentation] {
  \qrcode[hyperlink, height=3cm]{https://github.com/buzden/deptycheck/tree/master/examples}
};

\end{tikzpicture}
:::

\vfill

. . .

::: center
:::: Large
Questions?
::::
:::

