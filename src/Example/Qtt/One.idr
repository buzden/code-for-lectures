module Example.Qtt.One

import Control.Linear.LIO

import Data.Fin
import Data.Vect

%default total

---------------------------------
--- File remove grant example ---
---------------------------------

namespace FileRemoveGrantExample

  data File : Type where [external]

  data RmGrant : File -> Type where [external]

  wantToRemove : (fl : File) -> IO $ Maybe $ RmGrant fl
  remove : RmGrant fl -> IO Unit

  readFileFromUser : IO File

  whatever : IO Bool
  whatever = do
    fl <- readFileFromUser
    Just rm <- wantToRemove fl
      | Nothing => pure False
    remove rm
    pure True

----------------------
--- Disconnect arm ---
----------------------

namespace DisconnectArmExample

  data Arm = LeftTopArm | RightTopArm

  data DisconnectGrant : Arm -> Type where [external]

  data DisResult = CantDisconnect | Disconnected

  wantDisconnect : (arm : Arm) -> IO $ Maybe $ DisconnectGrant arm
  disconnect : DisconnectGrant arm -> IO Unit

  whatever : IO DisResult
  whatever = do
    Just rm <- wantDisconnect LeftTopArm
      | Nothing => pure CantDisconnect
    disconnect rm
    pure Disconnected

--------------------------------
--- Handle closing liability ---
--------------------------------

namespace HandleClosingLiability

  data File : Type where [external]

  data ClosingLia : File -> Type where [external]

  openFile  : (fl : File) -> IO $ Maybe $ ClosingLia fl
  readChar  : (fl : File) -> (0 _ : ClosingLia fl) => IO Char
  closeFile : ClosingLia h -> IO Unit

  whatever : File -> IO $ Either String Char
  whatever fl = do
    Just cl <- openFile fl
      | Nothing => pure $ Left "Can't open"
    c <- readChar fl
    closeFile cl
    pure $ Right c

----------------------
--- First examples ---
----------------------

namespace AppendList

  data List' : Type -> Type where
    Nil  : List' a
    (::) : (1 _ : a) -> (1 _ : List' a) -> List' a

  (++) : (1 _ : List' a) -> (1 _ : List' a) -> List' a
  []      ++ ys = ys
  (x::xs) ++ ys = x :: xs ++ ys

  null : (_ : List' a) -> Bool
  null []     = True
  null (_::_) = False

-----------------------------------
--- Entering the linear context ---
-----------------------------------

namespace EnterLin

  data Params = MkParams
  data Result = MkResult

  data Resource : Type where
    [noHints]
    MkResource : (1 _ : Nat) -> Resource

  public export
  data LPair' : Type -> Type -> Type where
    (#) : a -> (1 _ : b) -> LPair' a b

  namespace ResultMark

    export
    1 create : Params -> Resource
    create MkParams = MkResource 3

  namespace WrappingFunction

    public export
    data Ur : Type -> Type where
      MkUr : a -> Ur a

    export
    runWithCreated : Params -> (1 _ : (1 _ : Resource) -> Ur a) -> a
    runWithCreated MkParams f = let MkUr x = f $ MkResource 4 in x

  depend : (1 _ : Resource) -> LPair' Result Resource
  depend r = (MkResult # r)

  destroy : (1 _ : Resource) -> Unit -- Result
  destroy $ MkResource Z     = () -- MkResult
  destroy $ MkResource (S n) = () -- MkResult

  --- Usage of this simple linear interface ---

  --x : Nat
  --x = let r = runWithCreated MkParams (\x => x)
  --     in ?foo -- resource leaks if instead of `Ur a` just `a` was used

  f1 : Result
  f1 = runWithCreated MkParams \res =>
         MkUr ?foo_f1

  f2 : Result
  f2 = runWithCreated MkParams \res =>
         let (r # res') = depend res in
         MkUr ?foo_f2

  --f3 : Result
  --f3 = runWithCreated MkParams \res =>
  --       let (r # res') = depend res in
  --       let (s # res'') = depend res in
  --       MkUr ?foo_f3

  f4 : Result
  f4 = runWithCreated MkParams \res =>
         let (r # res') = depend res in
         let (s # res'') = depend res' in
         MkUr ?foo_f4

  f5 : Result
  f5 = runWithCreated MkParams \res =>
         let (r # res') = depend res in
         let _ = destroy res' in
         MkUr ?foo_f5

  --f6 : Result
  --f6 = runWithCreated MkParams \res =>
  --       let (r # res') = depend res in
  --       let _ = destroy res' in
  --       MkUr r

  --f7 : Result
  --f7 = runWithCreated MkParams \res =>
  --       let (r # res') = depend res in
  --       let z = destroy res' in
  --       MkUr r

  f8 : Result
  f8 = runWithCreated MkParams \res =>
         let (r # res') = depend res in
         let () = destroy res' in
         MkUr r

----------------------------------------
--- Pseudo-quantity-polymorphic pair ---
----------------------------------------

namespace PseudoQuantityPolymorphic

  --data Usage = None | Linear | Unrestricted

  namespace Pair

    public export
    data Pair' : {r : Usage} -> Type -> Type -> Type where
      W0 : a -> (0 _ : b) -> Pair' {r=None}   a b
      W1 : a -> (1 _ : b) -> Pair' {r=Linear} a b
      WW : a -> b         -> Pair'            a b
      --WW : a -> b -> {default Unrestricted 0 r : Usage} -> Pair' {r} a b

    relax : Pair' {r=Unrestricted} a b -> Pair' a b
    relax (WW x y) = WW x y
    -- When `WW` is declared with a default.
    --relax : Pair' {r=Unrestricted} a b -> {0 u : Usage} -> Pair' {r=u} a b
    --relax (WW x y) = WW {r=u} x y

    (.fst) : Pair' a b -> a
    (.fst) (W0 x _) = x
    (.fst) (W1 x _) = x
    (.fst) (WW x _) = x

    0 (.snd0) : (0 _ : Pair' {r=0} a b) -> b
    (W0 _ y).snd0 = y
    (WW _ y).snd0 = y

    1 (.snd1) : (1 _ : Pair' {r=1} a b) -> b
    (.snd1) (W1 _ y) = y
    (.snd1) (WW _ y) = y

    (.sndW) : (1 _ : Pair' {r=Unrestricted} a b) -> b
    (.sndW) (WW _ y) = y

  --- Not a pair ---

  namespace SingleValue

    public export
    data V : {r : Usage} -> Type -> Type where
      V0 : (0 _ : a) -> V {r=None}   a
      V1 : (1 _ : a) -> V {r=Linear} a
      VW : a         -> V            a

    relax : V {r=Unrestricted} a -> V a
    relax (VW x) = VW x

    0 (.v0) : (0 _ : V {r=0} a) -> a
    (.v0) (V0 x) = x
    (.v0) (VW x) = x

    1 (.v1) : (1 _ : V {r=1} a) -> a
    (.v1) (V1 x) = x
    (.v1) (VW x) = x

    (.vW) : (1 _ : V {r=Unrestricted} a) -> a
    (.vW) (VW x) = x

  namespace List

    public export
    data LinOrW = Linear | W

    public export
    fromInteger : (0 x : Integer) -> (0 _ : x = 1) => LinOrW
    fromInteger 1 @{Refl} = Linear

    infixr 7 .::, ::., .::.

    data List' : {l, r : LinOrW} -> Type -> Type where
      Nil    : List' a
      (::)   : a -> List' a -> List' {l=W,r=W} a
      (.::)  : (1 _ : a) -> List' a -> List' {l=1,r=W} a
      (::.)  : a -> (1 _ : List' a) -> List' {l=W,r=1} a
      (.::.) : (1 _ : a) -> (1 _ : List' a) -> List' {l=1,r=1} a

    relax : (1 _ : List' a) -> List' {l=1,r=1} a
    relax [] = []
    relax (x  ::  y) = x .::. y
    relax (x .::  y) = x .::. y
    relax (x  ::. y) = x .::. y
    relax (x .::. y) = x .::. y

    null : (1 _ : List' {l=W,r=W} a) -> Bool
    null []     = True
    null (x::y) = False

    (++) : (1 _ : List' {l=1,r=1} a) -> (1 _ : List' {l=1,r=1} a) -> List' {l=1,r=1} a
    [] ++ ys = ys
    (x .::. xs) ++ ys = assert_total $ x .::. (relax xs ++ ys)

    f : List' a -> List' a -> List' {l=1,r=1} a
    f xs ys = relax xs ++ relax ys

  namespace List'

    data List' : {l, r : LinOrW} -> Type -> Type where
      Nil    : List' a
      (::)   : a -> List' a -> List' a
      (.::)  : (1 _ : a) -> List' a -> List' {l=1} a
      (::.)  : a -> (1 _ : List' a) -> List' {r=1} a
      (.::.) : (1 _ : a) -> (1 _ : List' a) -> List' {l=1,r=1} a

    relax : (1 _ : List' a) -> List' {l=1,r=1} a
    relax [] = []
    relax (x  ::  y) = x  ::  y
    relax (x .::  y) = x .::  y
    relax (x  ::. y) = x  ::. y
    relax (x .::. y) = x .::. y

    null : (1 _ : List' {l=W,r=W} a) -> Bool
    null []     = True
    null (x::y) = False

    (++) : (1 _ : List' {l=1,r=1} a) -> (1 _ : List' {l=1,r=1} a) -> List' {l=1,r=1} a
    [] ++ ys = ys
    (x  ::  xs) ++ ys = assert_total $ x .::. (relax xs ++ ys)
    (x .::  xs) ++ ys = assert_total $ x .::. (relax xs ++ ys)
    (x  ::. xs) ++ ys = assert_total $ x .::. (relax xs ++ ys)
    (x .::. xs) ++ ys = assert_total $ x .::. (relax xs ++ ys)

    f : List' a -> List' a -> List' {l=1,r=1} a
    f xs ys = relax xs ++ relax ys

----------------------
--- Linear file IO ---
----------------------

namespace FileIO

  data FileName = MkFileName String

  FromString FileName where
    fromString = MkFileName

  data FileHandler : FileName -> Type where [external]

  namespace ImpureIO_API

    withOpenFile : LinearIO io =>
                   (fn : FileName) ->
                   (success : (1 _ : FileHandler fn) -> L io a) ->
                   (fail : L io a) ->
                   L io a

    closeFile : LinearIO io => (1 _ : FileHandler fn) -> L io Unit

    readLine : LinearIO io =>
               (1 _ : FileHandler fn) ->
               L io {use=1} $ LPair' String $ FileHandler fn

    f : LinearIO io => L io $ Maybe Bool
    f = withOpenFile "foo" success (putStrLn "alas" *> pure Nothing) where
      success : (1 _ : FileHandler _) -> L io $ Maybe Bool
      success fh = do (str # fh) <- readLine fh
                      closeFile fh
                      pure $ Just (str == "x")

  namespace AbstractedAPI

    interface (Monad io, LinearBind io) => FilesAPI io where
      withOpenFile : (fn : FileName) ->
                     (success : (1 _ : FileHandler fn) -> L io a) ->
                     (fail : L io a) ->
                     L io a
      closeFile : (1 _ : FileHandler fn) -> L io Unit
      readLine : (1 _ : FileHandler fn) ->
                 L io {use=1} $ LPair' String $ FileHandler fn

    f : (FilesAPI io, HasLinearIO io) => L io $ Maybe Bool
    f = withOpenFile "foo" success (putStrLn "alas" *> pure Nothing) where
      success : (1 _ : FileHandler _) -> L io $ Maybe Bool
      success fh = do (str # fh) <- AbstractedAPI.readLine fh
                      closeFile fh
                      pure $ Just (str == "x")

-----------------------------
--- Simple login protocol ---
-----------------------------

namespace SimpleLoginProtocol

  data JournalState = NotYetCheckedIn | CheckedIn
  data LoginState = Initial | LoggedIn JournalState | LoggedOut

  prefix 9 @
  data (@) : LoginState -> Type where [external]

  data Key : Type where [external]
  data FailureReason = WrongKey | MalformedKey

  Show FailureReason where
    show WrongKey     = "wrong key"
    show MalformedKey = "malformed key"

  interface (Monad m, LinearBind m) => SimpleProtocol m where
    beginSession : (1 _ : (1 _ : @ Initial) -> L m a) -> L m a
    endSession   : (1 _ : @ LoggedOut) -> L m Unit

    login  : (1 _ : @ Initial) ->
             (name : String) ->
             (key : Key) ->
             L m {use=1} $ Res Bool \case
               True  => @ LoggedIn NotYetCheckedIn
               False => LPair' FailureReason (@ LoggedOut)
    logout : (1 _ : @ LoggedIn CheckedIn) -> L m {use=1} (@ LoggedOut)

    updateKey  : (1 _ : @ LoggedIn x) ->
                 (newKey : Key) ->
                 L m {use=1} $ LPair' (Maybe FailureReason) (@ LoggedIn x)
    readSecret : (1 _ : @ LoggedIn x) -> L m {use=1} $ LPair' String (@ LoggedIn x)

    checkIn : (1 _ : @ LoggedIn NotYetCheckedIn) ->
              (info : String) ->
              L m {use=1} (@ LoggedIn CheckedIn)

  denisKey : Key

  f1 : SimpleProtocol m => L m $ Either String Bool
  f1 = beginSession \p => do
         ?foo_1

  f2 : SimpleProtocol m => L m $ Either String Bool
  f2 = beginSession \p => do
         ans <- login p "Denis" denisKey
         ?foo_2

  f3 : SimpleProtocol m => L m $ Either String Bool
  f3 = beginSession \p => do
         (True # s) <- login p "Denis" denisKey
           | (False # (reason # s)) => ?foo_bad
         ?foo_good

  f4 : SimpleProtocol m => L m $ Either String Bool
  f4 = beginSession \p => do
         (True # p) <- login p "Denis" denisKey
           | (False # (reason # s)) => do
               endSession s
               pure $ Left $ show reason
         ?foo_4

  f5 : SimpleProtocol m => L m $ Either String Bool
  f5 = beginSession \p => do
         (True # p) <- login p "Denis" denisKey
           | (False # (reason # s)) => do
               endSession s
               pure $ Left $ show reason
         sec # p <- readSecret p
         ?foo_5

  --f6 : SimpleProtocol m => L m $ Either String Bool
  --f6 = beginSession \p => do
  --       (True # p) <- login p "Denis" denisKey
  --         | (False # (reason # s)) => do
  --             endSession s
  --             pure $ Left $ show reason
  --       sec # p <- readSecret p
  --       p <- logout p
  --       ?foo_6

  f7 : SimpleProtocol m => L m $ Either String Bool
  f7 = beginSession \p => do
         (True # p) <- login p "Denis" denisKey
           | (False # (reason # s)) => do
               endSession s
               pure $ Left $ show reason
         sec # p <- readSecret p
         p <- checkIn p "read secret"
         p <- logout p
         ?foo_7

  --f8 : SimpleProtocol m => L m $ Either String Bool
  --f8 = beginSession \p => do
  --       (True # p) <- login p "Denis" denisKey
  --         | (False # (reason # s)) => do
  --             endSession s
  --             pure $ Left $ show reason
  --       sec # p <- readSecret p
  --       p <- checkIn p "read secret"
  --       p <- logout p
  --       pure $ Right $ sec == "foo"

  f9 : SimpleProtocol m => L m $ Either String Bool
  f9 = beginSession \p => do
         (True # p) <- login p "Denis" denisKey
           | (False # (reason # s)) => do
               endSession s
               pure $ Left $ show reason
         sec # p <- readSecret p
         p <- checkIn p "read secret"
         p <- logout p
         endSession p
         pure $ Right $ sec == "foo"

---------------------
--- Game protocol ---
---------------------

namespace GameLocalProtocol

  -- Not done yet.

-----------------------------------------
--- Safe pure mutable data structures ---
-----------------------------------------

namespace MonadicMutalbeArrays

  interface Monad m => MArray (0 ar : Nat -> Type -> Type) m where
    new   : (n : Nat) -> a -> m (ar n a)
    read  : Fin n -> ar n a -> m a
    write : Fin n -> a -> ar n a -> m Unit

    freeze : ar n a -> m (Vect n a) -- unsafe!

  modify : MArray ar m => (a -> a) -> Fin n -> ar n a -> m Unit
  modify f i arr = do
    x <- read i arr
    write i (f x) arr

  modifyAll : MArray ar m => (a -> a) -> ar n a -> m Unit

  f : MArray ar m => Fin n -> ar n Nat -> m Nat
  f i arr = do original <- read i arr
               modify (+1) i arr
               pure original

namespace LinearMutableArrays

  data LArray : Nat -> Type -> Type where [external]

  withNew : (n : Nat) -> a -> (1 _ : (1 _ : LArray n a) -> Ur b) -> b
  read    : Fin n -> (1 _ : LArray n a) -> LPair' a $ LArray n a
  write   : Fin n -> a -> (1 _ : LArray n a) -> LArray n a

  free   : (1 _ : LArray n a) -> Unit
  freeze : (1 _ : LArray n a) -> Ur $ Vect n a

  modify : (a -> a) -> Fin n -> (1 _ : LArray n a) -> LArray n a
  modify f i arr = let x # arr = read i arr
                    in write i (f x) arr

  modifyAll : (a -> a) -> (1 _ : LArray n a) -> LArray n a

  f : Fin n -> (1 _ : LArray n Nat) -> LPair' Nat $ LArray n Nat
  f i arr = let original # arr = read i arr
                arr = modify (+1) i arr
             in original # arr
