module Example.Qtt.One

import Control.Linear.LIO

%default total

---------------------------------
--- File remove grant example ---
---------------------------------

namespace FileRemoveGrantExample

  data File : Type where [external]

  data RmGrant : File -> Type where [external]

  wantToRemove : (fl : File) -> IO $ Maybe $ RmGrant fl
  remove : RmGrant fl -> IO ()

  readFileFromUser : IO File

  whatever : IO Bool
  whatever = do
    fl <- readFileFromUser
    Just rm <- wantToRemove fl
      | Nothing => pure False
    remove rm
    pure True

--------------------------------
--- Handle closing liability ---
--------------------------------

namespace HandleClosingLiability

  data File : Type where [external]

  data ClosingLia : File -> Type where [external]

  openFile  : (fl : File) -> IO $ Maybe $ ClosingLia fl
  readChar  : (fl : File) -> (0 _ : ClosingLia fl) => IO Char
  closeFile : ClosingLia h -> IO ()

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

  append : (1 _ : List' a) -> (1 _ : List' a) -> List' a
  append []      ys = ys
  append (x::xs) ys = x :: append xs ys

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

    export
    runWithCreated : Params -> (1 _ : (1 _ : Resource) -> a) -> a
    runWithCreated MkParams f = f $ MkResource 4

  depend : (1 _ : Resource) -> LPair' Result Resource
  depend r = (MkResult # r)

  destroy : (1 _ : Resource) -> Unit -- Result
  destroy $ MkResource Z     = () -- MkResult
  destroy $ MkResource (S n) = () -- MkResult

  --- Usage of this simple linear interface ---

  f1 : Result
  f1 = runWithCreated MkParams \res =>
         ?foo_f1

  f2 : Result
  f2 = runWithCreated MkParams \res =>
         let (r # res') = depend res in
         ?foo_f2

  --f3 : Result
  --f3 = runWithCreated MkParams \res =>
  --       let (r # res') = depend res in
  --       let (s # res'') = depend res in
  --       ?foo_f3

  f4 : Result
  f4 = runWithCreated MkParams \res =>
         let (r # res') = depend res in
         let (s # res'') = depend res' in
         ?foo_f4

  f5 : Result
  f5 = runWithCreated MkParams \res =>
         let (r # res') = depend res in
         let _ = destroy res' in
         ?foo_f5

  --f6 : Result
  --f6 = runWithCreated MkParams \res =>
  --       let (r # res') = depend res in
  --       let _ = destroy res' in
  --       r

  --f7 : Result
  --f7 = runWithCreated MkParams \res =>
  --       let (r # res') = depend res in
  --       let z = destroy res' in
  --       r

  f8 : Result
  f8 = runWithCreated MkParams \res =>
         let (r # res') = depend res in
         let () = destroy res' in
         r

----------------------
--- Linear file IO ---
----------------------

namespace FileIO

  data FileName = MkFileName String

  data FileHandler : FileName -> Type where [external]

  withOpenFile : LinearIO io =>
                 (fn : FileName) ->
                 (success : (1 _ : FileHandler fn) -> L io ()) ->
                 (fail : L io ()) ->
                 L io ()

  closeFile : (1 _ : FileHandler fn) -> L io ()

  readLine : (1 _ : FileHandler fn) ->
             L io {use=1} $ LPair' String $ FileHandler fn
