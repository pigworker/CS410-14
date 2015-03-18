module Ex4Sol where

{- Mark Scheme
   as indicated, below, totalling 15
-}

open import Ex1Prelude
open import IxCon

{-# BUILTIN BOOL Two #-}
{-# BUILTIN TRUE tt #-}
{-# BUILTIN FALSE ff #-}
{-# BUILTIN LIST List #-}
{-# BUILTIN NIL [] #-}
{-# BUILTIN CONS _:>_ #-}

postulate -- this means that we just suppose the following things exist...
  Char : Set
  String : Set
{-# BUILTIN CHAR Char #-}
{-# BUILTIN STRING String #-}

primitive -- these are baked in; they even work!
  primCharEquality : Char -> Char -> Two
  primStringAppend : String -> String -> String
  primStringToList : String -> List Char
  primStringFromList : List Char -> String

---------------------------------------------------------------------------
-- WRITING FILES, AN INTERFACE
---------------------------------------------------------------------------

{- If you possess the ability to open a file for writing, you might
   have the following interface. -}

-- States
data WriteState : Set where
  opened closed : WriteState  -- do you currently have a file open or not?

-- Commands
data WriteC : WriteState -> Set where
  openWrite   : (fileName : String)  -> WriteC closed
  writeChar   : Char                 -> WriteC opened
  closeWrite  :                         WriteC opened

-- Responses
WriteR : (j : WriteState)(c : WriteC j) -> Set
WriteR .closed (openWrite fileName)  = WriteState
WriteR .opened (writeChar x)         = One
WriteR .opened closeWrite            = One

{- 4.1 Implement the following operation which determines the next
   state. You should ensure that you can write characters only to
   a successfully opened file, and that you can write as many as
   you want. It should also be possible to insist that a process
   closes its file. (1 mark) -}

{-
writeNext : (j : WriteState)(c : WriteC j) -> WriteR j c -> WriteState
writeNext j c r = {!!}
-}
writeNext : (j : WriteState)(c : WriteC j) -> WriteR j c -> WriteState
writeNext ._ (openWrite fileName) j = j
writeNext .opened (writeChar x) r = opened
writeNext .opened closeWrite r = closed

-- the file writing interface, assembled as an indexed container
WRITE : WriteState => WriteState
WRITE = WriteC <! WriteR / writeNext


---------------------------------------------------------------------------
-- READING FILES, AN INTERFACE
---------------------------------------------------------------------------

{- To read from a file, it should be open, and you shouldn't be at the
   end of it. -}

-- States
data ReadState : Set where
  opened : (eof : Two) -> ReadState    -- eof is tt if we're at end of file
  closed : ReadState

{- 4.2 Finish the READ implementation, in accordance with the description.
   (3 marks, for commands, responses and next)  -}

{-
-- Commands
data ReadC : ReadState -> Set where
  openRead    : {- your stuff -} ReadC {!!}   -- needs a filename; might not open successfully;
                                              -- might open an empty file
  readChar    : {- your stuff -} ReadC {!!}   -- makes sense only if we're not at end of file
                                              -- and might take us to end of file
  closeRead   : {- your stuff -} ReadC {!!}   -- makes sense only if the file is open
                                              -- but you should not be forced to read the whole file

-- Responses
ReadR : (j : ReadState)(c : ReadC j) -> Set
ReadR j c = {!!}

-- next State; you need to make sure the response gives enough info
readNext : (j : ReadState)(c : ReadC j) -> ReadR j c -> ReadState
readNext j c r = {!!}
-}
-- Commands
data ReadC : ReadState -> Set where
  openRead    : String -> ReadC closed   -- needs a filename; might not open successfully;
                                              -- might open an empty file
  readChar    : ReadC (opened ff)   -- makes sense only if we're not at end of file
                                              -- and might take us to end of file
  closeRead   : {b : Two} -> ReadC (opened b)   -- makes sense only if the file is open

-- Responses
ReadR : (j : ReadState)(c : ReadC j) -> Set
ReadR .closed (openRead x) = ReadState
ReadR .(opened ff) readChar = Char /*/ Two
ReadR ._ closeRead = One

-- next State; you need to make sure the resonse gives enough info
readNext : (j : ReadState)(c : ReadC j) -> ReadR j c -> ReadState
readNext .closed (openRead x) s = s
readNext .(opened ff) readChar (c , b) = opened b
readNext ._ closeRead r = closed

-- the file reading interface, assembled as an indexed container
READ : ReadState => ReadState
READ = ReadC <! ReadR / readNext


---------------------------------------------------------------------------
-- COMBINING TWO INTERFACES WITH SHARED STATE
---------------------------------------------------------------------------

{- 4.3 Let's suppose we have two command-response interfaces which offer
       different functionality for the same system. Correspondingly, we'll
       have two indexed containers for the same index set. Show that you
       can combine them into one indexed container which lets you choose a
       command from either menu and evolves the state as specified by
       whichever interface offered the chosen command.
       (2 marks, one for commands, one for the rest)
-}

_=+=_ : {I : Set} -> I => I -> I => I -> I => I
(C0 <! R0 / n0) =+= (C1 <! R1 / n1)
  =   (\ i -> C0 i /+/ C1 i)
  <!  (\ { i (inl c0) -> R0 i c0 ; i (inr c1) -> R1 i c1 })
  /   (\ { i (inl c0) r0 -> n0 i c0 r0 ; i (inr c1) r1 -> n1 i c1 r1 })


---------------------------------------------------------------------------
-- WHEN IGNORANCE IS BLISS, BIS
---------------------------------------------------------------------------

{- 4.4 If we have a command-response interface with index I representing
       states of the system, show that we can index basically the same
       commands and responses over a state, I /*/ J, where the J is just
       useless information which never changes. (This operation isn't
       super-useful on its own, but it's handy in combination with other
       things. (2 marks; half each for C, R, n, half for deploying
       symmetry) -}

GrowR : {I J : Set} -> I => I -> (I /*/ J) => (I /*/ J)
GrowR (C <! R / n)
  =  (\ { (i , j) -> C i })
  <! (\ { (i , j) c -> R i c })
  /  (\ { (i , j) c r -> n i c r , j })

-- do the same for "growing the index on the left"

GrowL : {I J : Set} -> I => I -> (J /*/ I) => (J /*/ I)
GrowL (C <! R / n)
  =  (\ { (j , i) -> C i })
  <! (\ { (j , i) c -> R i c })
  /  (\ { (j , i) c r -> j , n i c r })


---------------------------------------------------------------------------
-- COMBINING TWO INTERFACES WITH SEPARATE STATE
---------------------------------------------------------------------------

{- 4.5 Making use of 4.4 and 4.5, show how to combine two interfaces which
       operate independently on separate state: commands from one should
       not affect the state of the other. (1 mark)
-}

{-
_<+>_ : {I0 I1 : Set} -> I0 => I0 -> I1 => I1 -> (I0 /*/ I1) => (I0 /*/ I1)
C0 <+> C1 = {!!}
-}

_<+>_ : {I0 I1 : Set} -> I0 => I0 -> I1 => I1 -> (I0 /*/ I1) => (I0 /*/ I1)
C0 <+> C1 = GrowR C0 =+= GrowL C1


---------------------------------------------------------------------------
-- ERROR REPORTING, AN INTERFACE
---------------------------------------------------------------------------

{- I'm building the next bit for you.

   When things go wrong, we need to trigger an error condition and abort
   mission. However, if we have other stuff going on (open files, etc),
   it may not always be ok to drop everything and run away. There will
   be some states in which it is safe to escape (and deliver a suitable
   error message, perhaps) and other states in which escape should be
   impossible.

   If it is safe to issue an error message, we should be able to do so
   without fear of any response from the environment that would oblige
   us to carry on.
-}

data ErrorC {I : Set}(SafeMessage : I -> Set)(i : I) : Set where
  error : SafeMessage i -> ErrorC SafeMessage i
    -- the SafeMessage parameter tells us what is an acceptable
    -- error message in any given state; in states where this gives
    -- Zero, it will be impossible to trigger an error!

ErrorR : {I : Set}{SafeMessage : I -> Set}(i : I)(c : ErrorC SafeMessage i) -> Set
ErrorR _ _ = Zero  -- there's no comeback

errorNext : {I : Set}{SafeMessage : I -> Set}
            (i : I)(c : ErrorC SafeMessage i) -> ErrorR i c -> I
errorNext i c ()  -- so we don't have to say how the state will evolve

ERROR : {I : Set}(SafeMessage : I -> Set) -> I => I
ERROR SafeMessage = ErrorC SafeMessage <! ErrorR / errorNext


---------------------------------------------------------------------------
-- COPY A FILE
---------------------------------------------------------------------------

{- 4.6 Implement a process which, given access to suitable interfaces, will
       give the process for copying a named source file to a named target
       file. You should:
         (1) construct the appropriate combination of interfaces
         (2) ensure that errors are appropriately signalled, including the
               text of any relevant filenames
         (3) ensure that all files are guaranteed by typechecking to be closed,
               whether or not there is an error
         (4) buffer as little data in memory as possible (so write early,
               write often)
-}

IndexCP : Set
IndexCP = (ReadState /*/ WriteState)

BothClosed : IndexCP -> Set
BothClosed (closed , closed) = String
BothClosed _ = Zero

InterfaceCP : IndexCP => IndexCP  -- (1 mark)
InterfaceCP = ERROR BothClosed =+= (READ <+> WRITE)

SuccessCP : IndexCP -> Set
SuccessCP (closed , closed) = One
SuccessCP _ = Zero

initialCP : IndexCP
initialCP = (closed , closed)

concat : List String -> String
concat [] = ""
concat (s :> ss) = primStringAppend s (concat ss)

{-# NO_TERMINATION_CHECK #-}
copyOpen : (b : Two) -> Game InterfaceCP SuccessCP (opened b , opened)
copyOpen tt = < inr (inl closeRead) , ( \ _ -> < inr (inr closeWrite) , ( \ _ -> win <> ) > ) >
copyOpen ff = < inr (inl readChar) , ( \ { (c , b) -> < inr (inr (writeChar c)) , (\ _ -> copyOpen b) > } ) >

-- (3 marks for beginning, middle, end)
cp : (sourceFile targetFile : String) -> Game InterfaceCP SuccessCP initialCP
cp sourceFile targetFile
  = < inr (inl (openRead sourceFile)) , (\
  { (opened b) ->
    < inr (inr (openWrite targetFile)) , ((\
    { opened -> copyOpen b
    ; closed -> < inr (inl closeRead) , (\ _ ->
        < inl (error (concat ("Could not open " :> targetFile :> []))) , (\ ()) >  ) >
    })) >
  ; closed -> < inl (error (concat ("Could not open " :> sourceFile :> []))) , (\ ()) > 
  }) >

-- (1 mark)
SCRIPT : {I : Set} -> I => I -> I => I
SCRIPT {I} CRn = Game CRn (\ I -> One) <! Rs / ns where
  Rs : (i : I) -> Game CRn (\ I -> One) i -> Set
  Rs i (win x) = One
  Rs i < c , k > = Sigma (Response CRn i c) \ r -> Rs (next CRn i c r) (k r)
  ns : (i : I)(cs : Game CRn (\ I -> One) i) -> Rs i cs -> I
  ns i (win x) rs = i
  ns i < c , k > (r , rs) = ns (next CRn i c r) (k r) rs

-- (1 mark)
unScript : {I : Set}(CRn : I => I){X : I -> Set}{i : I} ->
           Game (SCRIPT CRn) X i -> Game CRn X i
runScript : {I : Set}(CRn : I => I){X : I -> Set}{i : I} ->
            (cs : Command (SCRIPT CRn) i)
            (k : (rs : Response (SCRIPT CRn) i cs) ->
                   Game CRn X (next (SCRIPT CRn) i cs rs))
            -> Game CRn X i
unScript CRn (win x) = win x
unScript CRn {X}{i} < cs , k > = runScript CRn cs \ rs -> unScript CRn (k rs)

runScript CRn (win x) k = k <>
runScript CRn < c , f > k = < c , (\ r -> runScript CRn (f r) \ rs -> k (r , rs)) >

-- the rest was for fun
data Maybe (X : Set) : Set where
  yes : X -> Maybe X
  no  : Maybe X

data IOMode : Set where
  readMode writeMode appendMode readWriteMode : IOMode

postulate Handle : Set

data HaskellIOCommand (_ : One) : Set where
  hOpen : String -> IOMode -> HaskellIOCommand <>
  hClose hIsEOF hGetChar : Handle -> HaskellIOCommand <>
  hPutChar : Handle -> Char -> HaskellIOCommand <>
  hError : String -> HaskellIOCommand <>

HaskellIOResponse : (i : One) -> HaskellIOCommand i -> Set
HaskellIOResponse i (hOpen f m) = Maybe Handle
HaskellIOResponse i (hClose h) = One
HaskellIOResponse i (hIsEOF h) = Two
HaskellIOResponse i (hGetChar h) = Char
HaskellIOResponse i (hPutChar h c) = One
HaskellIOResponse i (hError e) = Zero

HASKELLIO : One => One
HASKELLIO = HaskellIOCommand <! HaskellIOResponse / _

record Driver {I J : Set}(Sync : I -> J -> Set)
              (Hi : I => I)(Lo : J => J) : Set where
  field
    hiClo :  (i : I)(j : J) -> Sync i j ->
             Command Hi i -> Command Lo j
    loRhi :  (i : I)(j : J)(s : Sync i j)(c : Command Hi i) ->
             Response Lo j (hiClo i j s c) -> Response Hi i c
    nSync :  (i : I)(j : J)(s : Sync i j)(c : Command Hi i)
             (r : Response Lo j (hiClo i j s c)) ->
             Sync (next Hi i c (loRhi i j s c r)) (next Lo j (hiClo i j s c) r)
open Driver public

RH : ReadState -> Set
RH (opened eof) = Handle
RH closed = One

WH : WriteState -> Set
WH opened = Handle
WH closed = One

hC : (i : IndexCP) (j : One) ->
     RH (outl i) /*/ WH (outr i) ->
     Command InterfaceCP i -> Command (SCRIPT HASKELLIO) j
hC (.closed , w) j (rh , wh) (inr (inl (openRead x)))
  = < hOpen x readMode , (\ { no -> win <> ;
      (yes h) -> < hIsEOF h , (\ b -> win <>) > }) >
hC (.(opened ff) , w) j (rh , wh) (inr (inl readChar))
  = < hGetChar rh , (\ c -> < hIsEOF rh , (\ b -> win <>) >) >
hC (._ , w) j (rh , wh) (inr (inl closeRead))
  = < hClose rh , (\ _ -> win <>) >
hC (r , .closed) j (rh , wh) (inr (inr (openWrite fileName)))
  = < hOpen fileName writeMode , (\ _ -> win <>) >
hC (r , .opened) j (rh , wh) (inr (inr (writeChar x)))
  = < hPutChar wh x , (\ _ -> win <>) >
hC (r , .opened) j (rh , wh) (inr (inr closeWrite))
  = < hClose wh , (\ _ -> win <>) >
hC (opened eof , opened) j (rh , wh) (inl (error ()))
hC (opened eof , closed) j (rh , wh) (inl (error ()))
hC (closed , opened) j (rh , wh) (inl (error ()))
hC (closed , closed) j (rh , wh) (inl (error e)) = < hError e , (\ ()) >
 
hR : (i : IndexCP) (j : One) (s : RH (outl i) /*/ WH (outr i))
     (c : Command InterfaceCP i) ->
     Response (SCRIPT HASKELLIO) j (hC i j s c) ->
     Response InterfaceCP i c
hR (.closed , w) j (<> , wh) (inr (inl (openRead x))) (yes rh , b , <>)
  = opened b
hR (.closed , w) j (<> , wh) (inr (inl (openRead x))) (no , <>)
  = closed
hR (.(opened ff) , w) j (rh , wh) (inr (inl readChar)) (c , b , <>) = c , b
hR (._ , w) j (rh , wh) (inr (inl closeRead)) rs = <>
hR (r , .closed) j (rh , <>) (inr (inr (openWrite fileName))) (yes wh , <>)
  = opened
hR (r , .closed) j (rh , <>) (inr (inr (openWrite fileName))) (no , <>)
  = closed
hR (r , .opened) j (rh , wh) (inr (inr (writeChar x))) rs = <>
hR (r , .opened) j (rh , wh) (inr (inr closeWrite)) rs = <>
hR (opened eof , opened) j (rh , wh) (inl (error ())) rs
hR (opened eof , closed) j (rh , wh) (inl (error ())) rs
hR (closed , opened) j (rh , wh) (inl (error ())) rs
hR (closed , closed) j (rh , wh) (inl (error x)) (() , snd)

hnS : (i : IndexCP) (j : One) (s : RH (outl i) /*/ WH (outr i))
      (c : Command InterfaceCP i)
      (r : Response (SCRIPT HASKELLIO) j (hC i j s c)) ->
      RH (outl (next InterfaceCP i c (hR i j s c r))) /*/
      WH (outr (next InterfaceCP i c (hR i j s c r)))
hnS (.closed , w) j (<> , wh) (inr (inl (openRead x))) (yes rh , snd) = rh , wh
hnS (.closed , w) j (<> , wh) (inr (inl (openRead x))) (no , snd) = <> , wh
hnS (.(opened ff) , w) j (rh , wh) (inr (inl readChar)) rs = rh , wh
hnS (._ , w) j (rh , wh) (inr (inl closeRead)) rs = <> , wh
hnS (r , .closed) j (rh , <>) (inr (inr (openWrite fileName))) (yes wh , snd)
  = rh , wh
hnS (r , .closed) j (rh , <>) (inr (inr (openWrite fileName))) (no , snd) = rh , <>
hnS (r , .opened) j (rh , wh) (inr (inr (writeChar x))) rs = rh , wh
hnS (r , .opened) j (rh , wh) (inr (inr closeWrite)) rs = rh , <>
hnS (opened eof , opened) j (rh , wh) (inl (error ())) rs
hnS (opened eof , closed) j (rh , wh) (inl (error ())) rs
hnS (closed , opened) j (rh , wh) (inl (error ())) rs
hnS (closed , closed) j (rh , wh) (inl (error x)) (() , snd)

safe2unsafe : Driver {IndexCP}{One} (\ { (r , w) j -> RH r /*/ WH w })
  InterfaceCP (SCRIPT HASKELLIO)
safe2unsafe = record
  { hiClo = hC
  ; loRhi = hR
  ; nSync = hnS
  }
