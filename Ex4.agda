module Ex4 where

{- I'm sorry I haven't quite finished setting this exercise yet, but by
   the joy of version control, the rest of it can be merged in later
   (quite soon). At least you can get cracking: I promise not to break
   anything, just to add a bit more on the end.

   The deadline for this is midnight on the Monday of Week 12 (15 Dec).
   It'd be good to get the marks in before Christmas, but if the end of
   term is looking deadlinetastic, please open negotiations.
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
WriteR .closed (openWrite fileName)  = WriteState  -- we get told whether it worked
WriteR .opened (writeChar x)         = One  -- always works
WriteR .opened closeWrite            = One  -- always works

{- 4.1 Implement the following operation which determines the next
   state. You should ensure that you can write characters only to
   a successfully opened file, and that you can write as many as
   you want. It should also be possible to insist that a process
   closes its file. -}

writeNext : (j : WriteState)(c : WriteC j) -> WriteR j c -> WriteState
writeNext j c r = {!!}

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

{- 4.2 Finish the READ implementation, in accordance with the description. -}

-- Commands
data ReadC : ReadState -> Set where
  openRead    : {- your stuff -} ReadC {!!}   -- needs a filename; might not open successfully;
                                              -- might open an empty file
  readChar    : {- your stuff -} ReadC {!!}   -- makes sense only if we're not at end of file
                                              -- and might take us to end of file
  closeRead   : {- your stuff -} ReadC {!!}   -- makes sense only if the file is open

-- Responses
ReadR : (j : ReadState)(c : ReadC j) -> Set
ReadR j c = {!!}

-- next State; you need to make sure the response gives enough info
readNext : (j : ReadState)(c : ReadC j) -> ReadR j c -> ReadState
readNext j c r = {!!}


---------------------------------------------------------------------------
-- COMBINING TWO INTERFACES WITH SHARED STATE
---------------------------------------------------------------------------

{- 4.3 Let's suppose we have two command-response interfaces which offer
       different functionality for the same system. Correspondingly, we'll
       have two indexed containers for the same index set. Show that you
       can combine them into one indexed container which lets you choose a
       command from either menu and evolves the state as specified by
       whichever interface offered the chosen command.
-}

_=+=_ : {I : Set} -> I => I -> I => I -> I => I
CRn0 =+= CRn1 = {!!}

---------------------------------------------------------------------------
-- WHEN IGNORANCE IS BLISS, BIS
---------------------------------------------------------------------------

{- 4.4 If we have a command-response interface with index I representing
       states of the system, show that we can index basically the same
       commands and responses over a state, I /*/ J, where the J is just
       useless information which never changes. (This operation isn't
       super-useful on its own, but it's handy in combination with other
       things. -}

GrowR : {I J : Set} -> I => I -> (I /*/ J) => (I /*/ J)
GrowR CRn = {!!}

-- do the same for "growing the index on the left"

GrowL : {I J : Set} -> I => I -> (J /*/ I) => (J /*/ I)
GrowL CRn = {!!}


---------------------------------------------------------------------------
-- COMBINING TWO INTERFACES WITH SEPARATE STATE
---------------------------------------------------------------------------

{- 4.5 Making use of 4.4 and 4.5, show how to combine two interfaces which
       operate independently on separate state: commands from one should
       not affect the state of the other.
-}

_<+>_ : {I0 I1 : Set} -> I0 => I0 -> I1 => I1 -> (I0 /*/ I1) => (I0 /*/ I1)
CRn0 <+> CRn1 = {!!}


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
       file. This goes in two phases.
-}

{- 4.6.1 Firstly, you should identify the command-reponse interface within
   which you need to work. You will need to be able to read and write files,
   but also to signal errors (in case a file fails to open for some reason).
   You must ensure that it is impossible for any process using your interface
   to escape with an error leaving a file open. You must also make it
   possible to guarantee that your copying process will, error or not, leave
   all files closed.
-}

CPState : Set
CPState = {!!}

CPInterface : CPState => CPState
CPInterface = {!!}

{- 4.6.2 Secondly, you should implement your copying process, working to your
   interface. I will let you switch off the termination checker: you cannot
   predict in advance how long the copying process will go on, as you have
   not seen the source file yet. (Later, we'll learn how to be honest about
   things which might go on for ever, but for now, let's cheat.)
-}
{-# NO_TERMINATION_CHECK #-}

cp : (sourceFile targetFile : String) -> Game CPInterface {!!} {!!}
cp sourceFile targetFile = {!!}

{- HINTS
  You will certainly need to build some extra bits and pieces.

  You have the components for reading, writing and error handling, and
  suitable kit with which to combine them. Reading and writing don't
  interfere with each other, but it's important to make sure that you
  can't bomb out with an error, so some shared state seems important.

  There are really two phases to the process:
    (1) getting the files open  -- this may go wrong
    (2) copying from one to the other  -- this will work if we reach it
  You might want to split these phases apart.
-}

---------------------------------------------------------------
-- TO BE CONTINUED...
---------------------------------------------------------------
