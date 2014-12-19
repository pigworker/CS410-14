module Edit where

{- This is the file where you should work. -}

open import AgdaSetup

{- The key editor data structure is the cursor. A Cursor M X represents
   being somewhere in the middle of a sequence of X values, holding an M. -}

record Cursor (M X : Set) : Set where
  constructor _<[_]>_
  field
    beforeMe  : Bwd X
    atMe      : M
    afterMe   : List X
infix 4 _<[_]>_

{- An editor buffer is a nested cursor: we're in the middle of a bunch of
   *lines*, holding a cursor for the current line, which puts us in the
   middle of a bunch of characters, holding the element of One. -}
Buffer : Set
Buffer = Cursor (Cursor One Char) (List Char)

{- This operator, called "chips", shuffles the elements from a backward list
   on to the start of a forward list, keeping them in the same order. -}
_<>>_ : {X : Set} -> Bwd X -> List X -> List X
[]         <>> xs  = xs
(xz <: x)  <>> xs  = xz <>> (x :> xs)

{- The "fish" operator goes the other way. -}
_<><_ : {X : Set} -> Bwd X -> List X -> Bwd X
xz <>< []         = xz
xz <>< (x :> xs)  = (xz <: x) <>< xs

{- You can turn a buffer into a list of lines, preserving its text. -}
bufText : Buffer -> List (List Char)
bufText
  (sz <[
   cz <[ <> ]> cs
   ]> ss)
  = sz <>> ((cz <>> cs) :> ss)

{- Here's an example of a proof of a fact about fish and chips. -}
firstFishFact : {X : Set} -> (xz : Bwd X)(xs : List X) ->
  (xz <>< xs) <>> []  ==  xz <>> xs
firstFishFact xz []          = refl
firstFishFact xz (x :> xs)   = firstFishFact (xz <: x) xs

{- You will need more such facts. -}

{- EXERCISE 5.1 -}
{- When we start the editor with the command
      ./Edit foo.txt
   the contents of foo.txt will be turned into a list of lines.
   Your (not so tricky) mission is to turn the file contents into a buffer which
   contains the same text.
   (1 mark)
-}
initBuf : List (List Char) -> Buffer
initBuf ss =
  [] <[
  [] <[ <> ]> []
  ]> []
{- As you can see, the current version will run, but it always gives the empty
   buffer, which is not what we want unless the input is empty. -}

{- Next comes the heart of the editor. You get a keystroke and the current buffer,
   and you have to say what is the new buffer. You also have to say what is the
   extent of the change.

   The tricky part is this: you have to be honest enough about your change
   report, so that we don't underestimate the amount of updating the screen needs.
-}

Honest : Buffer -> Change /*/ Buffer -> Set
Honest b (allQuiet    , b')                            = b == b'
Honest b (cursorMove  , b')                            = bufText b == bufText b'
Honest (sz <[ _ ]> ss) (lineEdit , (sz' <[ _ ]> ss'))  = (sz == sz') /*/ (ss == ss')
Honest _ (bigChange   , _)                             = One

record UpdateFrom (b : Buffer) : Set where   -- b is the starting buffer
  constructor _///_
  field
    update  : Change /*/ Buffer   -- change and new buffer
    honest  : Honest b update
open UpdateFrom
infix 2 _///_

{- EXERCISE 5.2 -}
{- Implement the appropriate behaviour for as many keystrokes as you can.
   I have done a couple for you, but I don't promise to have done them
   correctly. -}
keystroke : Key -> (b : Buffer) -> UpdateFrom b
keystroke (char c)
  (sz <[
   cz <[ <> ]> cs
   ]> ss)
  = lineEdit ,
  (sz <[
   cz <[ <> ]> c :> cs
   ]> ss)
  /// refl , refl          -- see? same above and below
keystroke (arrow normal right)
  (sz <: s <[
   [] <[ <> ]> cs
   ]> ss)
  = cursorMove ,
  (sz <[ ([] <>< s) <[ <> ]> [] ]> cs :> ss)
  /// within (\ x -> sz <>> (x :> cs :> ss)) turn s into ([] <>< s) <>> []
        because symmetry (firstFishFact [] s)
keystroke k b = allQuiet , b /// refl
{- Please expect to need to invent extra functions, e.g., to measure where you
   are, so that up and down arrow work properly. -}
{- Remember also that you can always overestimate the change by saying bigChange,
   which needs only a trivial proof. But you may find that the display will flicker
   badly if you do. -}
{- (char c)                 1 mark
   enter                    2 marks
   backspace delete         2 marks for the pair
   left right               2 marks for the pair (with cursorMove change)
   up down                  2 marks for the pair (with cursorMove change)
   -}


{- EXERCISE 5.3 -}
{- You will need to improve substantially on my implementation of the next component,
   whose purpose is to update the window. Mine displays only one line! -}
render :
  Nat /*/ Nat ->        -- height and width of window -- CORRECTION! width and height
  Nat /*/ Nat ->        -- first visible row, first visible column
  Change /*/ Buffer ->  -- what just happened
  List Action /*/       -- how to update screen
    (Nat /*/ Nat)       -- new first visible row, first visible column
render _ tl (allQuiet , _) = ([] , tl)
render _ tl (_ , (_ <[ cz <[ <> ]> cs ]> _))
  = (goRowCol 0 0 :> sendText (cz <>> cs) :> []) , tl
{- The editor window gives you a resizable rectangular viewport onto the editor buffer.
   You get told
     the current size of the viewport
     which row and col of the buffer are at the top left of the viewport
       (so you can handle documents which are taller or wider than the window)
     the most recent change report and buffer

   You need to figure out whether you need to move the viewport
       (by finding out if the cursor is still within the viewport)
     and if so, where to.

   You need to figure out what to redisplay. If the change report says
     lineEdit and the viewport has not moved, you need only repaint the
     current line. If the viewport has moved or the change report says
     bigChange, you need to repaint the whole buffer.

   You will need to be able to grab a rectangular region of text from the
     buffer, but you do know how big and where from.

   Remember to put the cursor in the right place, relative to where in
     the buffer the viewport is supposed to be. The goRowCol action takes
     *viewport* coordinates, not *buffer* coordinates! You will need to
     invent subtraction!
-}
{- Your code does not need to worry about resizing the window. My code does
   that. On detecting a size change, my code just calls your code with a
   bigChange report and the same buffer, so if you are doing a proper repaint,
   the right thing will happen. -}
{- 2 marks for ensuring that a buffer smaller than the viewport displays
       correctly, with the cursor in the right place, if nobody changes
       the viewport size
   2 marks for ensuring that the cursor remains within the viewport even if
       the viewport needs to move
   1 mark for ensuring that lineEdit changes need only affect one line of
       the display (provided the cursor stays in the viewport)
-}

{- FOR MASOCHISTS ONLY, you have a chance to be even more creative. You have
   spare detectable keys that you could invent meanings for. You also have the
   freedom to change the definition of Buffer, as my code does not care what
   a Buffer is: it only needs to know how to initialize, update and render,
   and these are defined by you.

   Additional structural cursor moves (beginning and end of line, etc) are quite
   easy. Going left or right word-by-word would be more fun: you can match
   against a pattern such as ' '.

   Selection and cut/copy/paste are more challenging. For these, you need to
   modify the Buffer structure to remember the clipboard contents (if any),
   and to manage the extent of any selected region.

   If you feel the need to vary the foreground or background colour of the displayed
   text (e.g. to show a selection), please let me know.

   (SUBTEXT: this exercise is a cut-down version of last year's post-Easter
   task. Feel free to ignore the cutting-down.)
-}


{- Your code then hooks into mine to produce a top level executable! -}
main : IO One
main = mainLoop initBuf (\ k b -> update (keystroke k b)) render

{- To build the editor, just do
     make
   in a shell window (with Ex5 the current directory).
   To run the editor, once compiled, do
     ./Edit
   in the shell window, which should become the editor window.
   To quit the editor, do
     ctrl-C
   like an old-fashioned soul.
-}

{- There is no one right way to do this exercise, and there is some scope for
   extension. It's important that you get in touch if you need help, either in
   achieving the basic deliverable, or in finding ways to explore beyond it.
-}
