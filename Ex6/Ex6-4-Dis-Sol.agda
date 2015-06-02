module Ex6-4-Dis-Sol where

open import Ex6-Setup
open import Ex6-1-Vec-Sol
open import Ex6-2-Box-Sol
open import Ex6-3-Cut-Sol


---------------------------------------------------------------------------
-- CURSES DISPLAY FOR APPLICATIONS (5 marks)                             --
---------------------------------------------------------------------------

-- You may need to look at the Ex6-Setup file to find some of the relevant
-- kit for this episode, and it's worth looking there for goodies, anyway.
-- We start from the idea of a main loop.

{- This is the bit of code I wrote in Haskell to animate your code. -}
postulate
  mainLoop : {S : Set} ->             -- program state
    -- INITIALIZER
    S ->                              -- initial state
    -- EVENT HANDLER
    (Event -> S ->                    -- event and state in
     S /**/ List Action) ->           -- new state and screen actions out
    -- PUT 'EM TOGETHER AND YOU'VE GOT AN APPLICATION!
    IO Thud
{-# COMPILED mainLoop (\ _ -> HaskellSetup.mainLoop) #-}

-- The type S /**/ T is a type of pairs that the compiler can share with
-- Haskell. Its constructor is _,_ just as for S /*/ T. Meanwhile Thud
-- does the same job for One, but you won't need to bother with it.

-- To make a thing you can run, you need to
--   (i)    choose a type to represent the program's internal state S
--   (ii)   give the initial state
--   (iii)  explain how, given an event and the current state, to
--            produce a new state and a list of actions to update the
--            display.

-- Let me show you the example I gave in class...


---------------------------------------------------------------------------
-- My silly wee demo                                                     --
---------------------------------------------------------------------------

-- the program state...

SillyState : Set
SillyState = Char /*/ Nat /*/ Nat

-- ...knows the character to put round the edge of the window, and the
-- size of the window

-- To paint a window whose dimensions are both at least 2, we...

sillyPaint : SillyState -> List Action
sillyPaint (c , suc (suc w), suc (suc h))
  =   goRowCol 0 0                   -- send the cursor home
  ::  bgText black :: fgText green   -- adopt our colour scheme
  ::  sendText (concat (             -- send ...   
        list (suc (suc w)) c ::                           -- ... top
        concat (list h (c :: list w ' ' +-+ c :: [])) ::  -- middle
        list (suc (suc w)) c :: [])) ::                   -- and bottom
        []
sillyPaint _ = []

-- There are two kinds of event we must consider: keystroke and resize.

sillyHandler : Event -> SillyState -> SillyState /**/ List Action
sillyHandler (key (char c)) (_ , w , h) = s , sillyPaint s where
  -- if we get an ordinary character key,
  -- update the character and repaint
  s : SillyState
  s = (c , w , h)
sillyHandler (resize w h) (c , _ , _) = s , sillyPaint s where
  -- if we get a resizing event,
  -- update the size and repaint
  s : SillyState
  s = (c , w , h)
sillyHandler _ s = s , []   -- otherwise, relax

-- To finish the job, we write a "main" function, plugging in the initial
-- state. The initial size of 0 by 0 will provoke an immediate resize event,
-- giving the correct size!

{- -
main : IO Thud
main = mainLoop ('*' , 0 , 0) sillyHandler
- -}

-- To run this program, start a terminal, change to your Ex6 directory, then
--
--    make go4
--
-- You should be able to press keys and resize the thing and see sensible
-- stuff happen. Ctrl-C quits.

-- When you're bored of green rectangles, comment out the above main
-- function, so you can move on to the actual work. There are other
-- main functions further down the file which you can comment in as you
-- need them. Of course, you can have at most one main at a time.


---------------------------------------------------------------------------
-- PAINTINGS                                                             --
---------------------------------------------------------------------------

-- Now that we're in colour, one cell of display will be a ColourChar ...

data ColourChar : Set where
  _-_/_ : (fg : Colour)(c : Char)(bg : Colour) -> ColourChar

-- ... e.g.     green - '*' / black    for what we had, above.

-- a painting is a Box structure whose basic tiles are either transparent
-- holes or opaque rectangles of coloured text.

Painting : Nat -> Nat -> Set
Painting = Box (HoleOr (Matrix ColourChar))

-- Now your turn. Making use of the equipment you developed in epsiode 2,
-- get us from a Painting to a List Action in two hops. Note that you will
-- have to decide how to render a Hole: some bland background stuff, please.
-- (1 mark)

paintMatrix : Painting []> Matrix ColourChar
paintMatrix p = pasteBox matrixPasteKit (mapBox fill p) where
  fill : HoleOr (Matrix ColourChar) []> Matrix ColourChar
  fill Hole = vec (vec (black - ' ' / white))
  fill [ m ] = m

vecFoldR : {X Y : Set} -> (X -> Y -> Y) -> Y -> {n : Nat} -> Vec X n -> Y
vecFoldR c n [] = n
vecFoldR c n (x :: xs) = c x (vecFoldR c n xs)

paintAction : {w h : Nat} -> Matrix ColourChar w h -> List Action
paintAction = vecFoldR (vecFoldR (\ {(f - c / b) k -> \ as ->
  fgText f :: bgText b :: sendText (c :: []) :: k as}) id) []


---------------------------------------------------------------------------
-- APPLICATIONS                                                          --
---------------------------------------------------------------------------

-- Here's a general idea of what it means to be an "application".
-- You need to choose some sort of size-dependent state, then provide these
-- bits and pieces. We need to know how the state is updated according to
-- events, with resizing potentially affecting the state's type. We must
-- be able to paint the state. The state should propose a cursor position.
-- (Keen students may modify this definition to ensure the cursor must be
-- within the bounds of the application.)

record Application (S : Nat -> Nat -> Set) : Set where
  field
    handleKey     : Key -> S []> S
    handleResize  : {w h : Nat}(w' h' : Nat) -> S w h -> S w' h'
    paintMe       : S []> Painting
    cursorMe      : {w h : Nat} -> S w h -> Nat /*/ Nat  -- x,y coords
open Application public

-- Now your turn. Build the appropriate handler to connect these
-- applications with mainLoop. Again, work in two stages, first
-- figuring out how to do the right actions, then managing the
-- state properly. (1 mark)

AppState : (S : Nat -> Nat -> Set) -> Set
AppState S = Sg Nat \ w -> Sg Nat \ h -> S w h

appPaint : {S : Nat -> Nat -> Set}{w h : Nat} ->
           Application S -> S w h -> List Action
appPaint app s =
  goRowCol 0 0 :: paintAction (paintMatrix p)
  +-+ (goRowCol (snd xy) (fst xy) :: [])
  where
    p  = paintMe app s
    xy = cursorMe app s

appHandler : {S : Nat -> Nat -> Set} ->
           Application S ->
           Event -> AppState S -> AppState S /**/ List Action
appHandler app (key k) (w , h , s) = (w , h , s') , appPaint app s'
  where s' = handleKey app k s
appHandler app (resize w' h') (w , h , s) = (w' , h' , s') , appPaint app s'
  where s' = handleResize app w' h' s

-- Your code turns into a main function, as follows.

appMain : {S : Nat -> Nat -> Set} -> Application S -> S 0 0 -> IO Thud
appMain app s = mainLoop (0 , 0 , s) (appHandler app) 


---------------------------------------------------------------------------
-- THE DEMO, MADE INTO AN APPLICATION                                    --
---------------------------------------------------------------------------

sillyChar : Char -> {w h : Nat} -> Painting w h
sillyChar c = [ [ vec (vec (green - c / black)) ] ]

sillyApp : Application \ _ _ -> Char
sillyApp = record
  {  handleKey     = \ { (char c) _ -> c ; _ c -> c }
  ;  handleResize  = \ _ _ c -> c
  ;  paintMe       = \
       { {suc (suc w)} {suc (suc h)} c ->
          tobo 1 (sillyChar c)
          (suc h) (tobo h
            (leri 1 (sillyChar c) (suc w)
             (leri w (sillyChar ' ') 1 (sillyChar c) (plusCommFact 1 w))
             refl)
            1 (sillyChar c) (plusCommFact 1 h) )
          refl
       ; c -> sillyChar c
       }
  ;  cursorMe      = \ _ -> 0 , 0
  }

{- -
main : IO Thud
main = appMain sillyApp '*'
- -}


---------------------------------------------------------------------------
-- COMPARING TWO NUMBERS                                                 --
---------------------------------------------------------------------------

-- You've done the tricky part in episode 3, comparing two splittings of
-- the same number. Here's an easy way to reuse that code just to compare
-- two numbers. It may help in what is to come.

Compare : Nat -> Nat -> Set
Compare x y = CutCompare x y y x (x + y)

compare : (x y : Nat) -> Compare x y
compare x y = cutCompare x y y x (x + y) refl (plusCommFact x y)

-- To make sure you've got the message, try writing these things
-- "with compare" to resize paintings. If you need to make a painting
-- bigger, pad its right or bottom with a hole. If you need to make it
-- smaller, trim off the right or bottom excess. You have all the gadgets
-- you need! I'm not giving marks for these, but they'll be useful in
-- the next bit.

cropPadLR : (w h w' : Nat) -> Painting w h -> Painting w' h
cropPadLR w h w' p with compare w w'
cropPadLR w h w' p | cutLt d q _ = leri w p (suc d) [ Hole ] q
cropPadLR w h .w p | cutEq refl _ = p
cropPadLR w h w' p | cutGt d q _
  = fst (CutKit.cutLR (boxCutKit (holeCutKit matrixCutKit))
         w h w' (suc d) q p)

cropPadTB : (w h h' : Nat) -> Painting w h -> Painting w h'
cropPadTB w h h' p with compare h h'
cropPadTB w h h' p | cutLt d q _ = tobo h p (suc d) [ Hole ] q
cropPadTB w h .h p | cutEq refl _ = p
cropPadTB w h h' p | cutGt d q _
  = fst (CutKit.cutTB (boxCutKit (holeCutKit matrixCutKit))
         w h h' (suc d) q p)

---------------------------------------------------------------------------
-- THE MOVING RECTANGLE                                                  --
---------------------------------------------------------------------------

-- This is the crux of the episode. Please build me an application which
-- displays a movable resizeable rectangle drawn with ascii art as follows
--
--           +--------------+
--           |              |
--           |              |
--           +--------------+
--
-- The "size" of the application is the terminal size: the rectangle should
-- be freely resizable *within* the terminal, so you should pad out the
-- rectangle to the size of the screen using Hole.
-- That is, only the rectangle is opaque; the rest is transparent.
-- The background colour of the rectangle should be given as an argument.
-- The foreground colour of the rectangle should be white.
-- The rectangle should have an interior consisting of opaque space with
-- the given background colour.
--
-- The arrow keys should move the rectangle around inside the terminal
-- window, preserving its size (like when you drag a window around).
-- Shifted arrow keys should resize the rectangle by moving its bottom
-- right corner (again, like you might do with a mouse).
-- You do not need to ensure that the rectangle fits inside the terminal.
-- The cursor should sit at the bottom right corner of the rectangle.
--
-- Mac users: the Terminal application which ships with OS X does NOT
-- give the correct treatment to shift-up and shift-down. You can get a
-- suitable alternative from http://iterm2.com/ (Thank @sigfpe for the tip!)
--
-- (2 marks, one for key handling, one for painting)

record RectState : Set where
  constructor rect
  field
    gapL rectW : Nat
    gapT rectH : Nat

rectKey : Key -> RectState -> RectState
rectKey (arrow normal up) (rect gapL rectW (suc gapT) rectH)
  = rect gapL rectW gapT rectH
rectKey (arrow normal down) (rect gapL rectW gapT rectH)
  = rect gapL rectW (suc gapT) rectH
rectKey (arrow normal left) (rect (suc gapL) rectW gapT rectH)
  = rect gapL rectW gapT rectH
rectKey (arrow normal right) (rect gapL rectW gapT rectH)
  = rect (suc gapL) rectW gapT rectH
rectKey (arrow shift up) (rect gapL rectW gapT (suc rectH))
  = rect gapL rectW gapT rectH
rectKey (arrow shift down) (rect gapL rectW gapT rectH)
  = rect gapL rectW gapT (suc rectH)
rectKey (arrow shift left) (rect gapL (suc rectW) gapT rectH)
  = rect gapL rectW gapT rectH
rectKey (arrow shift right) (rect gapL rectW gapT rectH)
  = rect gapL (suc rectW) gapT rectH
rectKey _ s = s

rectApp : Colour -> Application \ _ _ -> RectState
rectApp c = record
  {  handleKey     = \ k -> rectKey k
  ;  handleResize  = \ _ _ -> id
  ;  paintMe = \ { (rect gapL rectW gapT rectH) ->
       cropPadTB _ _ _ (cropPadLR _ _ _
       (tobo gapT [ Hole ] (suc (rectH + 1))
        (leri gapL [ Hole ] (suc (rectW + 1))
         (tobo 1 (horiz rectW) _
         (tobo rectH
           (leri 1 (vert rectH) _ 
           (leri rectW (interior rectW rectH) 
           1 (vert rectH) refl) refl) 
         1 (horiz rectW) refl) refl)
       refl) refl)) }
  ;  cursorMe = \ { (rect gapL rectW gapT rectH) ->
       (1 + gapL + rectW) , (1 + gapT + rectH)
     }
  } where
  horiz : (w : Nat) -> Painting (suc (w + 1)) 1
  horiz w = leri 1 [ [ (white - '+' / c :: []) :: [] ] ] _
    (leri w [ [ vec (white - '-' / c) :: [] ] ] 1
      [ [ (white - '+' / c :: []) :: [] ] ] refl) refl
  vert : (h : Nat) -> Painting 1 h
  vert h = [ [ vec (vec (white - '|' / c)) ] ]
  interior : (w h : Nat) -> Painting w h
  interior w h = [ [ vec (vec (white - ' ' / c)) ] ]

{- -
main : IO Thud
main = appMain (rectApp blue) (rect 10 40 3 15)
- -}


---------------------------------------------------------------------------
-- TWO BECOME ONE                                                        --
---------------------------------------------------------------------------

-- Write a function which turns two sub-applications into one main
-- application by layering them.
--
-- For some S and T, you get an Application S and an Application T
-- You should choose a suitable state representation so that you know
--   (i)   which of the two applications is at the front, and which behind
--   (ii)  the states of both.
--
-- The Tab key should swap which sub-application is at the front, as if you had
-- clicked on the one at the back. All other keys should be handled by
-- whichever action is in front at the time. Also, the cursor position
-- should be chosen by the sub-application at the front.
--
-- The overall application size will be used as the size for both
-- sub-application sizes, which means you should be able to compute the
-- layered Painting, using equipment from episode 3. Crucially, we should be
-- able to see through the holes in the front sub-application to stuff from
-- the back sub-application.
--
-- (1 mark)

frontBack : {S T : Nat -> Nat -> Set} ->
  Application S ->
  Application T ->
  Application \ w h -> (S w h /*/ T w h) /+/ (T w h /*/ S w h)
frontBack appS appT = record
  { handleKey = \
    { tab (inl (s , t))  -> inr (t , s)
    ; tab (inr (t , s))  -> inl (s , t)
    ; k (inl (s , t))    -> inl (handleKey appS k s , t)
    ; k (inr (t , s))    -> inr (handleKey appT k t , s)
    }
  ; handleResize = \
    { w h (inl (s , t)) -> inl  (  handleResize appS w h s
                                ,  handleResize appT w h t  )
    ; w h (inr (t , s)) -> inr  (  handleResize appT w h t
                                ,  handleResize appS w h s  )
    }
  ; paintMe = \ 
    { (inl (s , t)) -> overlay matrixCutKit (paintMe appS s) (paintMe appT t)
    ; (inr (t , s)) -> overlay matrixCutKit (paintMe appT t) (paintMe appS s)
    }
  ; cursorMe = \
    { (inl (s , t)) -> cursorMe appS s
    ; (inr (t , s)) -> cursorMe appT t
    }    
  }

-- By way of example, let's have a blue rectangle and a red rectangle.

{- -
main : IO Thud
main = appMain (frontBack (rectApp blue) (rectApp red))
  (inl (rect 10 40 3 15 , rect 20 40 8 15))
- -}

---------------------------------------------------------------------------
-- NEXT TIME ...                                                         --
---------------------------------------------------------------------------

-- You get to figure out how to reduce flicker.
-- You get to think up some fun stuff to put in the rectangles.
