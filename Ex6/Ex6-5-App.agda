module Ex6-5-App where

open import Ex6-Setup
open import Ex6-1-Vec-Sol
open import Ex6-2-Box-Sol
open import Ex6-3-Cut-Sol
open import Ex6-4-Dis-Sol


---------------------------------------------------------------------------
-- SMOOTHER AND MORE INTERESTING APPLICATIONS (5 marks)                  --
---------------------------------------------------------------------------

-- As these are the 5 marks which get you from "awesome first" to
-- "perfection", I'm leaving this task more open. There are two
-- parts to it.

-- Part 1. MINIMIZE FLICKER. The episode 4 setup repaints the whole
-- screenful every time. With a little bit of redesign, it's possible
-- to ensure that you repaint only what changes. Re-engineer the
-- functionality of exercise 4 to reduce flicker.
-- (2 marks)

-- Part 2. PUT SOMETHING INTERESTING IN THE RECTANGLES. It's one thing
-- being able to shove rectangles around the screen, but it would be
-- good if there was some actual content to them. You're free to design
-- whatever you like (and to raid Ex5 for spare parts, of course), but
-- I have some marking guidelines.
--   any nontrivial static content in the rectangles scores 1 mark,
--     provided you can still move and resize them;
--   treating the rectangle as a viewport into some content larger than
--     the rectangle scores 1 mark, provided you can move the viewport
--     all around the content
--   significant keyboard interaction with the rectangle at the front,
--     beyond what is needed for moving it, resizing it and refocusing
--     it, is worth 1 mark
-- (3 marks)

-- If you can think of other interesting things you might want to do that
-- don't quite fit the mark scheme for part 2, by all means pitch them to
-- me and I'll tell you how much I'd be willing to "pay" for them.


-- The rest of the file consists of some bits and pieces I came up with
-- while I was experimenting. You are free to adopt, adapt or reject these
-- components.


---------------------------------------------------------------------------
-- GENERALIZING OVERLAY TO MASKING                                       --
---------------------------------------------------------------------------

-- Here's what I should have asked you to build in episode 3.

mask : {X Y Z : Nat -> Nat -> Set} -> CutKit Y ->
       ({w h : Nat} -> X w h -> Box Y w h -> Box Z w h) ->
       {w h : Nat} ->
       {- front -}     Box X w h ->
       {- back  -}     Box Y w h ->
       {- combined -}  Box Z w h
mask {X}{Y}{Z} ck m = go where
  open CutKit (boxCutKit ck)
  go : {w h : Nat} -> Box X w h -> Box Y w h -> Box Z w h
  go xb yb = {!!}

-- The idea, as with "overlay", is that the box of X stuff is in front
-- and the box of Y stuff is behind. You need to combine them to make
-- a box of Z stuff. Fortunately, once you've cut your way through the
-- structure to reach each basic X tile, the parameter m is just what
-- you need to know to combine that tile with the Y box to make a Z box.

-- You should find that the implementation is almost the same as "overlay"
-- but the extra generality is quite useful. You might find the following
-- concepts helpful.

Update : Nat -> Nat -> Set
Update w h
  =    Two                               -- does it demand repainting?
  /*/  HoleOr (Matrix ColourChar) w h    -- transparent or opaque stuff?

-- A Box Update is more informative than a Painting, in that every primitive
-- tile tells you whether it is "new" or not; now you can build the logic
-- to combine the changes which happen in each layer. In particular, you can
-- model the idea that moving or resizing in the front can reveal stuff which
-- used to be hidden at the back: that's a "new hole", and even if what's
-- behind it hasn't changed, you'll need to update the display.

Selection : Nat -> Nat -> Set
Selection = Box \ _ _ -> Two

-- A selection is a tiling of the rectangle with tt or ff. You can lift all
-- the usual logical operations to selections using mask and mapBox. For
-- example, XOR-ing selections gives you everything in one but not the other,
-- which might help you spot what has changed.


---------------------------------------------------------------------------
-- RUN-LENGTH ENCODING INACTIVITY                                        --
---------------------------------------------------------------------------

-- An idea which might be useful in helping you to manage more selective
-- redrawing is to build the idea of "doing nothing for a bit" into the
-- lists of actions that you build up. Think about updating one line of
-- the display: it might sometimes help to be able to say "keep the next
-- n cells as they were", which you could interpret as a cursor move, rather
-- than a text output.

-- Correspondingly, you might benefit from a data structure like this:

data Skippy (X : Set) : Set where
  []    : Skippy X                        -- stop
  _::_  : X -> Skippy X -> Skippy X       -- give one X then keep going
  _>_   : Nat -> Skippy X -> Skippy X     -- skip n places, then keep going

-- Now, when you work with these structures, you should enforce that
--   (i)  you never have   zero > xs    (if there's nothing to skip, don't)
--   (ii) you never have   m > n > xs   (don't skip twice, skip further)

-- It's possible to refine the type Skippy to enforce those properties by
-- the power of type checking. Or you could just make sure you never cheat
-- by the more traditional method of defining a "smart constructor"

_>>_ : {X : Set} -> Nat -> Skippy X -> Skippy X
-- special cases go here
n >> xs = n > xs

-- The definition I've given you isn't very smart: >> is the same as >.
-- But the idea is that you add some special cases before that last line
-- which catch the possibilities that should never happen and do something
-- else instead. Now you can define operations like concatenation, using
-- the smart constructor in place of the regular one.

_+>+_ : {X : Set} -> Skippy X -> Skippy X -> Skippy X
[]         +>+  ys  = ys
(x :: xs)  +>+  ys  = x :: (xs +>+ ys)
(m > xs)   +>+  ys  = m >> (xs +>+ ys)
--                      ^^ see?

-- That way, you know that if the lists you're concatenating satisfy the
-- above rules, so will the result.


---------------------------------------------------------------------------
-- ANOTHER SMART CONSTRUCTOR                                             --
---------------------------------------------------------------------------

-- You might consider playing the same game with the List Action type that
-- we use for displaying things. Here's part of mine.

_:a:_ : Action -> List Action -> List Action
goRowCol _ _  :a: (goRowCol r c :: as)  = goRowCol r c :: as
sendText x    :a: (sendText y :: as)    = sendText (x +-+ y) :: as
a             :a: as                    = a :: as

-- That's to say
--   (i)  there's no point in positioning the cursor twice in a row, when
--          the second just overrides the first;
--   (ii) don't send two small texts when you can send one big text.


---------------------------------------------------------------------------
-- CROP-AND-PAD                                                          --
---------------------------------------------------------------------------

-- As with overlay, the types of cropPadLR and cropPadTB from episode 4
-- are more specific than is necessarily helpful. How about this instead?

cropPadXLR :  {X : Nat -> Nat -> Set}           -- some stuff
              (ck : CutKit X) ->                -- how to cut stuff
              (px : {w h : Nat} -> X w h) ->    -- how to make "blank" stuff
              (w h w' : Nat) -> Box X w h -> Box X w' h
cropPadXLR ck px w h w' b = {!!}

-- and its TB friend, of course. Now you can crop things other than
-- Paintings.


---------------------------------------------------------------------------
-- FROM APPLICATIONS TO UPPLICATIONS                                     --
---------------------------------------------------------------------------

-- The notion of "Application" from episode 4 required you to define a
-- paintMe function which just gives the full display. You may need to
-- rethink this concept to get an *updating* application, or "Upplication"
-- in which at least some of the event handlers tell you just what has
-- changed. You will certainly need *more* information, but you should
-- also consider whether it would be better if the existing information
-- took a different form.


---------------------------------------------------------------------------
-- PUTTING UPPLICATIONS TOGETHER                                         --
---------------------------------------------------------------------------

-- In episode 4, you had to define the frontBack operator, which combined
-- two applications into one by *layering* them. How does that work for
-- upplications? What other spatial combinations of upplications make sense?
-- Here are three possibilities worth considering:
--   (i)    putting two applications side-by-side,
--   (ii)   putting one application above another,
--   (iii)  viewing an application through a rectangular viewport.
-- Of course, there are many more possibilities.
--
-- Toggling with the tab key is all very well when there are only two
-- components, but you might need to think a little harder about how to
-- navigate when there are more. Normally, you'd use your finger for that,
-- or a mouse. Sadly, I don't know how to organise mouse interaction with
-- terminal windows. But you could make a pretend mouse: a top layer which
-- displays a "mouse cursor" that you can move around with arrow keys when
-- you're in "mouse mode". Clicking could be a keystroke which activates
-- the frontmost opaque thing behind the mouse and exits mouse mode.


---------------------------------------------------------------------------
-- MAIN                                                                  --
---------------------------------------------------------------------------

-- I've added
--   make go5
-- to the Makefile

-- I've set the main application to be the silly one from episode 4, but
-- you can swap in your own thing.

main : IO Thud
main = mainLoop ('*' , 0 , 0) sillyHandler
