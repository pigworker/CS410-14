module Ex6-3-Cut where

open import Ex6-Setup
open import Ex6-1-Vec
open import Ex6-2-Box

---------------------------------------------------------------------------
-- CUTTING UP BOXES (5 marks)                                            --
---------------------------------------------------------------------------

-- Previously...
-- ... we established what it is to be a CutKit, and we built CutKits
-- for some sorts of basic tile. Now we need to build the CutKit for
-- Box. Let's think about what that involves for a moment. We're going
-- to need a CutKit for basic tiles to stand a chance. But how do we
-- cut compound tiles?
--
-- Suppose we're writing cutLR, and we have some
--   cq : cwl + cwr == w   -- the "cut widths" equation
-- telling us where we want to make the cut in something of width w.
--
--             v
--    +--------:------+
--    |        :      |
--    |        :      |
--    +--cwl---:-cwr--+
--    :        ^      :
--    :.......w.......:
--
-- The tricky part is when the box we're cutting here is built with
--   leri bwl bl bwr br bq
-- where
--   bq : bwl + bwr == w   -- the "box widths" equation
--
-- There are three possible situations, all of which you must detect
-- and handle.
--
-- (i) you hit the sweet spot...
--
--             v
--    +--bwl---+-bwr--+
--    |        |      |
--    |        |      |
--    +--cwl---+-cwr--+
--    :        ^      :
--    :.......w.......:
--
--     ...where the box is already divided in the place where the cut
--     has to go. Happy days.
--
-- (ii) you're cutting to the left of the join...
--
--             v
--    +--bwl-----+bwr-+
--    |        : |    |
--    |        : |    |
--    +--cwl---:-cwr--+
--    :        ^      :
--    :.......w.......:
--
--     ...so you'll need to cut the left box in the correct place. You
--     will need some evidence about widths to do that. And then you'll
--     the have three pieces you can see in my diagram, so to complete
--     the cut, you will need to put two of those pieces together, which
--     will take more evidence.
--
-- (iii) you're cutting to the right of the join...
--
--             v
--    +--bwl-+--bwr---+
--    |      | :      |
--    |      | :      |
--    +--cwl---:-cwr--+
--    :        ^      :
--    :.......w.......:
--
--     ...so you'll need to cut the right box in the correct place, and
--     reassemble the bits.
--
-- HINT: THE FIRST THREE MARKS IN THIS EPISODE COME FROM ONE PROBLEM.
-- TREAT THEM AS A WHOLE.


---------------------------------------------------------------------------
-- COMPARING THE CUT POSITION                                            --
---------------------------------------------------------------------------

data CutCompare (x x' y y' n : Nat) : Set where
  -- Give three constructors for this type which characterize the three
  -- possibilities described above whenever
  --   x + x' == n   and   y + y' == n
  -- (E.g., take n to be w, x and x' to be cwl and cwr, y and y' to be
  -- bwl and bwr. But later, you'll need to do use the same tool for
  -- heights.)
  --
  -- You will need to investigate what evidence must be packaged in each
  -- situation. On the one hand, you need to be able to *generate* the
  -- evidence, with cutCompare, below. On the other hand, the evidence
  -- must be *useful* when you come to write boxCutKit, further below.
  -- Don't expect to know what to put here from the get-go. Figure it
  -- out by discovering what you *need*.
  --
  -- (1 mark)

-- Show that whenever you have two ways to express the same n as a sum,
-- you can always deliver the CutCompare evidence. (1 mark)

cutCompare : (x x' y y' n : Nat) -> x + x' == n -> y + y' == n ->
             CutCompare x x' y y' n
cutCompare x x' y y' n xq yq = {!!}


---------------------------------------------------------------------------
-- A CUTKIT FOR BOXES                                                    --
---------------------------------------------------------------------------

-- Now, show that you can construct a CutKit for Box X, given a CutKit
-- for X. There will be key points where you get stuck for want of crucial
-- information. The purpose of CutCompare is to *describe* that
-- information. The purpose of cutCompare is to *compute* that information.
-- Note that cutLR and cutTB will work out very similarly, just exchanging
-- the roles of width and height.
-- (1 mark)

boxCutKit : {X : Nat -> Nat -> Set} -> CutKit X -> CutKit (Box X)
boxCutKit {X} ck = record { cutLR = clr ; cutTB = ctb } where
  open CutKit ck
  clr : (w h wl wr : Nat) ->
          wl + wr == w -> Box X w h -> Box X wl h /*/ Box X wr h
  clr w h wl wr wq b = {!!}
  ctb : (w h ht hb : Nat) ->
          ht + hb == h -> Box X w h -> Box X w ht /*/ Box X w hb
  ctb w h ht hb hq b = {!!}


---------------------------------------------------------------------------
-- CROP                                                                  --
---------------------------------------------------------------------------

-- Show that, given a CutKit, you can implement the "crop" operation which
-- trims a small rectangle out of an enclosing rectangle.
-- (1 mark)

crop : {X : Nat -> Nat -> Set} -> CutKit X ->
       (wl wc wr ht hc hb : Nat) ->
       X (wl + wc + wr) (ht + hc + hb) -> X wc hc
crop ck wl wc wr ht hc hb x = {!!}

-- For fun, practice, and the chance to test your work, try building
-- a nontrivially tiled...

testBigBox : Box (HoleOr _*C*_) 20 15
testBigBox = {!!}

-- ...so that you can see this stuff in action:

textDisplayCutKit : CutKit (Box (HoleOr _*C*_))
textDisplayCutKit = boxCutKit (holeCutKit matrixCutKit)

testWeeBox : Box (HoleOr _*C*_) 10 5
testWeeBox = crop textDisplayCutKit 5 10 5 5 5 5 testBigBox


---------------------------------------------------------------------------
-- OVERLAY                                                               --
---------------------------------------------------------------------------

-- If we use HoleOr X as the basic tile, we can think of Hole as meaning
-- a bit of a box we can see through. Correspondingly, if we have two
-- boxes (the "front" one and the "back" one), both the same size, we
-- should be able to see through the holes in the front box to whatever
-- stuff is in the back box in the corresponding place.
--
-- Your task here is to show that you can combine front and back layers
-- into a single box, corresponding to what you would actually see. That
-- is, you will need to fill the front holes in with stuff cut from the
-- back. Which is why you need a CutKit for boxes.
--
-- Hint: you may be tempted to use crop, but try without crop first.
--
-- (1 mark)

overlay : {X : Nat -> Nat -> Set} -> CutKit X ->
          {w h : Nat} ->
          {- front -}     Box (HoleOr X) w h ->
          {- back  -}     Box (HoleOr X) w h ->
          {- combined -}  Box (HoleOr X) w h
overlay {X} ck = go where
  open CutKit (boxCutKit (holeCutKit ck))
  go : {w h : Nat} ->
       Box (HoleOr X) w h -> Box (HoleOr X) w h -> Box (HoleOr X) w h
  go front back = {!!}

-- You should ensure (but I won't ask you to prove) that you have thus
-- equipped Box (HoleOr X) w h with the structure of a *monoid* with
-- the neutral value (nil-like thing) being [ Hole ] and the
-- associative operation (append-like thing) being (overlay ck), where
-- ck is your CutKit X. That is, there is such a thing as a totally
-- transparent layer, and you can overlay *any* number of layers by
-- combining any two neighbouring layers at a time.

-- For fun, and the shape of things to come, build two box tilings.
-- Make sure each has a rectangle of text in the middle and Hole all
-- around. Make sure that the rectangles overlap each other, but not
-- completely. See what happens when you overlay them, either way
-- around.

rectangleA : Box (HoleOr _*C*_) 20 15
rectangleA = {!!}

rectangleB : Box (HoleOr _*C*_) 20 15
rectangleB = {!!}

frontA_backB : 20 *C* 15
frontA_backB = renderHoleOrText (overlay matrixCutKit rectangleA rectangleB)

frontB_backA : 20 *C* 15
frontB_backA = renderHoleOrText (overlay matrixCutKit rectangleB rectangleA)
