module Ex6-2-Box-Sol where

open import Ex6-Setup
open import Ex6-1-Vec-Sol

---------------------------------------------------------------------------
-- BOXES (5 marks)                                                       --
---------------------------------------------------------------------------

-- Boxes are sized rectangular tilings which fit together precisely.
-- They allow us to talk about the use of 2D space, e.g., on a screen.

data Box (X : Nat -> Nat -> Set)(w h : Nat) : Set where
--        ^basic-tile       width^ ^height

  [_] : X w h -> Box X w h
--      a basic tile is a tiling

  leri : (wl : Nat)   (bl : Box X wl h)
         (wr : Nat)   (br : Box X wr h)
         -> wl + wr == w -> Box X w  h
-- combine "left" and "right" tilings the same height
-- to make a tiling with their total width

  tobo : (ht : Nat)   (bt : Box X w ht)
         (hb : Nat)   (bb : Box X w hb)
         -> ht + hb == h -> Box X w h
-- combine "top" and "bottom" tilings the same width
-- to make a tiling with their total height


---------------------------------------------------------------------------
-- MONADIC STRUCTURE                                                     --
---------------------------------------------------------------------------

-- If X and Y are both kinds of "sized stuff", we can say what it is to be
-- a "size-preserving function" between them.

_[]>_ : (X Y : Nat -> Nat -> Set) -> Set
X []> Y = {w h : Nat} -> X w h -> Y w h
-- A size preserving function turns an X of some size
--                              into a Y the same size.

-- Think of X as "sized placeholders". If we have a way to turn each
-- placeholder into a tiling which fits into the place, we should be
-- able to deploy it across a whole tiling of placeholders. Check
-- that you can achieve that.

_=<<_ : forall {X Y} -> X []> Box Y -> Box X []> Box Y
f =<< [ x ]              = f x
f =<< leri wl bl wr br x = leri wl (f =<< bl) wr (f =<< br) x
f =<< tobo ht bt hb bb x = tobo ht (f =<< bt) hb (f =<< bb) x

-- Using _=<<_, rather than more recursion, define... 

mapBox : forall {X Y} -> X []> Y -> Box X []> Box Y
mapBox f b = ([_] o f) =<< b
-- roll out a size-preserving function on basic tiles to a whole tiling

joinBox : forall {X} -> Box (Box X) []> Box X
joinBox b = id =<< b
-- turn a tiling-of-tilings into a simple tiling

-- (1 mark) for the lot


---------------------------------------------------------------------------
-- PASTE KITS AND MATRICES                                               --
---------------------------------------------------------------------------

-- A "paste kit" for sized stuff is whatever you need to combine stuff
-- left-to-right and top-to-bottom

record PasteKit (X : Nat -> Nat -> Set) : Set where
  field
    leriPaste : (wl wr : Nat){h : Nat} -> X wl h -> X wr h -> X (wl + wr) h
    toboPaste : {w : Nat}(ht hb : Nat) -> X w ht -> X w hb -> X w (ht + hb)

-- Show that a PasteKit is just what you need to turn a tiling of
-- stuff into some stuff. (1 mark)

pasteBox : {X : Nat -> Nat -> Set} -> PasteKit X -> Box X []> X
pasteBox {X} pk = go where
  open PasteKit pk -- brings leriPaste and toboPaste into scope
  go : Box X []> X
  go [ x ] = x
  go (leri wl lb wr rb refl) = leriPaste wl wr (go lb) (go rb)
  go (tobo ht tb hb bb refl) = toboPaste ht hb (go tb) (go bb)

-- If you were wondering what any of this had to do with part 1, here we
-- go...

Matrix : Set -> Nat -> Nat -> Set
Matrix C w h = Vec (Vec C w) h
-- matrices are "sized stuff", represented as a vector the right height
-- of rows which are vectors the right width of some sort of unit "cell".

-- Using the equipment you built in part 1, give matrices their PasteKit.
-- (1 mark)

matrixPasteKit : {C : Set} -> PasteKit (Matrix C)
matrixPasteKit = record {
  leriPaste = \ _ _ ls rs -> vec _++_ <*> ls <*> rs ;
  toboPaste = \ _ _ -> _++_ }


---------------------------------------------------------------------------
-- INTERLUDE: TESTING WITH TEXT                                          --
---------------------------------------------------------------------------

-- Turn a list into a vector, either by truncating or padding with
-- a given dummy element.
paddy : {X : Set} -> X -> List X -> {n : Nat} -> Vec X n
paddy _ _         {zero}   = []
paddy x []        {suc n}  = x :: paddy x [] {n}
paddy x (y :: ys) {suc n}  = y :: paddy x ys {n}

-- Use that to make vectors of characters from strings, padding with space.
[-_-] : String -> {n : Nat} -> Vec Char n
[- s -] = paddy ' ' (primStringToList s)

-- Now we can have character matrices of a given size
_*C*_ : Nat -> Nat -> Set
w *C* h = Matrix Char w h

-- Here are some.
mat43-1 : 4 *C* 3
mat43-1 = [- "post" -] :: [- "cake" -] :: [- "flop" -] :: []

mat43-2 : 4 *C* 3
mat43-2 = [- "horn" -] :: [- "walk" -] :: [- "ping" -] :: []

mat22 : 2 *C* 2
mat22 = [- "go" -] :: [- "do" -] :: []

mat62 : 6 *C* 2
mat62 = [- "getter" -] :: [- "gooder" -] :: []

-- Put them together as a tiling.
myTiling : Box _*C*_ 8 5
myTiling = tobo 3 (leri 4 [ mat43-1 ] 4 [ mat43-2 ] refl)
                2 (leri 2 [ mat22 ] 6 [ mat62 ] refl) refl

-- Paste all the pieces and see what you get!
myText : 8 *C* 5
myText = pasteBox matrixPasteKit myTiling


---------------------------------------------------------------------------
-- CUT KITS, MATRICES                                                    --
---------------------------------------------------------------------------

-- A "cut kit" for sized stuff is whatever you need to cut stuff into
-- smaller pieces: left-and-right pieces, or top-and-bottom pieces.

record CutKit (X : Nat -> Nat -> Set) : Set where
  field
    cutLR : (w h wl wr : Nat) -> wl + wr == w ->
            X w h -> X wl h /*/ X wr h
    cutTB : (w h ht hb : Nat) -> ht + hb == h ->
            X w h -> X w ht /*/ X w hb

-- Equip matrices with their CutKit. (1 mark)

matrixCutKit : {C : Set} -> CutKit (Matrix C)
matrixCutKit {C} = record {
    cutLR = \ {.(wl + wr) h wl wr refl css ->
            vunzip (vec (vchop wl) <*> css)} ;
    cutTB = \ {w .(ht + hb) ht hb refl -> vchop ht } }


---------------------------------------------------------------------------
-- HOLES                                                                 --
---------------------------------------------------------------------------

-- We might want to make sure that, whatever other basic tiles are in play,
-- we can have tiles which are "missing", as if we had cut rectangular
-- holes in a piece of paper.

data HoleOr (X : Nat -> Nat -> Set)(w h : Nat) : Set where
  Hole : HoleOr X w h
  [_] : X w h -> HoleOr X w h

-- A HoleOr X is (you guessed it) either a hole or an X.

-- Show that if X has a CutKit, so has HoleOr X. What do you get when you
-- cut up a hole? (1 mark)

holeCutKit : {X : Nat -> Nat -> Set} -> CutKit X -> CutKit (HoleOr X)
holeCutKit {X} ck = record { cutLR = clr ; cutTB = ctb } where
  open CutKit ck
  clr : (w h wl wr : Nat) ->
          wl + wr == w -> HoleOr X w h -> HoleOr X wl h /*/ HoleOr X wr h
  clr w h wl wr wq Hole = Hole , Hole
  clr w h wl wr wq [ x ] with cutLR w h wl wr wq x
  clr w h wl wr wq [ x ] | xl , xr = [ xl ] , [ xr ]
  ctb : (w h ht hb : Nat) ->
          ht + hb == h -> HoleOr X w h -> HoleOr X w ht /*/ HoleOr X w hb
  ctb w h ht hb hq Hole = Hole , Hole
  ctb w h ht hb hq [ x ] with cutTB w h ht hb hq x
  ctb w h ht hb hq [ x ] | xt , xb = [ xt ] , [ xb ]


---------------------------------------------------------------------------
-- A BIT OF FUN                                                          --
---------------------------------------------------------------------------

-- Show that you can turn holes into spaces.

holeSpace : HoleOr _*C*_ []> _*C*_
holeSpace Hole = vec (vec ' ')
holeSpace [ x ] = x

-- Show how to render a tiling made of text or holes as text.

renderHoleOrText : Box (HoleOr _*C*_) []> _*C*_
renderHoleOrText = pasteBox matrixPasteKit o mapBox holeSpace

-- Make a test example and see!

myTest : 8 *C* 6
myTest = renderHoleOrText
  (leri 3 (tobo 4 [ [ vec (vec '*') ] ] 2 [ Hole ] refl)
        5 (tobo 2 [ Hole ] 4 [ [ vec (vec '=') ] ] refl) refl)


---------------------------------------------------------------------------
-- NEXT TIME...                                                          --
---------------------------------------------------------------------------

-- Have a wee think about what you might need to equip Box X with a CutKit.
