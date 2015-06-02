module Ex6-5-App-Sol where

open import Ex6-Setup
open import Ex6-1-Vec-Sol
open import Ex6-2-Box-Sol
open import Ex6-3-Cut-Sol
open import Ex6-4-Dis-Sol

mask : {X Y Z : Nat -> Nat -> Set} -> CutKit Y ->
       ({w h : Nat} -> X w h -> Box Y w h -> Box Z w h) ->
       {w h : Nat} ->
       {- front -}     Box X w h ->
       {- back  -}     Box Y w h ->
       {- combined -}  Box Z w h
mask {X}{Y}{Z} ck m = go where
  open CutKit (boxCutKit ck)
  go : {w h : Nat} -> Box X w h -> Box Y w h -> Box Z w h
  go [ x ] yb = m x yb
  go (leri wl xlb wr xrb wq) yb with cutLR _ _ wl wr wq yb
  go (leri wl xlb wr xrb wq) yb | ylb , yrb
    = leri wl (go xlb ylb) wr (go xrb yrb) wq
  go (tobo ht xtb hb xbb hq) yb with cutTB _ _ ht hb hq yb
  go (tobo ht xtb hb xbb hq) yb | ytb , ybb
    = tobo ht (go xtb ytb) hb (go xbb ybb) hq

Update : Nat -> Nat -> Set
Update w h
  =    Two                               -- does it demand repainting?
  /*/  HoleOr (Matrix ColourChar) w h    -- transparent or opaque stuff?

upCutKit : CutKit Update
upCutKit = record
  {  cutLR = \ { w h wl wr wq (b , x) ->
       let y = cutLR w h wl wr wq x in (b , fst y) , (b , snd y) }
  ;  cutTB = \ { w h ht hb hq (b , x) ->
       let y = cutTB w h ht hb hq x in (b , fst y) , (b , snd y) }
  }  where open CutKit (holeCutKit matrixCutKit)

upPaint : {w h : Nat} -> Update w h -> Update w h
upPaint (_ , x) = tt , x

upMask : {w h : Nat} -> Update w h -> Box Update w h -> Box Update w h
upMask (b , [ x ])  ub = [ b , [ x ] ]   -- opaque always wins
upMask (ff , Hole)  ub = ub
upMask (tt , Hole)  ub = mapBox upPaint ub

upLayer : {w h : Nat} -> Box Update w h -> Box Update w h -> Box Update w h
upLayer = mask upCutKit upMask

Selection : Nat -> Nat -> Set
Selection = Box \ _ _ -> Two

select : {w h : Nat} -> Selection w h -> Painting w h -> Box Update w h
select s p = mask (holeCutKit matrixCutKit) (\ b -> mapBox (_,_ b)) s p

data Skippy (X : Set) : Set where
  [] : Skippy X
  _::_ : X -> Skippy X -> Skippy X
  _>_ : Nat -> Skippy X -> Skippy X

_>>_ : {X : Set} -> Nat -> Skippy X -> Skippy X
zero >> xs = xs
m >> (n > xs) = (m + n) > xs
m >> xs = m > xs

_+>+_ : {X : Set} -> Skippy X -> Skippy X -> Skippy X
[] +>+ ys = ys
(x :: xs) +>+ ys = x :: (xs +>+ ys)
(m > xs) +>+ ys = m >> (xs +>+ ys)

Curses : Set
Curses = Skippy (Skippy Action)

skippy : {X : Set} -> Nat -> X -> Skippy X
skippy zero x = []
skippy (suc n) x = x :: skippy n x

skjoin : {X : Set} -> Skippy (Skippy X) -> Skippy X
skjoin [] = []
skjoin (xs :: xss) = xs +>+ skjoin xss
skjoin (_ > xss) = skjoin xss

cursing : {w h : Nat} -> Update w h -> Curses
cursing {w}{h} (tt , Hole)
  = skippy h (fgText black :: bgText white :: skippy w (sendText (' ' :: [])) )
cursing (tt , [ css ]) =
  vecFoldR (\ cs ss ->
    vecFoldR (\ { (f - c / b) s ->
        fgText f :: bgText b :: sendText (c :: []) :: s })
      [] cs :: ss)
    [] css
cursing {w}{h} (ff , _) = h > []

{-# NO_TERMINATION_CHECK #-}
jux : Nat -> Nat -> Curses -> Curses -> Curses
jux l r  []            ys            = []
jux l r  xs            []            = []
jux l r  (zero > xs)   ys            = jux l r xs ys
jux l r  xs            (zero > ys)   = jux l r xs ys
jux l r  (x :: xs)     (y :: ys)     = (x +>+ y) :: jux l r xs ys
jux l r  (x :: xs)     (suc n > ys)  = (x +>+ (r >> [])) :: jux l r xs (n >> ys)
jux l r  (suc m > xs)  (y :: ys)     = ((l >> []) +>+ y) :: jux l r (m >> xs) ys
jux l r  (suc m > xs)  (suc n > ys)  with compare m n
jux l r (suc m > xs) (suc .(m + suc d) > ys) | cutLt d refl x
  = suc m >> jux l r xs (suc d >> ys)
jux l r (suc m > xs) (suc .m > ys) | cutEq refl x
  = suc m >> jux l r xs ys
jux l r (suc .(n + suc d) > xs) (suc n > ys) | cutGt d refl x
  = suc n >> jux l r (suc d >> xs) ys

pasteCurses : PasteKit \ _ _ -> Curses
pasteCurses = record
  {  leriPaste = \ wl wr -> jux wl wr
  ;  toboPaste = \ _ _ -> _+>+_
  }

_:a:_ : Action -> List Action -> List Action
goRowCol _ _ :a: (goRowCol r c :: as) = goRowCol r c :: as
goRowCol r c :a: (move down n :: as) = goRowCol (r + n) c :: as
goRowCol r c :a: (move right n :: as) = goRowCol r (c + n) :: as
move down m :a: (move down n :: as) = move down (m + n) :: as
move right m :a: (move right n :: as) = move right (m + n) :: as
sendText x :a: (sendText y :: as) = sendText (x +-+ y) :: as
a :a: as = a :: as

lineAction : Skippy Action -> List Action
lineAction []         = []
lineAction (a :: as)  = a :a: lineAction as 
lineAction (n > as)   = move right n :a: lineAction as

curseAction : Nat -> Curses -> List Action
curseAction row [] = []
curseAction row (c :: cs) =
  (goRowCol row zero :a: lineAction c) +-+
  curseAction (suc row) cs
curseAction row (n > cs) = curseAction (row + n) cs

uppPaint : {w h : Nat} -> Selection w h -> Painting w h -> List Action
uppPaint s p = curseAction zero
  (pasteBox pasteCurses (mapBox cursing (select s p)))

Upplication : (Nat -> Nat -> Set) -> Set
Upplication S = Application S /*/ (Key -> S []> Selection)


uppHandler : {S : Nat -> Nat -> Set} ->
           Upplication S ->
           Event -> AppState S -> AppState S /**/ List Action
uppHandler (app , sel) (key k) (w , h , s) = (w , h , s') ,
    uppPaint (sel k s) (paintMe app s') +-+ (goRowCol (snd xy) (fst xy) :: [])
  where s' = handleKey app k s ; xy = cursorMe app s'
uppHandler (app , _) (resize w' h') (w , h , s) = (w' , h' , s') , appPaint app s'
  where s' = handleResize app w' h' s

-- Your code turns into a main function, as follows.

uppMain : {S : Nat -> Nat -> Set} -> Upplication S -> S 0 0 -> IO Thud
uppMain upp s = mainLoop (0 , 0 , s) (uppHandler upp) 

selCutKit : CutKit \ _ _ -> Two
selCutKit = record
  {  cutLR = \ _ _ _ _ _ b -> b , b
  ;  cutTB = \ _ _ _ _ _ b -> b , b
  }

cropPadSLR : (w h w' : Nat) -> Selection w h -> Selection w' h
cropPadSLR w h w' p with compare w w'
cropPadSLR w h w' p | cutLt d q _ = leri w p (suc d) [ ff ] q
cropPadSLR w h .w p | cutEq refl _ = p
cropPadSLR w h w' p | cutGt d q _
  = fst (CutKit.cutLR (boxCutKit selCutKit)
         w h w' (suc d) q p)

cropPadSTB : (w h h' : Nat) -> Selection w h -> Selection w h'
cropPadSTB w h h' p with compare h h'
cropPadSTB w h h' p | cutLt d q _ = tobo h p (suc d) [ ff ] q
cropPadSTB w h .h p | cutEq refl _ = p
cropPadSTB w h h' p | cutGt d q _
  = fst (CutKit.cutTB (boxCutKit selCutKit)
         w h h' (suc d) q p)

rectKeySel : Key -> RectState -> Sg Nat \ w -> Sg Nat \ h -> Selection w h
rectKeySel (arrow normal up) (rect gapL rectW (suc gapT) rectH)
  = (gapL + 2 + rectW) , (gapT + 3 + rectH) ,
  tobo gapT [ ff ] (3 + rectH) (leri gapL [ ff ] (2 + rectW) [ tt ] refl) refl
rectKeySel (arrow normal down) (rect gapL rectW gapT rectH)
  = (gapL + 2 + rectW) , (gapT + 3 + rectH) ,
  tobo gapT [ ff ] (3 + rectH) (leri gapL [ ff ] (2 + rectW) [ tt ] refl) refl
rectKeySel (arrow normal left) (rect (suc gapL) rectW gapT rectH)
  = (gapL + 3 + rectW) , (gapT + 2 + rectH) ,
  tobo gapT [ ff ] (2 + rectH) (leri gapL [ ff ] (3 + rectW) [ tt ] refl) refl
rectKeySel (arrow normal right) (rect gapL rectW gapT rectH)
  = (gapL + 3 + rectW) , (gapT + 2 + rectH) ,
  tobo gapT [ ff ] (2 + rectH) (leri gapL [ ff ] (3 + rectW) [ tt ] refl) refl
rectKeySel (arrow shift up) (rect gapL rectW gapT (suc rectH))
  = (gapL + 2 + rectW) , ((gapT + suc rectH) + 2) ,
  tobo (gapT + suc rectH) [ ff ] 2 (leri gapL [ ff ] (2 + rectW) [ tt ] refl) refl
rectKeySel (arrow shift down) (rect gapL rectW gapT rectH)
  = (gapL + 2 + rectW) , ((gapT + suc rectH) + 2) ,
  tobo (gapT + suc rectH) [ ff ] 2 (leri gapL [ ff ] (2 + rectW) [ tt ] refl) refl
rectKeySel (arrow shift left) (rect gapL (suc rectW) gapT rectH)
  = ((gapL + suc rectW) + 2) , (gapT + 2 + rectH) ,
  tobo gapT [ ff ] (2 + rectH) (leri (gapL + suc rectW) [ ff ] 2 [ tt ] refl) refl
rectKeySel (arrow shift right) (rect gapL rectW gapT rectH)
  = ((gapL + suc rectW) + 2) , (gapT + 2 + rectH) ,
  tobo gapT [ ff ] (2 + rectH) (leri (gapL + suc rectW) [ ff ] 2 [ tt ] refl) refl
rectKeySel _ s = 0 , 0 , [ ff ]

rectUpp : Colour -> Upplication \ _ _ -> RectState
rectUpp c = rectApp c , \ k s ->
  cropPadSTB _ _ _ (cropPadSLR _ _ _ (snd (snd (rectKeySel k s))))



frontBackUpp : {S T : Nat -> Nat -> Set} ->
  Upplication S ->
  Upplication T ->
  Upplication \ w h -> (S w h /*/ T w h) /+/ (T w h /*/ S w h)
frontBackUpp (appS , selS) (appT , selT) = frontBack appS appT ,
  (\ { tab (inl (s , t)) ->
        mask (holeCutKit matrixCutKit) see (paintMe appS s) (paintMe appT t)
     ; tab (inr (t , s)) ->
        mask (holeCutKit matrixCutKit) see (paintMe appT t) (paintMe appS s)
     ; k (inl (s , t)) -> selS k s
     ; k (inr (t , s)) -> selT k t
     })
  where
    see : {w h : Nat} -> HoleOr (Matrix ColourChar) w h ->
            Painting w h -> Selection w h
    see Hole  y = [ ff ]
    see [ x ] y = mapBox (\ { Hole -> ff ; [ _ ] -> tt }) y

try : Selection 80 25
try = cropPadSTB _ _ _ (cropPadSLR _ _ _ (snd (snd (rectKeySel (arrow normal up) (rect 10 40 3 15)))))

blah : Painting 80 25
blah = paintMe (rectApp blue) (handleKey (rectApp blue) (arrow normal up) {80}{25} ((rect 10 40 3 15)))

foo : Box (\ _ _ -> Curses) 80 25
foo = mapBox cursing (select try blah)

{- -}
main : IO Thud
main = uppMain (frontBackUpp (rectUpp blue) (rectUpp red))
  (inl (rect 10 40 3 15 , rect 20 40 8 15))
{- -}

{-
data SkipVec (X : Set) : Two -> Nat -> Set where
  []    : {b : Two} -> SkipVec X b zero
  _::_  : {b : Two}{n : Nat} -> X -> SkipVec X tt n -> SkipVec X b (suc n)
  _$>_  : (k : Nat){n : Nat} -> (xs : SkipVec X ff n) -> SkipVec X tt (suc (k + n))

plusAssoc : (a b c : Nat) -> (a + (b + c)) == ((a + b) + c)
plusAssoc zero b c = refl
plusAssoc (suc x) b c = sucResp (plusAssoc x b c)

_$$>_ : {X : Set}(k : Nat){n : Nat} -> SkipVec X tt n -> SkipVec X tt (suc (k + n))
k $$> [] = k $> []
k $$> (x :: xs) = k $> (x :: xs)
k $$> (_$>_ l {n} xs) with k + suc l + n | plusAssoc k (suc l) n
k $$> (l $> xs) | ._ | refl = (k + suc l) $> xs

_+$+_ : {X : Set}{b : Two}{m n : Nat} ->
        SkipVec X b m -> SkipVec X tt n -> SkipVec X tt (m + n)
[] +$+ ys = ys
(x :: xs) +$+ ys = x :: (xs +$+ ys)
_+$+_ {n = n} (_$>_ k {m} xs) ys with ((k + m) + n) | plusAssoc k m n
(k $> xs) +$+ ys | ._ | refl = k $$> (xs +$+ ys)

skip : {X : Set}{n : Nat} -> SkipVec X tt n
skip {X}{zero} = []
skip {X}{suc n} with n + 0 | _$>_ {X} n [] | plusZeroFact n
skip {X} {suc .n} | n | r | refl = r

jux : {X : Set}{b b' : Two}{h h' m n : Nat} -> h == h' ->
        SkipVec (SkipVec X tt m) b h ->
        SkipVec (SkipVec X tt n) b' h' ->
        SkipVec (SkipVec X tt (m + n)) tt h
jux hq [] [] = []
jux () [] (y :: ys)
jux () [] (k $> ys)
jux () (x :: xs) []
jux refl (x :: xs) (y :: ys) = (x +$+ y) :: jux refl xs ys
jux refl (x :: xs) (zero $> ys) = (x +$+ skip) :: jux refl xs ys
jux refl (x :: xs) (suc k $> ys) = (x +$+ skip) :: jux refl xs (k $> ys) 
jux () (k $> xs) []
jux {m = m} refl (zero $> xs) (y :: ys)
  = (skip {n = m} +$+ y) :: jux refl xs ys
jux {m = m} refl (suc k $> xs) (y :: ys)
  = (skip {n = m} +$+ y) :: jux refl (k $> xs) ys
jux hq (k $> xs) (l $> ys) with compare k l
jux hq (k $> xs) (l $> ys) | cutLt d x x₁ = {!!}
jux hq (k $> xs) (.k $> ys) | cutEq refl _ = {!!}
jux hq (k $> xs) (l $> ys) | cutGt d x x₁ = {!!}
-}
