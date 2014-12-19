module CoInd where

open import Ex1Prelude
open import FuncKit
open import IxCon

postulate
  Delay : {a : _} -> Set a -> Set a
  delay : {a : _}{A : Set a} -> A -> Delay A
  force : {a : _}{A : Set a} -> Delay A -> A

{-# BUILTIN INFINITY Delay  #-}
{-# BUILTIN SHARP    delay  #-}
{-# BUILTIN FLAT     force  #-}

data Stream (X : Set) : Set where
  _:>_ : X -> Delay (Stream X) -> Stream X

repeat : {X : Set} -> X -> Stream X
repeat x = x :> delay (repeat x)

natsFrom : Nat -> Stream Nat
natsFrom n = n :> delay (natsFrom (suc n))

takeUpto : {X : Set} -> (n : Nat) -> Stream X -> Vec X n
takeUpto zero xs = []
takeUpto (suc n) (x :> xs) = x , takeUpto n (force xs)

data Codata (k : Kit) : Set where
  [_] : kFun k (Delay (Codata k)) -> Codata k

unfold : {k : Kit}{S : Set} ->
         (S -> kFun k S) ->
         S -> Codata k
unfold {k}{S} f s = [ mapunfoldf k (f s) ] where
  mapunfoldf : (j : Kit) -> kFun j S -> kFun j (Delay (Codata k))
  mapunfoldf (kK A) a = a
  mapunfoldf kId s' = delay (unfold f s')
  mapunfoldf (j k+ j') (inl x) = inl (mapunfoldf j x)
  mapunfoldf (j k+ j') (inr x) = inr (mapunfoldf j' x)
  mapunfoldf (j k* j') (x , y) = mapunfoldf j x , mapunfoldf j' y

STREAM : Set -> Set
STREAM X = Codata (kK X k* kId)

REPEAT : {X : Set} -> X -> STREAM X
REPEAT x = unfold (\ _ -> x , <>) <>

NATSFROM : Nat -> STREAM Nat
NATSFROM n = unfold (\ k -> k , suc k) n

PERHAPS : Set -> Set
PERHAPS X = Codata (kK X k+ kId)

never : {X : Set} -> PERHAPS X
never = unfold (\ s -> inr s) <>

now : {X : Set} -> X -> PERHAPS X
now x = unfold (\ s -> inl x) <>

wait : {X : Set} -> PERHAPS X -> PERHAPS X
wait p = [ inr (delay p) ]

-- PERHAPS is a monad; its bind operator combines the delays in sequence
-- at each step, we're either still working on getting the X, or
-- we're trying to get the Y;
-- we should ensure that the delay for the whole process is the sum of
-- the delays for each part
bind : {X Y : Set} -> PERHAPS X -> (X -> PERHAPS Y) -> PERHAPS Y
bind {X}{Y} px x2py = unfold coalgebra (inl px) where
  workOnY : PERHAPS Y -> Y /+/ (PERHAPS X /+/ PERHAPS Y)
  workOnY [ inl y ] = inl y
  workOnY [ inr py ] = inr (inr (force py))
  workOnX : PERHAPS X -> Y /+/ (PERHAPS X /+/ PERHAPS Y)
  workOnX [ inl x ] = workOnY (x2py x)
  workOnX [ inr px ] = inr (inl (force px))
  coalgebra : (PERHAPS X /+/ PERHAPS Y) -> Y /+/ (PERHAPS X /+/ PERHAPS Y)
  coalgebra (inl px) = workOnX px
  coalgebra (inr py) = workOnY py

myTest : PERHAPS Nat
myTest =  bind (wait (now 2)) \ x ->
          bind (wait (now 3)) \ y ->
          wait (now (x + y))

-- you can test PERHAPS processes with a "boredom threshold"
-- saying how long you're willing to wait; you get either the
-- answer, or a process which has evolved by the indicated
-- number of steps

runFor : {X : Set} -> Nat -> PERHAPS X -> X /+/ PERHAPS X
runFor _    [ inl x ] = inl x
runFor (suc n) [ inr px ] = runFor n (force px)
runFor zero px = inr px

{-
data Game {I : Set}(C : I => I)(Win : I -> Set)(i : I) : Set where
  win : Win i -> Game C Win i
  <_> : FObj [[ C ]] (Game C Win) i -> Game C Win i
-}

data Oppo {I : Set}(C : I => I)(i : I) : Set where
  oppo : ((c : Command C i) ->
             Sigma (Response C i c) \ r ->
                Delay (Oppo C (next C i c r))) ->
         Oppo C i

runGame : {I : Set}{C : I => I}{Win : I -> Set}{i : I} ->
          Game C Win i -> Oppo C i ->
          Sigma I \ i' -> Win i' /*/ Oppo C i'
runGame {i = i'} (win x) o = i' , (x , o)
runGame < c , k > (oppo f) with f c
runGame < c , k > (oppo f) | r , o = runGame (k r) (force o)
