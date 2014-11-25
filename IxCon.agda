module IxCon where

open import Ex1Prelude

record Sigma (S : Set)(T : S -> Set) : Set where
  constructor _,_
  field
    fst : S
    snd : T fst
open Sigma public

record _=>_ (I J : Set) : Set1 where
  constructor _<!_/_
  field
    Command   : J -> Set
    Response  : (j : J) -> Command j -> Set
    next      : (j : J)(c : Command j) -> Response j c -> I
open _=>_ public

_-:>_ : {I : Set}(S T : I -> Set) -> Set
S -:> T = {i : _} -> S i -> T i

record FunctorIx (I J : Set) : Set1 where
  field
    FObj : (I -> Set) -> J -> Set
    FArr : {S T : I -> Set} -> (S -:> T) -> FObj S -:> FObj T
open FunctorIx public

[[_]] : {I J : Set} -> I => J -> FunctorIx I J
[[ Command <! Response / next ]] = record
  { FObj = \ Goal j -> Sigma (Command j) \ c -> (r : Response j c) -> Goal (next j c r)
  ; FArr = \ { f {j} (c , k) -> c , (\ r -> f (k r)) }
  }

data Game {I : Set}(C : I => I)(Win : I -> Set)(i : I) : Set where
  win : Win i -> Game C Win i
  <_> : FObj [[ C ]] (Game C Win) i -> Game C Win i

VCon : Set -> (Nat => Nat)
VCon A = (\ { zero -> Zero ; (suc n) -> A })
         <! (\ _ _ -> One)
         / \ { zero    () _
             ; (suc n) a  <> -> n
             }

Vector : Set -> Nat -> Set
Vector A n = Game (VCon A) (\ { zero -> One ; (suc n) -> Zero }) n

vnil : {A : Set} -> Vector A zero
vnil = win <>

vcons : {A : Set}{n : Nat} -> A -> Vector A n -> Vector A (suc n)
vcons a as = < a , (\ { <> -> as }) >

data Bound : Set where
  bot : Bound
  # : Nat -> Bound
  top : Bound

TGame : (Bound /*/ Bound) => (Bound /*/ Bound)
TGame = (\ _ -> Nat) <! (\ _ _ -> Two)
        / (\ { (l , u) n tt -> (l , # n)
             ; (l , u) n ff -> (# n , u)
             })

Le : Nat -> Nat -> Set
Le zero y = One
Le (suc x) zero = Zero
Le (suc x) (suc y) = Le x y

LeB : Bound /*/ Bound -> Set
LeB (bot , _) = One
LeB (# x , # y) = Le x y
LeB (_ , top) = One
LeB _ = Zero

MyTree : Set
MyTree = Game TGame LeB (bot , top)

leaf : {l u : Bound} -> LeB (l , u) -> Game TGame LeB (l , u)
leaf = win

node : {l u : Bound}(n : Nat) -> Game TGame LeB (l , # n) -> Game TGame LeB (# n , u) ->
     Game TGame LeB (l , u)
node n ln nu = < n , (\ { tt -> ln ; ff -> nu }) >
