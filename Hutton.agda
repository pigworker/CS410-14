module Hutton where

open import Ex1Prelude
open import Ex2Prelude


{-
data Nat : Set where
  zero : Nat
  suc : Nat -> Nat

{-# BUILTIN NATURAL Nat #-}


data List (X : Set) : Set where
  []    : List X
  _:>_  : X -> List X -> List X

infixr 5 _:>_

_+_ : Nat -> Nat -> Nat
zero + y = y
suc x + y = suc (x + y)
-}

data HExp : Set where
  val : Nat -> HExp
  _+++_ : HExp -> HExp -> HExp

{-
id : {X : Set} -> X -> X
id x = x
-}

eval : HExp -> Nat
eval (val n) = id n
eval (d +++ e) = eval d + eval e

leaves : HExp -> List Nat
leaves (val n) = n :> []
leaves (d +++ e) = {!leaves d ++ leaves e!}

data HCode : List One -> List One -> Set where
  PUSH : {i : List One} -> Nat -> HCode i (<> :> i)
  ADD : {i : List One} -> HCode (<> :> <> :> i) (<> :> i)
  _-SEQ-_ : {i j k : List One} -> HCode i j -> HCode j k -> HCode i k
infixr 3 _-SEQ-_

{-
data Vec (X : Set) : Nat -> Set where
  [] : Vec X zero
  _,_ : forall {n} -> X -> Vec X n -> Vec X (suc n)
-}

Stk : List One -> Set
Stk xs = All (\ _ -> Nat) xs


exec : {i j : List One} -> HCode i j -> Stk i -> Stk j
exec (PUSH x) s = x , s
exec ADD (x , (y , s)) = (y + x) , s
exec (h -SEQ- k) s = exec k (exec h s)


exec' : (i j : List One) -> HCode i j -> Stk i -> Stk j
exec' i .(<> :> i) (PUSH x) s = x , s
exec' .(<> :> <> :> i) .(<> :> i) (ADD {i}) (y , (x , s)) = (x + y) , s
exec' i j (c -SEQ- c') s = {!exec' _ j c' (exec' i _ c s)!}

{-
compile : HExp -> {i : Nat} -> HCode i (suc i)
compile (val n) = PUSH n
compile (d +++ e) = compile d -SEQ- compile e -SEQ- ADD
-}
