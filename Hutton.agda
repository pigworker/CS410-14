module Hutton where

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

data HExp : Set where
  val : Nat -> HExp
  _+++_ : HExp -> HExp -> HExp

id : {X : Set} -> X -> X
id x = x

eval : HExp -> Nat
eval (val n) = id n
eval (d +++ e) = eval d + eval e

leaves : HExp -> List Nat
leaves (val n) = n :> []
leaves (d +++ e) = {!leaves d ++ leaves e!}

data HCode : Nat -> Nat -> Set where
  PUSH : {i : Nat} -> Nat -> HCode i (suc i)
  ADD : {i : Nat} -> HCode (suc (suc i)) (suc i)
  _SEQ_ : {i j k : Nat} -> HCode i j -> HCode j k -> HCode i k
infixr 3 _SEQ_

data Vec (X : Set) : Nat -> Set where
  [] : Vec X zero
  _,_ : forall {n} -> X -> Vec X n -> Vec X (suc n)

exec : {i j : Nat} -> HCode i j -> Vec Nat i -> Vec Nat j
exec (PUSH x) s = x , s
exec ADD (x , (y , s)) = (y + x) , s
exec (h SEQ k) s = exec k (exec h s)

compile : HExp -> {i : Nat} -> HCode i (suc i)
compile (val n) = PUSH n
compile (d +++ e) = compile d SEQ compile e SEQ ADD
