module L1 where

data Nat : Set where
  zero : Nat
  suc : Nat -> Nat

{-# BUILTIN NATURAL Nat #-}

-- data Nat = Zero | Suc Nat

_+_ : Nat -> Nat -> Nat
zero + y = y
suc x + y = suc (x + y)

data List (X : Set) : Nat -> Set where
  [] : List X zero
  _,_ : forall {n} -> X -> List X n -> List X (suc n)

_++_ : forall {X m n} -> List X m -> List X n -> List X (m + n)
[] ++ ys = ys
(x₁ , x₂) ++ ys = x₁ , (x₂ ++ ys)
