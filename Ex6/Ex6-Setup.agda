module Ex6-Setup where


---------------------------------------------------------------------------
-- NATURAL NUMBERS                                                       --
---------------------------------------------------------------------------

data Nat : Set where
  zero : Nat
  suc : Nat -> Nat
{-# BUILTIN NATURAL Nat #-}

_+_ : Nat -> Nat -> Nat
zero + y = y
suc x + y = suc (x + y)

infixr 5 _+_


---------------------------------------------------------------------------
-- ONE, SIGMA TYPES AND BINARY PRODUCT                                   --
---------------------------------------------------------------------------

record One : Set where constructor <>

record Sg (S : Set)(T : S -> Set) : Set where
  constructor _,_
  field
    fst : S
    snd : T fst
open Sg
_/*/_ : Set -> Set -> Set
S /*/ T = Sg S \ _ -> T
infixr 3 _/*/_
infixr 3 _,_
