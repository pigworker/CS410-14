module HuttonFail where

open import Ex1Prelude

data HExp : Set where
  fail : HExp
  val : Nat -> HExp
  _+++_ : HExp -> HExp -> HExp

data Maybe (X : Set) : Set where
  yes : X -> Maybe X
  no  : Maybe X

eval : HExp -> Maybe Nat
eval fail = no
eval (val x) = yes x
eval (e +++ e') with eval e
eval (e +++ e') | yes x with eval e'
eval (e +++ e') | yes x | yes x' = yes (x + x')
eval (e +++ e') | yes x | no = no
eval (e +++ e') | no = no

_-then-_ : {S T : Set} -> Maybe S -> (S -> Maybe T) -> Maybe T
yes x -then- s2mt = s2mt x
no -then- s2mt = no

eval2 : HExp -> Maybe Nat
eval2 fail = no
eval2 (val x) = yes x
eval2 (e +++ e')  =
  eval2 e -then- \ v ->
  eval2 e' -then- \ v' ->
  yes (v + v')

_-?>_ : Set -> Set -> Set
S -?> T = S -> Maybe T
