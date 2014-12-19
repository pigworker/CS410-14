module Lambda where

open import Ex1Prelude

data Ty : Set where
  base : Ty
  _>>_ : Ty -> Ty -> Ty

data Cx : Set where
  C0 : Cx
  _/_ : Cx -> Ty -> Cx
infixl 4 _/_

infixr 3 _<:_
data _<:_ (T : Ty) : Cx -> Set where
  zero : {G : Cx} -> T <: G / T
  suc : {G : Cx}{S : Ty} -> T <: G -> T <: G / S

data Term (G : Cx) : Ty -> Set where
  var : {S : Ty} -> S <: G -> Term G S
  lam : {S T : Ty} -> Term (G / S) T -> Term G (S >> T)
  _$_ : {S T : Ty} -> Term G (S >> T) -> Term G S -> Term G T

myTerm : Term (C0 / base) base
myTerm = lam (var zero $ (var zero $ var (suc zero))) $ lam (var zero)

Semantics : Ty -> Set
Semantics base = Nat
Semantics (S >> T) = Semantics S -> Semantics T

Env : Cx -> Set
Env G = {T : Ty} -> T <: G -> Semantics T

_//_ : {G : Cx}{S : Ty} -> Env G -> Semantics S -> Env (G / S)
(g // s) zero = s
(g // s) (suc x) = g x

eval : {G : Cx}{T : Ty} -> Term G T -> Env G -> Semantics T
eval (var x) g = g x
eval (lam t) g = \ s -> eval t (g // s)
eval (f $ s) g = eval f g (eval s g)

myTest : Nat
myTest = eval myTerm ((\ ()) // 42)

myTerm' : Term (C0 / (base >> base) / base) base
myTerm' = lam (var zero $ (var zero $ var (suc zero))) $
           lam (var (suc (suc zero)) $ (var (suc (suc zero)) $ var zero))

myTest' : Nat
myTest' = eval myTerm' (((\ ()) // suc) // 42)
