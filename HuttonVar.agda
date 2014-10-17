module HuttonVar where

open import Ex1Prelude

data HExp (V : Set) : Set where
  var : V -> HExp V
  val : Nat -> HExp V
  _+++_ : HExp V -> HExp V -> HExp V

eval : HExp Zero -> Nat
eval (var ())
eval (val n) = id n
eval (d +++ e) = eval d + eval e

subst : {U V : Set} -> HExp U -> (U -> HExp V) -> HExp V
subst (var x) s = s x
subst (val n) s = val n
subst (d +++ e) s = subst d s +++ subst e s

eval' : {V : Set} -> HExp V -> (V -> Nat) -> Nat
eval' e g = eval (subst e (val o g))

mySubst : Two -> HExp One
mySubst tt = val 5
mySubst ff = var <> +++ val 3

myTest : HExp One
myTest = subst ((val 1 +++ var tt) +++ (var tt +++ var ff)) mySubst

Subst : Set -> Set -> Set
Subst U V = U -> HExp V

idSubst : (V : Set) -> Subst V V
idSubst V = var

compSubst : {U V W : Set} -> Subst V W -> Subst U V -> Subst U W
compSubst f g = \ u -> subst (g u) f

Envy : Set -> Set -> Set
Envy V X = (V -> Nat) -> X

envyRet : {V X : Set} -> X -> Envy V X
envyRet x g = x

_-envyThen-_ : {V X Y : Set} ->
           Envy V X -> (X -> Envy V Y) -> Envy V Y
evx -envyThen- x2evy = \ g -> x2evy (evx g) g

gimme : {V : Set} -> V -> Envy V Nat
gimme v = \ g -> g v

eval2 : {V : Set} -> HExp V -> Envy V Nat
eval2 (var x) = gimme x
eval2 (val n) = envyRet n
eval2 (e +++ e') =
  eval2 e -envyThen- \ v ->
  eval2 e' -envyThen- \ v' ->
  envyRet (v + v')

{-
leaves : HExp -> List Nat
leaves (val n) = n :> []
leaves (d +++ e) = {!leaves d ++ leaves e!}

data HCode : Nat -> Nat -> Set where
  PUSH : {i : Nat} -> Nat -> HCode i (suc i)
  ADD : {i : Nat} -> HCode (suc (suc i)) (suc i)
  _-SEQ-_ : {i j k : Nat} -> HCode i j -> HCode j k -> HCode i k
infixr 3 _-SEQ-_

data Vec (X : Set) : Nat -> Set where
  [] : Vec X zero
  _,_ : forall {n} -> X -> Vec X n -> Vec X (suc n)

exec : {i j : Nat} -> HCode i j -> Vec Nat i -> Vec Nat j
exec (PUSH x) s = x , s
exec ADD (x , (y , s)) = (y + x) , s
exec (h -SEQ- k) s = exec k (exec h s)

exec' : (i j : Nat) -> HCode i j -> Vec Nat i -> Vec Nat j
exec' i .(suc i) (PUSH x) s = x , s
exec' .(suc (suc i)) .(suc i) (ADD {i}) s = {!!}
exec' i j (c -SEQ- c₁) s = {!!}

compile : HExp -> {i : Nat} -> HCode i (suc i)
compile (val n) = PUSH n
compile (d +++ e) = compile d -SEQ- compile e -SEQ- ADD
-}
