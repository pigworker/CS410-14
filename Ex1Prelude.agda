module Ex1Prelude where

data Nat : Set where
  zero  : Nat
  suc   : Nat -> Nat

{-# BUILTIN NATURAL  Nat   #-}
{-# BUILTIN ZERO     zero  #-}
{-# BUILTIN SUC      suc   #-}

_+_ : Nat -> Nat -> Nat
zero   + n  = n
suc m  + n  = suc (m + n)

infixr 5 _+_

data Zero : Set where

magic :  {X : Set} ->
         Zero -> X
magic ()

record One : Set where
  constructor <>

data Two : Set where
  tt ff : Two

if_then_else_ : {X : Set} -> Two -> X -> X -> X
if tt then t else f = t
if ff then t else f = f

_/\_ : Two -> Two -> Two
b1 /\ b2 = if b1 then b2 else ff

_<=_ : Nat -> Nat -> Two
zero   <= y      = tt
suc x  <= zero   = ff
suc x  <= suc y  = x <= y

data List (X : Set) : Set where
  []    : List X
  _:>_  : X -> List X -> List X

infixr 5 _:>_

postulate
      Level : Set
      lzero  : Level
      lsuc   : Level -> Level
      lmax   : Level -> Level -> Level

{-# BUILTIN LEVEL     Level #-}
{-# BUILTIN LEVELZERO lzero  #-}
{-# BUILTIN LEVELSUC  lsuc   #-}
{-# BUILTIN LEVELMAX  lmax   #-}

data _==_ {l}{X : Set l}(x : X) : X -> Set l where
  refl : x == x
infix 4 _==_
{-# BUILTIN EQUALITY _==_ #-}
{-# BUILTIN REFL refl #-}

infixr 1 _/+/_

data _/+/_ (S T : Set) : Set where
  inl  : S  -> S /+/ T
  inr  : T  -> S /+/ T

_<?>_ :   {S T X : Set} ->
          (S -> X) -> (T -> X) ->
          S /+/ T -> X
(f <?> g) (inl s) = f s
(f <?> g) (inr t) = g t

infixr 2 _/*/_

record _/*/_ (S T : Set) : Set where
  constructor _,_
  field
    outl  : S
    outr  : T
open _/*/_ public
infixr 4 _,_

curry :  {S T X : Set} ->
         (S /*/ T -> X) ->
         S -> T -> X
curry f s t = f (s , t)

uncurry :  {S T X : Set} ->
           (S -> T -> X) ->
           S /*/ T -> X
uncurry f (s , t) = f s t

id : {X : Set} -> X -> X
id x = x

_o_ : {A B C : Set} -> (B -> C) -> (A -> B) -> (A -> C)
(f o g) a = f (g a)

infixr 2 _o_
