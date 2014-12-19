module NBE where

open import Ex1Prelude

data Ty : Set where
  base : Ty
  _>>_ : Ty -> Ty -> Ty

data Cx : Set where
  C0 : Cx
  _/_ : Cx -> Ty -> Cx
infixl 4 _/_

infixl 3 _<:_
data _<:_ (T : Ty) : Cx -> Set where
  zero : {G : Cx} -> T <: G / T
  suc  : {G : Cx}{S : Ty} -> T <: G -> T <: G / S

data Term (G : Cx) : Ty -> Set where
  lam : {S T : Ty} ->
        Term (G / S) T -> Term G (S >> T)
  var : {S : Ty} -> S <: G -> Term G S
  _$_ : {S T : Ty} -> Term G (S >> T) ->
          Term G S -> Term G T

data Form : Set where normal neutral : Form

data Result (G : Cx) : Form -> Ty -> Set where
  lam : {S T : Ty} ->
        Result (G / S) normal T -> Result G normal (S >> T)
  [_] : {T : Ty} -> Result G neutral T -> Result G normal T
  var : {S : Ty} -> S <: G -> Result G neutral S
  _$_ : {S T : Ty} -> Result G neutral (S >> T) ->
          Result G normal S -> Result G neutral T

Renaming : Cx -> Cx -> Set
Renaming G G' = {T : Ty} -> T <: G -> T <: G'

pushRen : {G G' : Cx}{S : Ty} ->
  Renaming G G' -> Renaming (G / S) (G' / S)
pushRen r zero = zero
pushRen r (suc x) = suc (r x)

Semantics : Cx -> Ty -> Set
Computing : Cx -> Ty -> Set
Semantics G T = Result G neutral T /+/ Computing G T
Computing G base = Zero
Computing G (S >> T) = {G' : Cx} -> Renaming G G' ->
  Semantics G' S -> Semantics G' T

wkRes : {G G' : Cx}{f : Form} -> Renaming G G' -> {T : Ty} ->
        Result G f T -> Result G' f T
wkRes r (lam t) = lam (wkRes (pushRen r) t)
wkRes r [ t ] = [ wkRes r t ]
wkRes r (var x) = var (r x)
wkRes r (f $ s) = wkRes r f $ wkRes r s

wkSem : {G G' : Cx} -> Renaming G G' -> (T : Ty) ->
        Semantics G T -> Semantics G' T
wkSem r T (inl e) = inl (wkRes r e)
wkSem r base (inr ())
wkSem r (S >> T) (inr f) = inr \ r' -> f (r' o r)

Env : Cx -> Cx -> Set
Env G G' = {T : Ty} -> T <: G -> Semantics G' T

wkEnv : {G0 G1 G2 : Cx} -> Renaming G1 G2 -> Env G0 G1 -> Env G0 G2
wkEnv r g x = wkSem r _ (g x)

_//_ : {G G' : Cx}{T : Ty} -> Env G G' -> Semantics G' T ->
  Env (G / T) G'
_//_ g v zero = v
_//_ g v (suc x) = g x

_$$_ : {G : Cx}{S T : Ty} -> Semantics G (S >> T) ->
         Semantics G S -> Semantics G T
stop : {G : Cx}(S : Ty) -> Semantics G S -> Result G normal S

inl e $$ s = inl (e $ stop _ s)
inr f $$ s = f id s

stop base (inl e) = [ e ]
stop base (inr ())
stop (S >> T) v = lam (stop T
  (wkSem suc (S >> T) v $$ inl (var zero)))

semantics : {G G' : Cx}{T : Ty} ->
            ({T : Ty} -> T <: G -> Semantics G' T) ->
            Term G T -> Semantics G' T
semantics g (lam t) = inr \ r s -> semantics (wkEnv r g // s) t
semantics g (var x) = g x
semantics g (f $ s) = semantics g f $$ semantics g s

value : {G : Cx}{T : Ty} -> Term G T -> Result G normal T
value {G}{T} t = stop T (semantics (inl o var) t)

myTerm : Term (C0 / base) base
myTerm = lam (var zero $ (var zero $ var (suc zero))) $ lam (var zero)
