module FuncLec where

open import Ex1Prelude

_=^=_ : {S T : Set}(f g : S -> T) -> Set
f =^= g = (s : _) -> f s == g s
infixl 2 _=^=_

map : {S T : Set} -> (S -> T) -> (List S -> List T)
map f [] = []
map f (s :> ss) = f s :> map f ss

mapId : {S : Set} -> map (id {S}) =^= id {List S}
mapId [] = refl
mapId (x :> ss) rewrite mapId ss = refl

mapComp : {R S T : Set}(f : S -> T)(g : R -> S) ->
          map f o map g =^= map (f o g)
mapComp f g [] = refl
mapComp f g (x :> ss) rewrite mapComp f g ss = refl

_>=_ : Nat -> Nat -> Set
m >= zero = One
zero >= suc n = Zero
suc m >= suc n = m >= n

geRefl : (n : Nat) -> n >= n
geRefl zero = <>
geRefl (suc x) = geRefl x

geTrans : (l m n : Nat) -> m >= n -> l >= m -> l >= n
geTrans l zero zero mn lm = <>
geTrans zero zero (suc x) mn lm = mn
geTrans (suc x) zero (suc zero) mn lm = <>
geTrans (suc x) zero (suc (suc x₁)) mn lm = geTrans x zero (suc x₁) mn <>
geTrans l (suc x) zero mn lm = <>
geTrans zero (suc x) (suc x₁) mn lm = lm
geTrans (suc x) (suc x₁) (suc x₂) mn lm = geTrans x x₁ x₂ mn lm


data Vec (X : Set) : Nat -> Set where
  [] : Vec X zero
  _,_ : forall {n} -> X -> Vec X n -> Vec X (suc n)

take : {X : Set}(m n : Nat) -> m >= n -> (Vec X m -> Vec X n)
take m zero mn xs = []
take .0 (suc n) () []
take ._ (suc n) mn (x , xs) = x , take _ n mn xs

data Tree (X : Set) : Set where
  leaf : Tree X
  node : Tree X -> X -> Tree X -> Tree X

treeMap : {S T : Set} -> (S -> T) -> (Tree S -> Tree T)
treeMap f leaf = leaf
treeMap f (node l s r) = node (treeMap f l) (f s) (treeMap f r)

From : Set -> Set -> Set
From A X = A -> X
fromMap : {A S T : Set} -> (S -> T) -> ((From A) S -> (From A) T)
fromMap f g = f o g

{-
To : Set -> Set -> Set
To B X = X -> B
toMap : {B S T : Set} -> (S -> T) -> ((To B) S -> (To B) T)
toMap {B}{S}{T} f g = {!!}
-}

NotNot : Set -> Set
NotNot X = (X -> Zero) -> Zero

nnMap : {S T : Set} -> (S -> T) -> (NotNot S -> NotNot T)
nnMap f nns = \ nt -> nns (\ s -> nt (f s))

good : Zero -> One
good ()
{-
bad : One -> Zero
bad = toMap good id
-}

Id : Set -> Set
Id X = X
idMap : {S T : Set} -> (S -> T) -> (Id S -> Id T)
idMap {S}{T} = id

Product : (F G : Set -> Set) -> Set -> Set
Product F G X = F X /*/ G X
prodMap :  {F G : Set -> Set} -> 
           ({S T : Set} -> (S -> T) -> (F S -> F T)) ->
           ({S T : Set} -> (S -> T) -> (G S -> G T)) ->
            ({S T : Set} -> (S -> T) -> ((Product F G) S -> (Product F G) T))
prodMap fmap gmap h (fs , gs) = fmap h fs , gmap h gs

ex1 : Product Id Id Nat
ex1 = 6 , 7

ex2 : Product Id Id Two
ex2 = prodMap idMap idMap (\ n -> n <= 6) ex1

Sum : (F G : Set -> Set) -> Set -> Set
Sum F G X = F X /+/ G X
sumMap :  {F G : Set -> Set} -> 
           ({S T : Set} -> (S -> T) -> (F S -> F T)) ->
           ({S T : Set} -> (S -> T) -> (G S -> G T)) ->
            ({S T : Set} -> (S -> T) -> ((Sum F G) S -> (Sum F G) T))
sumMap fmap gmap h (inl fs) = inl (fmap h fs)
sumMap fmap gmap h (inr gs) = inr (gmap h gs)

ex3 : Sum (Product Id Id) Id Two
ex3 = inl (tt , ff)

K : Set -> Set -> Set
K A X = A

kMap : {A S T : Set} -> (S -> T) -> (K A S -> K A T)
kMap f a = a

Mystery : Set -> Set
Mystery = Sum (K One) Id

mystery : Mystery Two
mystery = inl <>

data Kit : Set1 where
  kK : Set -> Kit
  kId : Kit
  _k+_ : Kit -> Kit -> Kit
  _k*_ : Kit -> Kit -> Kit

kFun : Kit -> (Set -> Set)
kFun (kK A)    X = A
kFun kId       X = X
kFun (f k+ g)  X = kFun f X /+/ kFun g X
kFun (f k* g)  X = kFun f X /*/ kFun g X

kitMap : (k : Kit){S T : Set} -> (S -> T) -> kFun k S -> kFun k T
kitMap (kK A) h a = a
kitMap kId h s = h s
kitMap (f k+ g) h (inl fs) = inl (kitMap f h fs)
kitMap (f k+ g) h (inr gs) = inr (kitMap g h gs)
kitMap (f k* g) h (fs , gs) = kitMap f h fs , kitMap g h gs

data Data (k : Kit) : Set where
  [_] : kFun k (Data k) -> Data k

fold : (k : Kit){X : Set} -> (kFun k X -> X) -> Data k -> X
fold k {X} f [ kd ] = f (kitMapFold k kd) where
  kitMapFold : (j : Kit) -> kFun j (Data k) -> kFun j X
  kitMapFold (kK A) a = a
  kitMapFold kId s = fold k f s
  kitMapFold (f k+ g) (inl fs) = inl (kitMapFold f fs)
  kitMapFold (f k+ g) (inr gs) = inr (kitMapFold g gs)
  kitMapFold (f k* g) (fs , gs) = kitMapFold f fs , kitMapFold g gs

kMaybe : Kit
kMaybe = kK One k+ kId

pattern ze = inl <>
pattern su n = inr n

NAT = Data kMaybe
exNat : NAT
exNat = [ su [ su [ ze ] ] ]

_+'_ : NAT -> NAT -> NAT
x +' y = fold kMaybe p x where
  p : kFun kMaybe NAT -> NAT
  p ze       = y
  p (su x+y) = [ su x+y ]


{-
[ ze ] +' y = y
[ su x ] +' y = [ su (x +' y) ]
-}


kT : Kit
kT = kK One k+ (kId k* kId)

exTree : Data kT
exTree = [ inl <> ]

FreeMo : Kit -> Set -> Set
FreeMo k X = Data (k k+ kK X)

return : (k : Kit) -> {A : Set} -> A -> FreeMo k A
return k a = [ inr a ]

bind : (k : Kit){A B : Set} ->
        FreeMo k A ->
        (A -> FreeMo k B) ->
        FreeMo k B
bind k {A} ma a2mb = fold (k k+ kK A)
   (\ { (inl kb) -> [ inl kb ]
      ; (inr a) -> a2mb a 
      }) ma

Error : Set -> Set -> Set
Error E = FreeMo (kK E)

kBitWrite : Kit
kBitWrite = kK Two k* kId

kBitRead : Kit
kBitRead = kId k* kId

RWBit : Set -> Set
RWBit = FreeMo (kBitWrite k+ kBitRead)

run : {X : Set} -> RWBit X ->
       List Two -> List Two /*/ Error One X
run [ inl (inl (b , p)) ] bs with run p bs
run [ inl (inl (b , p)) ] bs | bs' , ex
  = (b :> bs') , ex
run [ inl (inr (tp , fp)) ] [] = [] , [ inl <> ]
run [ inl (inr (tp , fp)) ] (tt :> bs)
  = run tp bs
run [ inl (inr (tp , fp)) ] (ff :> bs)
  = run fp bs
run [ inr x ] bs = [] , [ inr x ]

data GenMo (C : Set)
           (R : C -> Set)
           (X : Set) : Set where
  ret : X -> GenMo C R X
  _?-_ : (c : C)(k : R c -> GenMo C R X) -> GenMo C R X

_>>=_ : {C : Set}{R : C -> Set}
        {A B : Set} -> GenMo C R A -> (A -> GenMo C R B)
          -> GenMo C R B
ret a >>= f = f a
(c ?- k) >>= f = c ?- (\ r -> k r >>= f)
