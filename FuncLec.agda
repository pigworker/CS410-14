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

record Container : Set1 where
  constructor _<!_
  field
    Command : Set                 -- aka Shape
    Response : Command -> Set     -- aka Position
open Container public

record Sigma (S : Set)(T : S -> Set) : Set where
  constructor _,_
  field
    fst : S
    snd : T fst
open Sigma public

_*'_ : Set -> Set -> Set
S *' T = Sigma S \ _ -> T

_+s_ : Set -> Set -> Set
S +s T = Sigma Two \ { tt -> S ; ff -> T }

[[_]] : Container -> Set -> Set
[[ C <! R ]] Y = Sigma C (\ c -> R c -> Y) 

cmap : (F : Container) -> {S T : Set} -> (S -> T) -> [[ F ]] S -> [[ F ]] T
cmap F f (c , k) = c , (\ r -> f (k r))

data GenMo (F : Container)
           (X : Set) : Set where
  ret : X -> GenMo F X
  <_> : [[ F ]] (GenMo F X) -> GenMo F X

_>>=_ : {F : Container}
        {A B : Set} -> GenMo F A -> (A -> GenMo F B)
          -> GenMo F B
ret a      >>= f = f a
< c , k >  >>= f = < c , (\ r -> k r >>= f) >

data Fail : Set where
  fail : Fail

FailR : Fail -> Set
FailR fail = Zero

Maybe : Container
Maybe = Fail <! FailR

! : {F : Container} ->
    (c : Command F) -> GenMo F (Response F c)
! c = < c , ret >

_c+_ : Container -> Container -> Container
(C0 <! R0) c+ (C1 <! R1) = (C0 /+/ C1) <! (\ { (inl c0) -> R0 c0 ; (inr c1) -> R1 c1 })

inC : {F G : Container}{X : Set} -> [[ F ]] X /+/ [[ G ]] X -> [[ F c+ G ]] X
inC (inl (fc , fk)) = inl fc , fk
inC (inr (gc , gk)) = inr gc , gk

_c*_ : Container -> Container -> Container
(C0 <! R0) c* (C1 <! R1) = (C0 /*/ C1) <! (\ { (c0 , c1) -> R0 c0 /+/ R1 c1 })

pairC : {F G : Container}{X : Set} -> [[ F ]] X /*/ [[ G ]] X -> [[ F c* G ]] X
pairC ((fc , fk) , (gc , gk))
  = (fc , gc) , (\ { (inl fr) -> fk fr ; (inr gr) -> gk gr })

kContainer : Kit -> Container
kContainer (kK A) = A <! (\ _ -> Zero)
kContainer kId = One <! (\ _ -> One)
kContainer (k k+ k') = kContainer k c+ kContainer k'
kContainer (k k* k') = kContainer k c* kContainer k'

tail : {X : Set} -> List X -> GenMo Maybe (List X)
tail [] = ! fail >>= (\ ())
tail (x :> xs) = ret xs

try : {X : Set} -> GenMo Maybe X -> X -> X
try (ret x)       _ = x
try < fail , k >  x = x

data State (S : Set) : Set where
  get : State S
  put : S -> State S

StateR : {S : Set} -> State S -> Set
StateR {S} get = S
StateR (put x) = One

StateC : Set -> Container
StateC S = State S <! StateR

c++ : GenMo (StateC Nat) Nat
c++ = ! get >>= \ c -> ! (put (suc c)) >>= \ _ -> ret c

runState : {S X : Set} -> GenMo (StateC S) X ->
  S -> X /*/ S
runState (ret x) s = x , s
runState < get , k > s = runState (k s) s
runState < put s' , k > s = runState (k <>) s'

test : (Nat /*/ Nat) /*/ Nat
test = runState (c++ >>= \ x -> c++ >>= \ y -> ret (x , y)) 41

data Choose : Set where
  choose : Choose

ChooseR : Choose -> Set
ChooseR choose = Two

ChooseC : Container
ChooseC = Choose <! ChooseR

truey : {X : Set} -> GenMo ChooseC X -> X
truey (ret x) = x
truey < choose , k > = truey (k tt)

streamy : {X : Set} ->
          GenMo ChooseC X -> (Nat -> Two) -> X
streamy (ret x) s = x
streamy < choose , k > s = streamy (k (s zero)) (s o suc)

_++_ : {X : Set} -> List X -> List X -> List X
[] ++ ys = ys
x :> xs ++ ys = x :> (xs ++ ys)

infixr 3 _++_

pokemon : {X : Set} -> GenMo ChooseC X -> List X
pokemon (ret x) = x :> []
pokemon < choose , k > = pokemon (k tt) ++ pokemon (k ff)

FailOrChoose : Container
FailOrChoose = Maybe c+ ChooseC

answers : {X : Set} -> GenMo FailOrChoose X -> List X
answers (ret x) = x :> []
answers < inl fail , k > = []
answers < inr choose , k > = answers (k tt) ++ answers (k ff)

data Sender (X : Set) : Set where
  send : X -> Sender X

SenderC : Set -> Container
SenderC X = Sender X <! \ _ -> One

data Receiver : Set where
  receive : Receiver

ReceiverC : Set -> Container
ReceiverC X = Receiver <! \ _ -> X

TransducerC : Set -> Container
TransducerC X = ReceiverC X c+ SenderC X

FlakyTransducerC : Set -> Container
FlakyTransducerC X = Maybe c+ (ReceiverC X c+ SenderC X)

pipe : {X Y : Set} -> GenMo (TransducerC X) One -> GenMo (TransducerC X) Y ->
         GenMo (FlakyTransducerC X) Y
pipe (ret <>) (ret y) = ret y
pipe (ret <>) < inl receive , k > = < inl fail , (\ ()) >
pipe < inl receive , k > q = < inr (inl receive) , (\ x -> pipe (k x) q) >
pipe < inr (send x) , k > (ret y) = ret y
pipe < inr (send x) , k > < inl receive , j > = pipe (k <>) (j x)
pipe p < inr (send x) , k > = < inr (inr (send x)) , (\ _ -> pipe p (k <>)) >
