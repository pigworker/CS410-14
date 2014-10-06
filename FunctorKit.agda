module FunctorKit where

open import BasicPrelude

record Functor (F : Set{-type of elements-} -> Set{-type of structures-})
  : Set1 where
  field

    map : {S T : Set} -> (S -> T)    {- operation on elements-} 
                      -> F S -> F T  {- operation on structures -}

    mapI : {X : Set}(xs : F X) -> map id xs == xs
    mapC : {R S T : Set}(f : S -> T)(g : R -> S)(xs : F R) ->
              map f (map g xs) == map (f o g) xs

open Functor public

ListFunctor : Functor List
ListFunctor = record { map = mapList; mapI = mapIList; mapC = mapCList } where

  mapList : {S T : Set} -> (S -> T) -> List S -> List T
  mapList f [] = []
  mapList f (x :> xs) = f x :> mapList f xs

  mapIList : {X : Set} (xs : List X) -> mapList id xs == xs
  mapIList [] = refl
  mapIList (x :> xs) rewrite mapIList xs = refl

  mapCList : {R S T : Set} (f : S -> T) (g : R -> S) (xs : List R) ->
               mapList f (mapList g xs) == mapList (f o g) xs
  mapCList f g [] = refl
  mapCList f g (x :> xs) rewrite mapCList f g xs = refl

Label : Set -> (Set -> Set)  -- no elements
Label A X = A

LabelFunctor : (A : Set) -> Functor (Label A)
LabelFunctor A = record
  { map = \ _ a -> a; mapI = \ _ -> refl; mapC = \ _ _ _ -> refl }

Id : Set -> Set  -- one element
Id X = X

IdFunctor : Functor Id
IdFunctor = record {
              map = id;
              mapI = \ _ -> refl;
              mapC = \ _ _ _ -> refl }

PairFunctor : {F G : Set -> Set} -> Functor F -> Functor G ->
              Functor \ X -> F X /*/ G X
PairFunctor {F}{G} FunF FunG = record { map = mapP ; mapI = mapPI ; mapC = mapPC }
  where
  mapP : {S T : Set} -> (S -> T) -> (F S /*/ G S) -> (F T /*/ G T)
  mapP f (xF , xG) = map FunF f xF , map FunG f xG
  mapPI : forall {X : Set}(xs : F X /*/ G X) -> mapP id xs == xs
  mapPI (xF , xG) rewrite mapI FunF xF | mapI FunG xG = refl
  mapPC : {R S T : Set} (f : S -> T) (g : R -> S) (xs : F R /*/ G R) ->
          mapP f (mapP g xs) == mapP (f o g) xs
  mapPC f g (xF , xG) rewrite mapC FunF f g xF | mapC FunG f g xG = refl

SumFunctor : {F G : Set -> Set} -> Functor F -> Functor G ->
              Functor \ X -> F X /+/ G X
SumFunctor {F}{G} FunF FunG = record { map = mapS ; mapI = mapSI; mapC = mapSC }
  where
  mapS : {S T : Set} -> (S -> T) -> (F S /+/ G S) -> (F T /+/ G T)
  mapS f (inl xF) = inl (map FunF f xF)
  mapS f (inr xG) = inr (map FunG f xG)
  mapSI : {X : Set} (xs : F X /+/ G X) -> mapS id xs == xs
  mapSI (inl xF) rewrite mapI FunF xF = refl
  mapSI (inr xG) rewrite mapI FunG xG = refl
  mapSC : {R S T : Set} (f : S -> T) (g : R -> S) (xs : F R /+/ G R) ->
           mapS f (mapS g xs) == mapS (f o g) xs
  mapSC f g (inl xF) rewrite mapC FunF f g xF = refl
  mapSC f g (inr xG) rewrite mapC FunG f g xG = refl

data Kit : Set1 where
  zeroK oneK : Kit
  idK : Kit
  dataK : Kit -> Kit
  _*K_ : Kit -> Kit -> Kit
  _+K_ : Kit -> Kit -> Kit

infixr 4 _+K_
infixr 5 _*K_

Fun : Kit -> Set -> Set

data DATA (f : Kit) : Set where
  [_] : Fun f (DATA f) -> DATA f

Fun zeroK X = Zero
Fun oneK X = One
Fun idK X = Id X
Fun (dataK f) X = DATA f
Fun (f *K g) X = Fun f X /*/ Fun g X
Fun (f +K g) X = Fun f X /+/ Fun g X

FunFunctor : (f : Kit) -> Functor (Fun f)
FunFunctor zeroK = LabelFunctor Zero
FunFunctor oneK = LabelFunctor One
FunFunctor (dataK f) = LabelFunctor (DATA f)
FunFunctor idK = IdFunctor
FunFunctor (f *K g) = PairFunctor (FunFunctor f) (FunFunctor g)
FunFunctor (f +K g) = SumFunctor (FunFunctor f) (FunFunctor g)

twoK : Kit
twoK = oneK +K oneK

pattern true =  [ inl <> ]
pattern false =  [ inr <> ]

natK : Kit
natK = oneK +K idK

pattern ze =  [ inl <> ]
pattern su n = [ inr n ]

toNatK : Nat -> DATA natK
toNatK zero = ze
toNatK (suc n) = su (toNatK n)

listK : Kit -> Kit
listK f = oneK +K (dataK f *K idK)

pattern nil = [ inl <> ]
pattern cons x xs = [ inr (x , xs) ]

treeK : Kit -> Kit
treeK f = oneK +K (idK *K dataK f *K idK)

leaf' : {f : Kit} -> DATA (treeK f)
pattern leaf = [ inl <> ]
leaf' = leaf
pattern node l x r = [ inr (l , x , r) ]
node' : {f : Kit} ->  DATA (treeK f) -> DATA f -> DATA (treeK f) -> DATA (treeK f)
node' l x r = node l x r

leK : DATA natK -> DATA natK -> DATA twoK
leK ze n = true
leK (su m) ze = false
leK (su m) (su n) = leK m n


{-

noLabels : (f : Kit) -> DATA f -> Zero

noLabels' : (r f : Kit) -> Fun f (DATA r) -> Zero
noLabels' r idK x = noLabels r x
noLabels' r (f *K g) (xf , xg) = noLabels' r f xf
noLabels' r (f +K g) (inl x) = noLabels' r f x
noLabels' r (f +K g) (inr x) = noLabels' r g x

noLabels f [ x ] = noLabels' f f x
-}

{-
mysteryf : Kit
mysteryf = (labelK One) +K idK

MYSTERY : Set
MYSTERY = DATA mysteryf

{- -- ask Agsy to try making some elements of the MYSTERY type
mystery : MYSTERY
mystery = {!-l!}  -- do [C-c C-a] with -l in the braces
-}

-- Aha! It's a copy of the natural numbers!

zeroM : MYSTERY
zeroM = [ inl <> ]

sucM : MYSTERY -> MYSTERY
sucM n = [ inr n ]

-- Now how about this...

treef : Set -> Kit
treef X = labelK One   +K   idK *K labelK X *K idK

pattern leaf = [ inl <> ]
pattern node l x r = [ inr (l , x , r) ]

flatten : {X : Set} -> DATA (treef X) -> List X
flatten leaf          = []
flatten (node l x r)  = flatten l ++ x :> flatten r

insert : Nat -> DATA (treef Nat) -> DATA (treef Nat)
insert n leaf = node leaf n leaf
insert n (node l x r) with n <= x 
insert n (node l x r) | tt = node (insert n l) x r
insert n (node l x r) | ff = node l x (insert n r)

StuffINeed : Kit -> Set
StuffINeed (labelK A) = A -> A -> Two
StuffINeed idK = One
StuffINeed (f *K g) = StuffINeed f /*/ StuffINeed g
StuffINeed (f +K g) = StuffINeed f /*/ StuffINeed g
-}

kitEq : {f : Kit} -> DATA f -> DATA f -> DATA twoK

nodeEq : (r f : Kit) -> Fun f (DATA r) -> Fun f (DATA r) -> DATA twoK
nodeEq r zeroK () y
nodeEq r oneK <> <> = true
nodeEq r idK x y = kitEq x y  -- here's where r is used
nodeEq r (dataK f) x y = kitEq x y
nodeEq r (f *K g) (xf , xg) (yf , yg) with nodeEq r f xf yf | nodeEq r g xg yg
nodeEq r (f *K g) (xf , xg) (yf , yg) | true | true  = true
nodeEq r (f *K g) (xf , xg) (yf , yg) | qf | qg  = false
nodeEq r (f +K g) (inl x) (inl y) = nodeEq r f x y
nodeEq r (f +K g) (inl x) (inr y) = false
nodeEq r (f +K g) (inr x) (inl y) = false
nodeEq r (f +K g) (inr x) (inr y) = nodeEq r g x y

kitEq {f} [ x ] [ y ] = nodeEq f f x y

delOne : Kit -> Kit
delOne zeroK = zeroK
delOne oneK = zeroK
delOne idK = oneK
delOne (dataK f) = zeroK
delOne (f *K g) = delOne f *K g  +K  f *K delOne g
delOne (f +K g) = delOne f +K delOne g


{-
nodeEq r sr (labelK A) s a a' = s a a'
nodeEq r sr idK s x y = kitEq sr x y
nodeEq r sr (f *K g) (sf , sg) (xf , xg) (yf , yg)
   with nodeEq r sr f sf xf yf | nodeEq r sr g sg xg yg
nodeEq r sr (f *K g) (sf , sg) (xf , xg) (yf , yg) | tt | tt  = tt
nodeEq r sr (f *K g) (sf , sg) (xf , xg) (yf , yg) | qf | qg  = ff
nodeEq r sr (f +K g) s (inl xf) (inl yf) = nodeEq r sr f (outl s) xf yf
nodeEq r sr (f +K g) s (inl xf) (inr yg) = ff
nodeEq r sr (f +K g) s (inr xg) (inl yf) = ff
nodeEq r sr (f +K g) s (inr xg) (inr yg) = nodeEq r sr g (outr s) xg yg

kitEq {f} s [ x ] [ y ] = nodeEq f s f s x y

myGo : Two
myGo = kitEq ((\ _ _ -> tt) , _) (sucM (sucM (sucM zeroM))) (sucM (sucM (sucM zeroM)))
-}