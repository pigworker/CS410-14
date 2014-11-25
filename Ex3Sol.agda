module Ex3Sol where

open import Ex1Prelude
open import FuncKit

{- 3.1 Numbers in the Kit -}

{- We can define the type of natural numbers using the tools
   from the functor kit like this: -}

kNat : Kit
kNat = kK One k+ kId

NAT : Set
NAT = Data kNat

-- Define the function which sends "ordinary" numbers to
-- the corresponding kit-encoded numbers.

Nat2NAT : Nat -> NAT
Nat2NAT zero = [ inl <> ]
Nat2NAT (suc n) = [ inr (Nat2NAT n) ]

-- Use fold to define the function which sends them back.

NAT2Nat : NAT -> Nat
NAT2Nat = fold (kK One k+ kId) (\
  { (inl <>) -> zero
  ; (inr NAT2Nat_n)  -> suc NAT2Nat_n
  })

-- Show that you get the "round trip" property (by writing
-- recursive functions that use rewrite.

Nat2NAT2Nat : NAT2Nat o Nat2NAT =^= id
Nat2NAT2Nat zero = refl
Nat2NAT2Nat (suc n) rewrite Nat2NAT2Nat n = refl

NAT2Nat2NAT : Nat2NAT o NAT2Nat =^= id
NAT2Nat2NAT [ inl <> ] = refl
NAT2Nat2NAT [ inr x ] rewrite NAT2Nat2NAT x = refl


{- 3.2 Lists in the Kit -}

-- find the code which gives you lists with a given element
-- type (note that the kId constructor marks the place for
-- recursive *sublists* not for list elements

kLIST : Set -> Kit
kLIST A = kK One k+ (kK A k* kId)

LIST : Set -> Set
LIST A = Data (kLIST A)

-- define nil and cons for your lists

nil : {A : Set} -> LIST A
nil = [ inl <> ]

cons : {A : Set} -> A -> LIST A -> LIST A
cons a as = [ inr (a , as) ]

-- use fold to define concatenation

conc : {A : Set} -> LIST A -> LIST A -> LIST A
conc {A} xs ys = fold (kLIST A)
   (\ { (inl <>) -> ys
      ; (inr (a , conc_as_ys)) -> cons a conc_as_ys
      })
   xs

-- prove the following (the yellow bits should disappear when
-- you define kLIST);
-- maddeningly, "rewrite" won't do it, but this piece of kit
-- (which is like a manual version of rewrite) will do it

cong : {S T : Set}(f : S -> T){a b : S} -> a == b -> f a == f b
cong f refl = refl

concNil : {A : Set}(as : LIST A) -> conc as nil == as
concNil [ inl <> ] = refl
concNil [ inr (a , as) ] = cong (cons a) (concNil as)

concAssoc : {A : Set}(as bs cs : LIST A) ->
            conc (conc as bs) cs == conc as (conc bs cs)
concAssoc [ inl <> ] bs cs = refl
concAssoc [ inr (a , as) ] bs cs = cong (cons a) (concAssoc as bs cs)


{- 3.3 Trees in the Kit -}

-- give a kit code for binary trees with unlabelled leaves
-- and nodes labelled with elements of NAT

kTREE : Kit
kTREE = kK One k+ (kId k* (kK NAT k* kId))

TREE : Set
TREE = Data kTREE

-- give the constructors

leaf : TREE
leaf = [ inl <> ]

node : TREE -> NAT -> TREE -> TREE
node l n r = [ inr (l , n , r) ]

-- implement flattening (slow flattening is ok) as a fold

flatten : TREE -> LIST NAT
flatten = fold kTREE (\
  { (inl <>) -> nil
  ; (inr (flatten_l , n , flatten_r)) -> conc flatten_l (cons n flatten_r)
  })


{- 3.4 "rec" from "fold" -}

-- The recursor is a variation on the theme of fold, but you
-- get a wee bit more information at each step. In particular,
-- in each recursive position, you get the original substructure
-- *as well as* the value that is computed from it.

rec : (k : Kit){X : Set} ->

      (kFun k (Data k /*/ X) -> X) ->
--             ^^^^^^     ^
--       substructure   value

      Data k -> X

-- Demonstrate that rec is no more powerful than fold by constructing
-- rec from fold. The trouble is that fold throws away the original
-- substructures. But you can compensate by computing something extra
-- as well as the value you actually want.

rec k {X} f d = outr (fold k {Data k /*/ X}
                 (\ kdx -> [ kitMap k outl kdx ] , f kdx) d)


-- use rec to implement "insList", being the function which inserts
-- a number in a list, such that if the input list is in increasing
-- order, so is the output list; you may assume that "lessEq" exists

lessEq : NAT -> NAT -> Two

insList : NAT -> LIST NAT -> LIST NAT
insList n = rec (kLIST NAT) (\
  { (inl <>) -> cons n nil
  ; (inr (a , (as , insList_n_as))) ->
      if lessEq n a
        then cons n (cons a as)
        else cons a insList_n_as
  })

-- justify the assumption by defining "lessEq"; do not use explicit
-- recursion; do use "rec kNat" once more to take numbers apart

lessEq x y = rec kNat {NAT -> Two}
  (\ { (inl <>) -> \ y -> {- lessEq zero y -} tt
     ; (inr (x , lessEq_x)) -> rec kNat (\
       { (inl <>) -> {- lessEq (suc x) zero -} ff
       ; (inr (y , lessEq_[suc_x]_y)) -> {- lessEq (suc x) (suc y) -} lessEq_x y
       })
     })
  x y

-- implement insertion for binary search trees using "rec"

insTree : NAT -> TREE -> TREE
insTree n = rec kTREE (\
  { (inl <>) -> node leaf n leaf
  ; (inr ((l , insTree_n_l) , y , (r , insTree_n_r))) ->
      if lessEq n y then node insTree_n_l y r else node l y insTree_n_r
  })
