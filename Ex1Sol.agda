module Ex1Sol where

open import Ex1Prelude

{----------------------------------------------------------------------------}
{- Name: Conor McSpecimen                                                   -}
{----------------------------------------------------------------------------}

{----------------------------------------------------------------------------}
{- DEADLINE: Week 3 Monday 13 October 23:59 (preferably by BitBucket)       -}
{----------------------------------------------------------------------------}

{-----------------------------------------------------------------------------
TOP TIP: if you have annoyingly many open goals, comment out big chunks of the
file with a multi-line comment a bit like this one.
-----------------------------------------------------------------------------}


{----------------------------------------------------------------------------}
{- 1.1: Tree Sort -}
{----------------------------------------------------------------------------}

-- 1.1.1 implement concatenation for lists

_++_ : {X : Set} -> List X -> List X -> List X
[] ++ ys = ys
x :> xs ++ ys = x :> (xs ++ ys)

infixr 3 _++_

-- a datatype of node-labelled binary trees is given as follows

data Tree (X : Set) : Set where
  leaf : Tree X
  _<[_]>_ : Tree X -> X -> Tree X -> Tree X

{-
data Tree x = Leaf | Node (Tree X) X (Tree X)
Leaf :: Tree x
Node :: Tree x -> x -> Tree x -> Tree x
-}

demoTree : Tree Nat
demoTree = (leaf <[ 3 ]> leaf) <[ 5 ]> leaf

-- 1.1.2 implement the insertion of a number into a tree, ensuring that
-- the numbers in the tree are in increasing order from left to right;
-- make sure to retain duplicates

insertTree : Nat -> Tree Nat -> Tree Nat
insertTree x leaf            = leaf <[ x ]> leaf
insertTree x (l <[ y ]> r) with x <= y  -- or use if_then_else_
insertTree x (l <[ y ]> r) | tt = insertTree x l <[ y ]> r
insertTree x (l <[ y ]> r) | ff = l <[ y ]> insertTree x r

-- 1.1.3 implement the function which takes the elements of a list and
-- builds an ordered tree from them, using insertTree

makeTree : List Nat -> Tree Nat
makeTree [] = leaf
makeTree (x :> xs) = insertTree x (makeTree xs)

-- 1.1.4 implement the function which flattens a tree to a list,
-- using concatenation

flatten : {X : Set} -> Tree X -> List X
flatten leaf           = []
flatten (l <[ x ]> r)  = flatten l ++ x :> flatten r

-- 1.1.5 using the above components, implement a sorting algorithm which
-- works by building a tree and then flattening it

treeSort : List Nat -> List Nat
treeSort = flatten o makeTree

-- 1.1.6 give a collection of unit tests which cover every program line
-- from 1.1.1 to 1.1.5

treeSortTest :  treeSort (1 :> 5 :> 2 :> 4 :> 3 :> [])
                == (1 :> 2 :> 3 :> 4 :> 5 :> [])
treeSortTest = refl

-- 1.1.7 implement a fast version of flatten, taking an accumulating parameter,
-- never using ++. and ensuring that the law
--
-- fastFlatten t xs == flatten t ++ xs
--
-- is true;

{-
fastFlatten : {X : Set} -> Tree X -> (List X -> List X)
fastFlatten leaf xs
  -- = flatten leaf ++ xs                    -- by specification
  -- = [] ++ xs                              -- definition of flatten
  = xs                                       -- definition of ++
fastFlatten (l <[ x ]> r) xs
  -- = flatten (l <[ x ]> r) ++ xs           -- by specification
  -- = (flatten l ++ x :> flatten r) ++ xs   -- definition of flatten
  -- = flatten l ++ x :> flatten r ++ xs     -- ++ is associative
  -- = flatten l ++ x :> fastFlatten r xs    -- by specification
  = fastFlatten l (x :> fastFlatten r xs)    -- by specification
-}

-- for an extra style point, ensure that the accumulating parameter
-- is never given a name in your program

fastFlatten : {X : Set} -> Tree X -> (List X -> List X)
fastFlatten leaf           = id
fastFlatten (l <[ x ]> r)  = (fastFlatten l) o (_:>_ x) o (fastFlatten r)

-- 1.1.8 use fastFlatten to build a fast version of tree sort

fastTreeSort : List Nat -> List Nat
fastTreeSort xs = fastFlatten (makeTree xs) []

-- 1.1.9 again, give unit tests which cover every line of code

fastTreeSortTest :  fastTreeSort (1 :> 5 :> 2 :> 4 :> 3 :> [])
                    == (1 :> 2 :> 3 :> 4 :> 5 :> [])
fastTreeSortTest = refl


{----------------------------------------------------------------------------}
{- 1.2: Shooting Propositional Logic Fish In A Barrel -}
{----------------------------------------------------------------------------}

-- 1.2.1 implement the following operations; try to use only
-- [C-c C-c] and [C-c C-a]

orCommute : {A B : Set} -> A /+/ B -> B /+/ A
orCommute (inl a) = inr a
orCommute (inr b) = inl b

orAbsorbL : {A : Set} -> Zero /+/ A -> A
orAbsorbL (inl ())
orAbsorbL (inr a)   = a

orAbsorbR : {A : Set} -> A /+/ Zero -> A
orAbsorbR (inl a)   = a
orAbsorbR (inr ())

orAssocR : {A B C : Set} -> (A /+/ B) /+/ C -> A /+/ (B /+/ C)
orAssocR (inl (inl a))  = inl a
orAssocR (inl (inr b))  = inr (inl b)
orAssocR (inr c)        = inr (inr c)

orAssocL : {A B C : Set} -> A /+/ (B /+/ C) -> (A /+/ B) /+/ C
orAssocL (inl a)        = inl (inl a)
orAssocL (inr (inl b))  = inl (inr b)
orAssocL (inr (inr c))  = inr c

-- 1.2.2 implement the following operations; try to use only
-- [C-c C-c] and [C-c C-a]

andCommute : {A B : Set} -> A /*/ B -> B /*/ A
andCommute (a , b) = b , a

andAbsorbL : {A : Set} -> A -> One /*/ A
andAbsorbL a = <> , a

andAbsorbR : {A : Set} -> A -> A /*/ One
andAbsorbR a = a , <>

andAssocR : {A B C : Set} -> (A /*/ B) /*/ C -> A /*/ (B /*/ C)
andAssocR ((a , b) , c) = a , (b , c)

andAssocL : {A B C : Set} -> A /*/ (B /*/ C) -> (A /*/ B) /*/ C
andAssocL (a , (b , c)) = (a , b) , c

-- how many times is [C-c C-c] really needed?
--  NEVER, but I'd rather use patterns than projections

-- 1.2.3 implement the following operations; try to use only
-- [C-c C-c] and [C-c C-a]

distribute : {A B C : Set} -> A /*/ (B /+/ C) -> (A /*/ B) /+/ (A /*/ C)
distribute (a , inl b) = inl (a , b)
distribute (a , inr c) = inr (a , c)

factor : {A B C : Set} -> (A /*/ B) /+/ (A /*/ C) -> A /*/ (B /+/ C)
factor (inl (a , b)) = (a , inl b)
factor (inr (a , c)) = (a , inr c)


-- 1.2.4 try to implement the following operations; try to use only
-- [C-c C-c] and [C-c C-a]; at least one of them will prove to be
-- impossible, in which case you should comment it out and explain
-- why it's impossible

Not : Set -> Set
Not X = X -> Zero

deMorgan1 : {A B : Set} -> (Not A /+/ Not B) -> Not (A /*/ B)
deMorgan1 (inl na) (a , b) = na a
deMorgan1 (inr nb) (a , b) = nb b

{-
All I know is that A and B are not both true. That does not tell
me which of the two is false. To give a value in S /+/ T, I must
come off the fence and choose either the inl constructor and give
an S value or the inr constructor with a T. I can't just say "well,
I'm sure it isn't neither of those".

deMorgan2 : {A B : Set} -> Not (A /*/ B) -> (Not A /+/ Not B)
deMorgan2 x = inl (\ a -> {!!})

Closer to the detail, a value of type Not (A /*/ B) is really a
function of type (A /*/ B) -> Zero, so I can never get any actual
data out of it that would help me come off the fence. If I plump
for one side (inl, above), I get offered an A, but that isn't
enough to make use of the hypoothesis.
-}

deMorgan3 : {A B : Set} -> (Not A /*/ Not B) -> Not (A /+/ B)
deMorgan3 (na , nb) (inl a) = na a
deMorgan3 (na , nb) (inr b) = nb b

deMorgan4 : {A B : Set} -> Not (A /+/ B) -> (Not A /*/ Not B)
deMorgan4 n = (\ a -> n (inl a)) , (\ b -> n (inr b))


-- 1.2.5 try to implement the following operations; try to use only
-- [C-c C-c] and [C-c C-a]; at least one of them will prove to be
-- impossible, in which case you should comment it out and explain
-- why it's impossible

dnegI : {X : Set} -> X -> Not (Not X)
dnegI = \ x nx → nx x

{-
dnegE : {X : Set} -> Not (Not X) -> X
dnegE = {!!}

Just because you can't prove that X's don't exist, it doesn't mean
you actually know how to compute an X.
-}

neg321 : {X : Set} -> Not (Not (Not X)) -> Not X
neg321 = λ nnx x → nnx \ nx -> nx x

{-
hamlet : {B : Set} -> B /+/ Not B
hamlet = {!!}

For any proposition (e.g., the halting of a Turing machine), that
we can encode as a Set, hamlet promises to compute whether or not
it has a proof. That's far cleverer than a real computer.
-}

nnHamlet : {B : Set} -> Not (Not (B /+/ Not B))
nnHamlet z = z (inr (\ b -> z (inl b)))

{- Just for fun... -}

DEMORGAN2 : Set1
DEMORGAN2 = {A B : Set} -> Not (A /*/ B) -> (Not A /+/ Not B)

DNEGE : Set1
DNEGE = {X : Set} -> Not (Not X) -> X

HAMLET : Set1  -- also known as "the law of the excluded middle"
HAMLET = {B : Set} -> B /+/ Not B  -- or "tertium non datur" (third (way) not given)

-- and one more variation, Peirce's Law, also a classical truth

PEIRCE : Set1
PEIRCE = {P Q : Set} -> ((P -> Q) -> P) -> P

-- DNEGE, PEIRCE and HAMLET are equivalent

imp1 : DNEGE -> HAMLET
imp1 dne = dne nnHamlet

imp2 : HAMLET -> PEIRCE
imp2 h {P} {Q} pqp with h {P}
imp2 h pqp | inl p   = p
imp2 h pqp | inr np  = pqp (\ p -> magic (np p)) where

imp3 : PEIRCE -> DNEGE
imp3 peirce nnx = peirce (\ nx -> magic (nnx nx))

-- they all imply DEMORGAN2

impDeMorgan : DNEGE -> DEMORGAN2
impDeMorgan dne nab = dne (\ z -> z (inl (\ a -> z (inr (\ b → nab (a , b))))))

-- but (and sorry if I led some of you to believe the opposite)
-- DEMORGAN2 is weaker than the others, because you can only
-- get one bit at at time

{- So, the business of constructing values as evidence for
   propositions corresponds to functional programming in a "total"
   language, but it doesn't give us quite the same logic as the
   Boolean logic we teach you when you start. That logic (aka
   "classical logic") makes "true" some things which do not correspond
   to computations.

   The logic you get here is sometimes called "constructive logic"
   because we ask not "is it true?" but "can you make the evidence?".

   FUN FACT (due to Kurt Goedel): if something is true, classically,
   you can prove that it's not false, constructively.

   WEIRD POSSIBILITY: there are such things as "anti-classical" logics
   which are even more constructive, in which things like HAMLET are
   actually false; these logics build in the idea that the *only*
   truths arise by construction.
-}
