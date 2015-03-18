#CS410-14#

This repository contains the materials for CS410 Advanced Functional
Programming in the 2014-15 session. The class runs through semesters
1 and 2, with most of its teaching and assessment activity completed
already in semester 1. Accordingly, for ease of reference, this page
includes the exercises so far, and is intended to be a reasonably
self-contained account of how the class works.

CS410 is assessed entirely by coursework. It runs for all 15 weeks of
semester 1, in which there are 5 exercises, each lasting 3 weeks and
worth 15% of the class score, then it suspends for the 10 "project"
weeks of semester 2, before resuming in the last 5 weeks of semester 2
for a single "capstone" exercise worth 25% of the class score.

The class is about programming in the advanced functional language,
Agda. Teaching is largely show-and-tell: I introduce concepts and
illustrate them with "live programming" in the classroom. Agda
supports development by interactive type-directed refinement---filling
in "holes".  Exercises thus consist of incomplete programs, to be
finished appropriately by each student. They are distributed via this
public code repository on GitHub. The students work in lab sessions
which I supervise: often, the discussion which breaks out in the lab
once they are hands-on with a problem is how the real learning
happens. The students each have their own private branch of the
repository on BitBucket, to which they invite me as a "collaborator"
whilst keeping everyone else out. After each deadline, the students
make individual appointments to see me, where we work through their
code. I quiz them about it, grade it, and issue oral feedback.

This is a challenging class, but the students are bright and
enthusiastic for a challenge, having done well at the corresponding
third year Haskell class. The precise direction and choice of material
is informed by the progress the class makes as we go. This year, I was
pleasantly surprised by their willingness to engage with some quite
deep concepts.

The semester 1 exercises were as follows.

1. *an introduction to propositions-as-types and programming by
   refinement* This exercise is as much an orientation in driving
   the tools as it is an introduction to the basic concepts.
2. *a study of a simple interpreter, once with monadic error
   propagation, and again with a typesafe representation ensuring
   error-free execution* This exercise introduces basic techniques of
   programming with monads, but also the idea of imposing strong
   invariants by indexing datatypes.
3. *a study of polynomial datatypes, and their generic recursion
   schemes* This exercise revisits some examples from exercise 1, but
   encourages the students to recognize the types and programs as
   instances of a general scheme.
4. *a study of interaction with an external environment* The students
   develop the basic building blocks of command-response systems
   contingent on some sort of state. They develop an approach to
   file-handling which is statically guaranteed to be safe, and then
   implement a file-copying program within that discipline.
5. *a text editor with verified update* A mostly dysfunctional text
   editor is provided. The students repair it and extend it with
   useful behaviour by implementing the behaviour of keystrokes,
   estimating the severity of the change each makes. They are obliged
   to prove that they overestimate change, thus ensuring that
   necessary updates happen.

The exercise files, mark schemes and specimen solutions for exercises
1-4 are included below. For exercise 5, the main exercise file and the
mark scheme is included.

At time of writing, exercise 6 is under construction. It will be
issued to students at the start of the Easter break, giving them some
chance of a head start. It will amount to

* building a basic library for working with lists indexed by length (5
  marks)
* developing the theory of rectangular tilings indexed by length and
  height: these have monadic structure, and when you include
  transparent tiles, a monoidal "overlaying" structure, with a clear
  visual intuition (10 marks)
* developing a simple window manager for rectangular overlapping
  windows, runnning in a shell: what sort of content goes in the
  windows will leave room for creativity (10 marks)

The exercises tend to be quite structured, designed to promote the
grasping of key concepts. How far they get depends on their ability
and determination to struggle to an understanding. They get out what
they put in.

Below are the relevant files for the first 5 exercises.

##Exercise 1##

**problem file**

```
module Ex1 where

open import Ex1Prelude

{----------------------------------------------------------------------------}
{- Name: -}
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
xs ++ ys = {!!}

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
demoTree = ({!!} <[ 3 ]> {!!}) <[ 5 ]> {!!}

-- 1.1.2 implement the insertion of a number into a tree, ensuring that
-- the numbers in the tree are in increasing order from left to right;
-- make sure to retain duplicates

insertTree : Nat -> Tree Nat -> Tree Nat
insertTree x t = {!!}

-- 1.1.3 implement the function which takes the elements of a list and
-- builds an ordered tree from them, using insertTree

makeTree : List Nat -> Tree Nat
makeTree xs = {!!}

-- 1.1.4 implement the function which flattens a tree to a list,
-- using concatenation

flatten : {X : Set} -> Tree X -> List X
flatten t = {!!}

-- 1.1.5 using the above components, implement a sorting algorithm which
-- works by building a tree and then flattening it

treeSort : List Nat -> List Nat
treeSort = {!!}

-- 1.1.6 give a collection of unit tests which cover every program line
-- from 1.1.1 to 1.1.5

-- 1.1.7 implement a fast version of flatten, taking an accumulating parameter,
-- never using ++. and ensuring that the law
--
-- fastFlatten t xs == flatten t ++ xs
--
-- is true; for an extra style point, ensure that the accumulating parameter
-- is never given a name in your program

fastFlatten : {X : Set} -> Tree X -> List X -> List X
fastFlatten t = {!!}

-- 1.1.8 use fastFlatten to build a fast version of tree sort

fastTreeSort : List Nat -> List Nat
fastTreeSort xs = {!!}

-- 1.1.9 again, give unit tests which cover every line of code



{----------------------------------------------------------------------------}
{- 1.2: Shooting Propositional Logic Fish In A Barrel -}
{----------------------------------------------------------------------------}

-- 1.2.1 implement the following operations; try to use only
-- [C-c C-c] and [C-c C-a]

orCommute : {A B : Set} -> A /+/ B -> B /+/ A
orCommute x = {!!}

orAbsorbL : {A : Set} -> Zero /+/ A -> A
orAbsorbL x = {!!}

orAbsorbR : {A : Set} -> A /+/ Zero -> A
orAbsorbR x = {!!}

orAssocR : {A B C : Set} -> (A /+/ B) /+/ C -> A /+/ (B /+/ C)
orAssocR x = {!!}

orAssocL : {A B C : Set} -> A /+/ (B /+/ C) -> (A /+/ B) /+/ C
orAssocL x = {!!}

-- 1.2.2 implement the following operations; try to use only
-- [C-c C-c] and [C-c C-a]

andCommute : {A B : Set} -> A /*/ B -> B /*/ A
andCommute x = {!!}

andAbsorbL : {A : Set} -> A -> One /*/ A
andAbsorbL x = {!!}

andAbsorbR : {A : Set} -> A -> A /*/ One
andAbsorbR x = {!!}

andAssocR : {A B C : Set} -> (A /*/ B) /*/ C -> A /*/ (B /*/ C)
andAssocR x = {!!}

andAssocL : {A B C : Set} -> A /*/ (B /*/ C) -> (A /*/ B) /*/ C
andAssocL x = {!!}

-- how many times is [C-c C-c] really needed?

-- 1.2.3 implement the following operations; try to use only
-- [C-c C-c] and [C-c C-a]

distribute : {A B C : Set} -> A /*/ (B /+/ C) -> (A /*/ B) /+/ (A /*/ C)
distribute x = {!!}

factor : {A B C : Set} -> (A /*/ B) /+/ (A /*/ C) -> A /*/ (B /+/ C)
factor x = {!!}


-- 1.2.4 try to implement the following operations; try to use only
-- [C-c C-c] and [C-c C-a]; at least one of them will prove to be
-- impossible, in which case you should comment it out and explain
-- why it's impossible

Not : Set -> Set
Not X = X -> Zero

deMorgan1 : {A B : Set} -> (Not A /+/ Not B) -> Not (A /*/ B)
deMorgan1 x y = {!!}

deMorgan2 : {A B : Set} -> Not (A /*/ B) -> (Not A /+/ Not B)
deMorgan2 x = {!!}

deMorgan3 : {A B : Set} -> (Not A /*/ Not B) -> Not (A /+/ B)
deMorgan3 x y = {!!}

deMorgan4 : {A B : Set} -> Not (A /+/ B) -> (Not A /*/ Not B)
deMorgan4 x = {!!}


-- 1.2.5 try to implement the following operations; try to use only
-- [C-c C-c] and [C-c C-a]; at least one of them will prove to be
-- impossible, in which case you should comment it out and explain
-- why it's impossible

dnegI : {X : Set} -> X -> Not (Not X)
dnegI = {!!}

dnegE : {X : Set} -> Not (Not X) -> X
dnegE = {!!}

neg321 : {X : Set} -> Not (Not (Not X)) -> Not X
neg321 = {!!}

hamlet : {B : Set} -> B /+/ Not B
hamlet = {!!}

nnHamlet : {B : Set} -> Not (Not (B /+/ Not B))
nnHamlet = {!!}
```

**specimen solution and mark scheme**

```
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

{- Mark scheme:
   The programming for each part is worth one mark.
   the explanation of why the impossible cases are impossible is worth
   one mark.
   The total number of available marks is 15.
-}


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
```

##Exercise 2##

**problem file**

```
module Ex2 where

{-----------------------------------------------------------------------------
Name:
-----------------------------------------------------------------------------}

{-----------------------------------------------------------------------------
CS410 Exercise 2, due 5pm on Monday of Week 6 (3 November 2014)
NOTE: I am well aware that week 6 is quite busy with deadlines,
what with CS408-related obligations and so on. I'd much prefer
you did things to the best of your ability rather than on time,
so I would be sympathetic to requests for some flexibility.
Still, your best bet is to make an early start rather than a
late finish.
-----------------------------------------------------------------------------}

{-----------------------------------------------------------------------------
This exercise is based around extending Hutton's razor with Boolean
values and conditional expressions. By introducing a second value
type, we acquire the risk of type mismatch. The idea here is to
explore different approaches to managing that risk.
-----------------------------------------------------------------------------}

open import Ex1Prelude
open import Ex2Prelude

{- The extended Hutton's Razor syntax -}

data HExpIf : Set where
  num   : Nat -> HExpIf
  boo   : Two -> HExpIf
  _+++_ : HExpIf -> HExpIf -> HExpIf
  hif_then_else_ : HExpIf -> HExpIf -> HExpIf -> HExpIf

{- Note that an expression

   hif eb then ex1 else ex2

   makes sense only when
     * eb produces a Boolean value
     * ex1 and ex2 produce the same sort of value (numeric or Boolean)
-}

HValIf : Set
HValIf = Two /+/ Nat

{- We now have the risk of run time type errors. Let's introduce a type
for things which can go wrong. -}

data Error (E X : Set) : Set where
  ok : X -> Error E X
  error : E -> Error E X

{- 2.1 Add a constructor to the following datatype for each different
   kind of run time error that can happen. (Come back to this exercise
   when you're writing the evaluator in 2.3.) Make these error reports
   as informative as you can.
-}

data EvalError : Set where
  -- your constructors here

{- 2.2 Write a little piece of "glue code" to make it easier to manage
   errors. The idea is to combine error-prone process in *sequence*, where
   the second process can depend on the value produced by the first if it
   succeeds. The resulting process is, of course, also error-prone, failing
   as soon as either component fails.
-}

_>>=_ : {E S T : Set}
        -> Error E S          -- process which tries to get an S
        -> (S -> Error E T)   -- given an S, process which tries for a T
        -> Error E T          -- combined in sequence
es >>= s2et = {!!}

{- 2.3 Implement an evaluator for HExpIf. Be sure to add only numbers and
   to branch only on Booleans. Report type mismatches as errors. You should
   use _>>=_ to help with the propagation of error messages.
-}

eval : HExpIf -> Error EvalError HValIf
eval e = {!!}

{- Note that the type of eval is not specific about whether the value
   expected is numeric or Boolean. It may help to introduce auxiliary
   definitions of error-prone processes which are "ok" only for the
   type that you really want.
-}

{- Next up, stack machine code, and its execution. -}

data HBCode : Set where
  PUSHN : Nat -> HBCode
  PUSHB : Two -> HBCode
  ADD : HBCode
  _SEQ_ : HBCode -> HBCode -> HBCode
  _IFPOP_ : HBCode -> HBCode -> HBCode

{- The intended behaviour of (t IFPOP f) is as follows
  * pop the (we hope) Boolean value from top of stack
  * if it's tt, execute t, else execute f
  * whichever branch is executed, it gets the popped stack to start
-}

{- 2.4 Populate the type of possible execution errors and implement the
   execution behaviour of HBCode, operating on a stack represented as
   a list of HValIf values.
-}

data ExecError : Set where
  -- your constructors here

exec : HBCode -> List HValIf -> Error ExecError (List HValIf)
exec c s = {!!}

{- Next, we take a look at code generation and type safety. -}

data HTy : Set where  -- we have two types in HExpIf
  NUM BOOL : HTy

_=HTy=_ : HTy -> HTy -> Two   -- we can test if two types are equal
NUM  =HTy= NUM   = tt
NUM  =HTy= BOOL  = ff
BOOL =HTy= NUM   = ff
BOOL =HTy= BOOL  = tt

{- 2.5 Write a type-synthesizing compiler, computing both the HTy type and
   the HBCode executable for a given expression. Your compiler should
   give an informative error report if the expression it receives is
   ill typed. Your compiler should also ensure (at least informally) that
   the code produced will never trigger any execution errors.
-}

data CompileError : Set where
  -- your constructors here

compile : HExpIf -> Error CompileError (HTy /*/ HBCode)
compile (num x) = {!!}
compile (boo x) = {!!}
compile (e1 +++ e2) = compile e1 >>= \
  {  (BOOL , c1)  -> error {!!}
  ;  (NUM , c1)   -> {!!}
  }
compile (hif e then e₁ else e₂) = {!!}


{- You have a little bit more room for creative problem-solving in what's
   left of the exercise. The plan is to build the type system into expressions
   and code, the same way we did with plain Hutton's Razor in class.
-}

{- If we *know* which HTy type we want, we can compute which Agda type we
   expect our value to take. -}

HVal : HTy -> Set
HVal NUM  = Nat
HVal BOOL = Two

{- 2.6 Finish the type of typed expressions. You should ensure that only
   well HTy-typed expressions can be constructed. -}

data THExpIf : HTy -> Set where
  val : {t : HTy} -> HVal t -> THExpIf t
  -- you fill in addition and if-then-else

{- 2.7 Implement a type-safe evaluator. -}

teval : {t : HTy} -> THExpIf t -> HVal t
teval e = {!!}

{- 2.8 Implement a type checker. -}

data TypeError : Set where
  -- your constructors here

tcheck : (t : HTy) -> HExpIf -> Error TypeError (THExpIf t)
tcheck t e = {!!}

{- 2.9 Adapt the technique from Hutton.agda to give a type-safe underflow-free
   version of HBCode. You will need to think what is a good type to represent
   the "shape" of a stack: before, we just used Nat to represent the *height* of
   the stack, but now we must worry about types. See next question for a hint. -}

data THBCode : {- your indices here -} Set where
  -- your constructors here

{- 2.10 Implement the execution semantics for your code. You will need to think
   about how to represent a stack. The Ex2Prelude.agda file contains a very
   handy piece of kit for this purpose. You write the type, too. -}

-- your code here

{- 2.11 Write the compiler from well typed expressions to safe code. -}

tcompile : {t : HTy} -> THExpIf t -> {!!}
tcompile e = {!!}
```

**specimen solution and mark scheme**

```
module Ex2Sol where

{-----------------------------------------------------------------------------
Name: Conor McSpecimen
-----------------------------------------------------------------------------}

{-----------------------------------------------------------------------------
CS410 Exercise 2, due 5pm on Monday of Week 6 (3 November 2014)
NOTE: I am well aware that week 6 is quite busy with deadlines,
what with CS408-related obligations and so on. I'd much prefer
you did things to the best of your ability rather than on time,
so I would be sympathetic to requests for some flexibility.
Still, your best bet is to make an early start rather than a
late finish.
-----------------------------------------------------------------------------}

{-----------------------------------------------------------------------------
This exercise is based around extending Hutton's razor with Boolean
values and conditional expressions. By introducing a second value
type, we acquire the risk of type mismatch. The idea here is to
explore different approaches to managing that risk.
-----------------------------------------------------------------------------}

{- Mark scheme
   Each part is worth one mark each, apart from the four labelled
   as worth two. The total number of marks available is 15.
-}

open import Ex1Prelude
open import Ex2Prelude

{- The extended Hutton's Razor syntax -}

data HExpIf : Set where
  num   : Nat -> HExpIf
  boo   : Two -> HExpIf
  _+++_ : HExpIf -> HExpIf -> HExpIf
  hif_then_else_ : HExpIf -> HExpIf -> HExpIf -> HExpIf

{- Note that an expression

   hif eb then ex1 else ex2

   makes sense only when
     * eb produces a Boolean value
     * ex1 and ex2 produce the same sort of value (numeric or Boolean)
-}

HValIf : Set
HValIf = Two /+/ Nat

{- We now have the risk of run time type errors. Let's introduce a type
for things which can go wrong. -}

data Error (E X : Set) : Set where
  ok    : X -> Error E X
  error : E -> Error E X

{- 2.1 Add a constructor to the following datatype for each different
   kind of run time error that can happen. (Come back to this exercise
   when you're writing the evaluator in 2.3.) Make these error reports
   as informative as you can.
-}

data EvalError : Set where
  wantedANatButGotALousy : HExpIf -> EvalError
  wantedATwoButGotALousy : HExpIf -> EvalError
  -- your constructors here

{- 2.2 Write a little piece of "glue code" to make it easier to manage
   errors. The idea is to combine error-prone process in *sequence*, where
   the second process can depend on the value produced by the first if it
   succeeds. The resulting process is, of course, also error-prone, failing
   as soon as either component fails.
-}

_>>=_ : {E S T : Set}
        -> Error E S          -- process which tries to get an S
        -> (S -> Error E T)   -- given an S, process which tries for a T
        -> Error E T          -- combined in sequence
ok s    >>= s2et = s2et s
error e >>= s2et = error e

{- 2.3 Implement an evaluator for HExpIf. Be sure to add only numbers and
   to branch only on Booleans. Report type mismatches as errors. You should
   use _>>=_ to help with the propagation of error messages.
   (2 marks)
-}

natOrBust : {E : Set} -> E -> HValIf -> Error E Nat
natOrBust e (inl b) = error e
natOrBust e (inr n) = ok n

twoOrBust : {E : Set} -> E -> HValIf -> Error E Two
twoOrBust e (inl b) = ok b
twoOrBust e (inr n) = error e

eval : HExpIf -> Error EvalError HValIf
eval (num n) = ok (inr n)
eval (boo x) = ok (inl x)
eval (d +++ e) =
  (eval d >>= natOrBust (wantedANatButGotALousy d)) >>= \ dn ->
  (eval e >>= natOrBust (wantedANatButGotALousy e)) >>= \ en ->
  ok (inr (dn + en))
eval (hif e then t else f) =
  (eval e >>= twoOrBust (wantedATwoButGotALousy e)) >>= \ eb ->
  if eb then eval t else eval f

{- Note that the type of eval is not specific about whether the value
   expected is numeric or Boolean. It may help to introduce auxiliary
   definitions of error-prone processes which are "ok" only for the
   type that you really want.
-}

{- Next up, stack machine code, and its execution. -}

data HBCode : Set where
  PUSHN : Nat -> HBCode
  PUSHB : Two -> HBCode
  ADD : HBCode
  _SEQ_ : HBCode -> HBCode -> HBCode
  _IFPOP_ : HBCode -> HBCode -> HBCode

{- The intended behaviour of (t IFPOP f) is as follows
  * pop the (we hope) Boolean value from top of stack
  * if it's tt, execute t, else execute f
  * whichever branch is executed, it gets the popped stack to start
-}

{- 2.4 Populate the type of possible execution errors and implement the
   execution behaviour of HBCode, operating on a stack represented as
   a list of HValIf values. (2 marks)
-}

data ExecError : Set where
  stackUnderflowInADD : ExecError
  stackUnderflowInIFPOP : ExecError
  addingATwo : HValIf -> ExecError
  iffingANat : HValIf -> ExecError
  -- your constructors here

exec : HBCode -> List HValIf -> Error ExecError (List HValIf)
exec (PUSHN n) s = ok (inr n :> s)
exec (PUSHB b) s = ok (inl b :> s)
exec ADD (y :> x :> s)
  = natOrBust (addingATwo x) x >>= \ xn ->
    natOrBust (addingATwo y) y >>= \ yn ->
    ok (inr (xn + yn) :> s)
exec ADD _ = error stackUnderflowInADD
exec (c SEQ d) s = exec c s >>= exec d
exec (t IFPOP f) [] = error stackUnderflowInIFPOP
exec (t IFPOP f) (x :> s)
  = twoOrBust (iffingANat x) x >>= \ xb ->
    if xb then exec t s else exec f s

{- Next, we take a look at code generation and type safety. -}

data HTy : Set where  -- we have two types in HExpIf
  NUM BOOL : HTy

_=HTy=_ : HTy -> HTy -> Two   -- we can test if two types are equal
NUM  =HTy= NUM   = tt
NUM  =HTy= BOOL  = ff
BOOL =HTy= NUM   = ff
BOOL =HTy= BOOL  = tt

{- 2.5 Write a type-synthesizing compiler, computing both the HTy type and
   the HBCode executable for a given expression. Your compiler should
   give an informative error report if the expression it receives is
   ill typed. Your compiler should also ensure (at least informally) that
   the code produced will never trigger any execution errors.
   (2 marks)
-}

data CompileError : Set where
  addingABool : HExpIf -> CompileError
  iffingANumber : HExpIf -> CompileError
  ifBranchesMismatchedTypes : (HExpIf /*/ HTy) -> (HExpIf /*/ HTy) -> CompileError

compile : HExpIf -> Error CompileError (HTy /*/ HBCode)
compile (num x) = ok (NUM , PUSHN x)
compile (boo x) = ok (BOOL , PUSHB x)
compile (e1 +++ e2) = compile e1 >>= \
  {  (BOOL , _)   -> error (addingABool e1)
  ;  (NUM , c1)   -> compile e2 >>= \
    {  (BOOL , _)   -> error (addingABool e2)
    ;  (NUM , c2)   -> ok (NUM , (c1 SEQ c2) SEQ ADD)
    }
  }
compile (hif e then t else f) = compile e >>= \
  {  (NUM , _)   -> error (iffingANumber e)
  ;  (BOOL , c)  -> compile t >>= \
    {  (tty , tc)   -> compile f >>= \
      {  (fty , fc)   ->
         if tty =HTy= fty then ok (tty , c SEQ (tc IFPOP fc))
           else error (ifBranchesMismatchedTypes (t , tty) (f , fty))
      }
    }
  }


{- You have a little bit more room for creative problem-solving in what's
   left of the exercise. The plan is to build the type system into expressions
   and code, the same way we did with plain Hutton's Razor in class.
-}

{- If we *know* which HTy type we want, we can compute which Agda type we
   expect our value to take. -}

HVal : HTy -> Set
HVal NUM  = Nat
HVal BOOL = Two

{- 2.6 Finish the type of typed expressions. You should ensure that only
   well HTy-typed expressions can be constructed. -}

data THExpIf : HTy -> Set where
  val : {t : HTy} -> HVal t -> THExpIf t
  _+++_ : THExpIf NUM -> THExpIf NUM -> THExpIf NUM
  hif_then_else_ : {t : HTy} -> THExpIf BOOL -> THExpIf t -> THExpIf t -> THExpIf t
  -- you fill in addition and if-then-else

{- 2.7 Implement a type-safe evaluator. -}

teval : {t : HTy} -> THExpIf t -> HVal t
teval (val x) = x
teval (d +++ e) = teval d + teval e
teval (hif e then t else f) = if teval e then teval t else teval f

{- 2.8 Implement a type checker. (2 marks) -}

data TypeError : Set where
  wanted_got_ : HTy -> HExpIf -> TypeError
  -- your constructors here

tcheck : (t : HTy) -> HExpIf -> Error TypeError (THExpIf t)
tcheck NUM (num x) = ok (val x)
tcheck BOOL (num x) = error (wanted BOOL got num x)
tcheck NUM (boo x) = error (wanted NUM got boo x)
tcheck BOOL (boo x) = ok (val x)
tcheck NUM (d +++ e) = tcheck NUM d >>= \ dt -> tcheck NUM e >>= \ et -> ok (dt +++ et)
tcheck BOOL (d +++ e) = error (wanted BOOL got (d +++ e))
tcheck t (hif e then th else el) =
  tcheck BOOL e >>= \ et ->
  tcheck t th >>= \ tht ->
  tcheck t el >>= \ elt -> ok (hif et then tht else elt)

{- 2.9 Adapt the technique from Hutton.agda to give a type-safe underflow-free
   version of HBCode. You will need to think what is a good type to represent
   the "shape" of a stack: before, we just used Nat to represent the *height* of
   the stack, but now we must worry about types. See next question for a hint. -}

data THBCode : List HTy -> List HTy -> Set where
  PUSHV : {t : HTy}{s : List HTy} -> HVal t -> THBCode s (t :> s)
  ADD : {s : List HTy} -> THBCode (NUM :> NUM :> s) (NUM :> s)
  _SEQ_ : {i j k : List HTy} -> THBCode i j -> THBCode j k -> THBCode i k
  _IFPOP_ : {i j : List HTy} -> THBCode i j -> THBCode i j -> THBCode (BOOL :> i) j

{- 2.10 Implement the execution semantics for your code. You will need to think
   about how to represent a stack. The Ex2Prelude.agda file contains a very
   handy piece of kit for this purpose. You write the type, too. -}

Stack : List HTy → Set
Stack i = All HVal i

-- forward composition
_followedBy_ : {A B C : Set} (f : A → B) (g : B → C) → A → C
f followedBy g = λ z → g (f z)

tsemantics : {i j : List HTy} (c : THBCode i j) (s : Stack i) → Stack j
tsemantics (PUSHV x)   s           = x , s
tsemantics ADD         (m , n , s) = m + n , s
tsemantics (c SEQ d)   s           = (tsemantics c followedBy tsemantics d) s
tsemantics (t IFPOP f) (b , s)     = if b then tsemantics t s else tsemantics f s

{- 2.11 Write the compiler from well typed expressions to safe code. -}

tcompile : {t : HTy} -> THExpIf t -> {s : List HTy} -> THBCode s (t :> s)
tcompile (val x) = PUSHV x
tcompile (d +++ e) = (tcompile d SEQ tcompile e) SEQ ADD
tcompile (hif e then t else f) = tcompile e SEQ (tcompile t IFPOP tcompile f)
```

##Exercise 3##

**problem file**

```
module Ex3 where

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
Nat2NAT n = {!!}

-- Use fold to define the function which sends them back.

NAT2Nat : NAT -> Nat
NAT2Nat = fold (kK One k+ kId) {!!}

-- Show that you get the "round trip" property (by writing
-- recursive functions that use rewrite.

Nat2NAT2Nat : NAT2Nat o Nat2NAT =^= id
Nat2NAT2Nat n = {!!}

NAT2Nat2NAT : Nat2NAT o NAT2Nat =^= id
NAT2Nat2NAT n = {!!}


{- 3.2 Lists in the Kit -}

-- find the code which gives you lists with a given element
-- type (note that the kId constructor marks the place for
-- recursive *sublists* not for list elements

kLIST : Set -> Kit
kLIST A = {!!}

LIST : Set -> Set
LIST A = Data (kLIST A)

-- define nil and cons for your lists

nil : {A : Set} -> LIST A
nil = {!!}

cons : {A : Set} -> A -> LIST A -> LIST A
cons a as = {!!}

-- use fold to define concatenation

conc : {A : Set} -> LIST A -> LIST A -> LIST A
conc {A} xs ys = fold (kLIST A) {!!} xs

-- prove the following (the yellow bits should disappear when
-- you define kLIST);
-- maddeningly, "rewrite" won't do it, but this piece of kit
-- (which is like a manual version of rewrite) will do it

cong : {S T : Set}(f : S -> T){a b : S} -> a == b -> f a == f b
cong f refl = refl

concNil : {A : Set}(as : LIST A) -> conc as nil == as
concNil as = {!!}

concAssoc : {A : Set}(as bs cs : LIST A) ->
            conc (conc as bs) cs == conc as (conc bs cs)
concAssoc as bs cs = {!!}


{- 3.3 Trees in the Kit -}

-- give a kit code for binary trees with unlabelled leaves
-- and nodes labelled with elements of NAT

kTREE : Kit
kTREE = {!!}

TREE : Set
TREE = Data kTREE

-- give the constructors

leaf : TREE
leaf = {!!}

node : TREE -> NAT -> TREE -> TREE
node l n r = {!!}

-- implement flattening (slow flattening is ok) as a fold

flatten : TREE -> LIST NAT
flatten = fold kTREE {!!}


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

rec k {X} f d = outr (fold k {{!!} /*/ X} {!!} d)


-- use rec to implement "insList", being the function which inserts
-- a number in a list, such that if the input list is in increasing
-- order, so is the output list; you may assume that "lessEq" exists

lessEq : NAT -> NAT -> Two

insList : NAT -> LIST NAT -> LIST NAT
insList n = rec (kLIST NAT) {!!}

-- justify the assumption by defining "lessEq"; do not use explicit
-- recursion;
-- note that the thing we build for each number is its less-or-equal
-- test;
-- do use "rec kNat" once more to take numbers apart

lessEq x y = rec kNat {NAT -> Two} {!!} x y

-- implement insertion for binary search trees using "rec"

insTree : NAT -> TREE -> TREE
insTree n = rec kTREE {!!}
```

**specimen solution and mark scheme**

```
module Ex3Sol where

{- Mark Scheme
   3.1 is work 3; 3.2 is worth 4; 3.3 is worth 3; 3.4 is worth 5
   The total number of marks available is 15.
   See below for individual mark breakdown.
-}

open import Ex1Prelude
open import FuncKit

{- 3.1 Numbers in the Kit (3 marks) -}

{- We can define the type of natural numbers using the tools
   from the functor kit like this: -}

kNat : Kit
kNat = kK One k+ kId

NAT : Set
NAT = Data kNat

-- Define the function which sends "ordinary" numbers to
-- the corresponding kit-encoded numbers. (1 mark)

Nat2NAT : Nat -> NAT
Nat2NAT zero = [ inl <> ]
Nat2NAT (suc n) = [ inr (Nat2NAT n) ]

-- Use fold to define the function which sends them back.  (1 mark)

NAT2Nat : NAT -> Nat
NAT2Nat = fold (kK One k+ kId) (\
  { (inl <>) -> zero
  ; (inr NAT2Nat_n)  -> suc NAT2Nat_n
  })

-- Show that you get the "round trip" property (by writing
-- recursive functions that use rewrite.  (1 mark)

Nat2NAT2Nat : NAT2Nat o Nat2NAT =^= id
Nat2NAT2Nat zero = refl
Nat2NAT2Nat (suc n) rewrite Nat2NAT2Nat n = refl

NAT2Nat2NAT : Nat2NAT o NAT2Nat =^= id
NAT2Nat2NAT [ inl <> ] = refl
NAT2Nat2NAT [ inr x ] rewrite NAT2Nat2NAT x = refl


{- 3.2 Lists in the Kit (4 marks) -}

-- find the code which gives you lists with a given element
-- type (note that the kId constructor marks the place for
-- recursive *sublists* not for list elements (1 mark)

kLIST : Set -> Kit
kLIST A = kK One k+ (kK A k* kId)

LIST : Set -> Set
LIST A = Data (kLIST A)

-- define nil and cons for your lists  (1 mark)

nil : {A : Set} -> LIST A
nil = [ inl <> ]

cons : {A : Set} -> A -> LIST A -> LIST A
cons a as = [ inr (a , as) ]

-- use fold to define concatenation  (1 mark)

conc : {A : Set} -> LIST A -> LIST A -> LIST A
conc {A} xs ys = fold (kLIST A)
   (\ { (inl <>) -> ys
      ; (inr (a , conc_as_ys)) -> cons a conc_as_ys
      })
   xs

-- prove the following (the yellow bits should disappear when
-- you define kLIST);  (1 mark)
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


{- 3.3 Trees in the Kit (3 marks) -}

-- give a kit code for binary trees with unlabelled leaves
-- and nodes labelled with elements of NAT (1 mark)

kTREE : Kit
kTREE = kK One k+ (kId k* (kK NAT k* kId))

TREE : Set
TREE = Data kTREE

-- give the constructors (1 mark)

leaf : TREE
leaf = [ inl <> ]

node : TREE -> NAT -> TREE -> TREE
node l n r = [ inr (l , n , r) ]

-- implement flattening (slow flattening is ok) as a fold (1 mark)

flatten : TREE -> LIST NAT
flatten = fold kTREE (\
  { (inl <>) -> nil
  ; (inr (flatten_l , n , flatten_r)) -> conc flatten_l (cons n flatten_r)
  })


{- 3.4 "rec" from "fold" (5 marks) -}

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
-- as well as the value you actually want. (1 mark)

rec k {X} f d = outr (fold k {Data k /*/ X}
                 (\ kdx -> [ kitMap k outl kdx ] , f kdx) d)


-- use rec to implement "insList", being the function which inserts
-- a number in a list, such that if the input list is in increasing
-- order, so is the output list; you may assume that "lessEq" exists (1 mark)

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
-- (2 marks, one for each "rec")

lessEq x y = rec kNat {NAT -> Two}
  (\ { (inl <>) -> \ y -> {- lessEq zero y -} tt
     ; (inr (x , lessEq_x)) -> rec kNat (\
       { (inl <>) -> {- lessEq (suc x) zero -} ff
       ; (inr (y , lessEq_[suc_x]_y)) -> {- lessEq (suc x) (suc y) -} lessEq_x y
       })
     })
  x y

-- implement insertion for binary search trees using "rec" (1 mark)

insTree : NAT -> TREE -> TREE
insTree n = rec kTREE (\
  { (inl <>) -> node leaf n leaf
  ; (inr ((l , insTree_n_l) , y , (r , insTree_n_r))) ->
      if lessEq n y then node insTree_n_l y r else node l y insTree_n_r
  })
```


##Exercise 4##

**problem file**

```
module Ex4 where

{- I'm sorry I haven't quite finished setting this exercise yet, but by
   the joy of version control, the rest of it can be merged in later
   (quite soon). At least you can get cracking: I promise not to break
   anything, just to add a bit more on the end.

   The deadline for this is midnight on the Monday of Week 12 (15 Dec).
   It'd be good to get the marks in before Christmas, but if the end of
   term is looking deadlinetastic, please open negotiations.
-}

open import Ex1Prelude
open import IxCon

{-# BUILTIN BOOL Two #-}
{-# BUILTIN TRUE tt #-}
{-# BUILTIN FALSE ff #-}
{-# BUILTIN LIST List #-}
{-# BUILTIN NIL [] #-}
{-# BUILTIN CONS _:>_ #-}

postulate -- this means that we just suppose the following things exist...
  Char : Set
  String : Set
{-# BUILTIN CHAR Char #-}
{-# BUILTIN STRING String #-}

primitive -- these are baked in; they even work!
  primCharEquality : Char -> Char -> Two
  primStringAppend : String -> String -> String
  primStringToList : String -> List Char
  primStringFromList : List Char -> String

---------------------------------------------------------------------------
-- WRITING FILES, AN INTERFACE
---------------------------------------------------------------------------

{- If you possess the ability to open a file for writing, you might
   have the following interface. -}

-- States
data WriteState : Set where
  opened closed : WriteState  -- do you currently have a file open or not?

-- Commands
data WriteC : WriteState -> Set where
  openWrite   : (fileName : String)  -> WriteC closed
  writeChar   : Char                 -> WriteC opened
  closeWrite  :                         WriteC opened

-- Responses
WriteR : (j : WriteState)(c : WriteC j) -> Set
WriteR .closed (openWrite fileName)  = WriteState  -- we get told whether it worked
WriteR .opened (writeChar x)         = One  -- always works
WriteR .opened closeWrite            = One  -- always works

{- 4.1 Implement the following operation which determines the next
   state. You should ensure that you can write characters only to
   a successfully opened file, and that you can write as many as
   you want. It should also be possible to insist that a process
   closes its file. -}

writeNext : (j : WriteState)(c : WriteC j) -> WriteR j c -> WriteState
writeNext j c r = {!!}

-- the file writing interface, assembled as an indexed container
WRITE : WriteState => WriteState
WRITE = WriteC <! WriteR / writeNext


---------------------------------------------------------------------------
-- READING FILES, AN INTERFACE
---------------------------------------------------------------------------

{- To read from a file, it should be open, and you shouldn't be at the
   end of it. -}

-- States
data ReadState : Set where
  opened : (eof : Two) -> ReadState    -- eof is tt if we're at end of file
  closed : ReadState

{- 4.2 Finish the READ implementation, in accordance with the description. -}

-- Commands
data ReadC : ReadState -> Set where
  openRead    : {- your stuff -} ReadC {!!}   -- needs a filename; might not open successfully;
                                              -- might open an empty file
  readChar    : {- your stuff -} ReadC {!!}   -- makes sense only if we're not at end of file
                                              -- and might take us to end of file
  closeRead   : {- your stuff -} ReadC {!!}   -- makes sense only if the file is open

-- Responses
ReadR : (j : ReadState)(c : ReadC j) -> Set
ReadR j c = {!!}

-- next State; you need to make sure the response gives enough info
readNext : (j : ReadState)(c : ReadC j) -> ReadR j c -> ReadState
readNext j c r = {!!}

READ : ReadState => ReadState
READ = ReadC <! ReadR / readNext

---------------------------------------------------------------------------
-- COMBINING TWO INTERFACES WITH SHARED STATE
---------------------------------------------------------------------------

{- 4.3 Let's suppose we have two command-response interfaces which offer
       different functionality for the same system. Correspondingly, we'll
       have two indexed containers for the same index set. Show that you
       can combine them into one indexed container which lets you choose a
       command from either menu and evolves the state as specified by
       whichever interface offered the chosen command.
-}

_=+=_ : {I : Set} -> I => I -> I => I -> I => I
CRn0 =+= CRn1 = {!!}

---------------------------------------------------------------------------
-- WHEN IGNORANCE IS BLISS, BIS
---------------------------------------------------------------------------

{- 4.4 If we have a command-response interface with index I representing
       states of the system, show that we can index basically the same
       commands and responses over a state, I /*/ J, where the J is just
       useless information which never changes. (This operation isn't
       super-useful on its own, but it's handy in combination with other
       things. -}

GrowR : {I J : Set} -> I => I -> (I /*/ J) => (I /*/ J)
GrowR CRn = {!!}

-- do the same for "growing the index on the left"

GrowL : {I J : Set} -> I => I -> (J /*/ I) => (J /*/ I)
GrowL CRn = {!!}


---------------------------------------------------------------------------
-- COMBINING TWO INTERFACES WITH SEPARATE STATE
---------------------------------------------------------------------------

{- 4.5 Making use of 4.4 and 4.5, show how to combine two interfaces which
       operate independently on separate state: commands from one should
       not affect the state of the other.
-}

_<+>_ : {I0 I1 : Set} -> I0 => I0 -> I1 => I1 -> (I0 /*/ I1) => (I0 /*/ I1)
CRn0 <+> CRn1 = {!!}


---------------------------------------------------------------------------
-- ERROR REPORTING, AN INTERFACE
---------------------------------------------------------------------------

{- I'm building the next bit for you.

   When things go wrong, we need to trigger an error condition and abort
   mission. However, if we have other stuff going on (open files, etc),
   it may not always be ok to drop everything and run away. There will
   be some states in which it is safe to escape (and deliver a suitable
   error message, perhaps) and other states in which escape should be
   impossible.

   If it is safe to issue an error message, we should be able to do so
   without fear of any response from the environment that would oblige
   us to carry on.
-}

data ErrorC {I : Set}(SafeMessage : I -> Set)(i : I) : Set where
  error : SafeMessage i -> ErrorC SafeMessage i
    -- the SafeMessage parameter tells us what is an acceptable
    -- error message in any given state; in states where this gives
    -- Zero, it will be impossible to trigger an error!

ErrorR : {I : Set}{SafeMessage : I -> Set}(i : I)(c : ErrorC SafeMessage i) -> Set
ErrorR _ _ = Zero  -- there's no comeback

errorNext : {I : Set}{SafeMessage : I -> Set}
            (i : I)(c : ErrorC SafeMessage i) -> ErrorR i c -> I
errorNext i c ()  -- so we don't have to say how the state will evolve

ERROR : {I : Set}(SafeMessage : I -> Set) -> I => I
ERROR SafeMessage = ErrorC SafeMessage <! ErrorR / errorNext


---------------------------------------------------------------------------
-- COPY A FILE
---------------------------------------------------------------------------

{- 4.6 Implement a process which, given access to suitable interfaces, will
       give the process for copying a named source file to a named target
       file. This goes in two phases.
-}

{- 4.6.1 Firstly, you should identify the command-reponse interface within
   which you need to work. You will need to be able to read and write files,
   but also to signal errors (in case a file fails to open for some reason).
   You must ensure that it is impossible for any process using your interface
   to escape with an error leaving a file open. You must also make it
   possible to guarantee that your copying process will, error or not, leave
   all files closed.
-}

CPState : Set
CPState = {!!}

CPInterface : CPState => CPState
CPInterface = {!!}

{- 4.6.2 Secondly, you should implement your copying process, working to your
   interface. I will let you switch off the termination checker: you cannot
   predict in advance how long the copying process will go on, as you have
   not seen the source file yet. (Later, we'll learn how to be honest about
   things which might go on for ever, but for now, let's cheat.)
-}
{-# NO_TERMINATION_CHECK #-}

cp : (sourceFile targetFile : String) -> Game CPInterface {!!} {!!}
cp sourceFile targetFile = {!!}

{- HINTS
  You will certainly need to build some extra bits and pieces.

  You have the components for reading, writing and error handling, and
  suitable kit with which to combine them. Reading and writing don't
  interfere with each other, but it's important to make sure that you
  can't bomb out with an error, so some shared state seems important.

  There are really two phases to the process:
    (1) getting the files open  -- this may go wrong
    (2) copying from one to the other  -- this will work if we reach it
  You might want to split these phases apart.
-}


---------------------------------------------------------------------------
-- SCRIPTING INTERACTION
---------------------------------------------------------------------------

{- 4.7.1 Show how to take a command-response interface and deliver its
   "scripted" version, where a script command consists of any permitted
   (possibly empty) sequence of the given commands. -}

SCRIPT : {I : Set} -> I => I -> I => I
SCRIPT {I} CRn = Game CRn (\ I -> One) <! Rs / ns where
  Rs : (i : I) -> Game CRn (\ I -> One) i -> Set
  Rs i cs = {!!}
  ns : (i : I)(cs : Game CRn (\ I -> One) i) -> Rs i cs -> I
  ns i cs rs = {!!}

{- 4.7.2 Show how to take a strategy for scripted interaction and turn
   it into a strategey for unscripted interaction, by running the scripts
   one command at a time. You may find it useful to build a helper function
   to process one script. -}

unScript : {I : Set}(CRn : I => I){X : I -> Set}{i : I} ->
           Game (SCRIPT CRn) X i -> Game CRn X i
unScript CRn g = {!!}

-- HINT doing recursion in the "fold" pattern may help


---------------------------------------------------------------------------
-- INDEXED CONTAINER DRIVERS(*)
-- (*) The researchers who invented this stuff are fans of The Fall
-- (by which I mean the group led my Mark E Smith who wrote the song
-- The Container Drivers, not some johnny-come-lately Northern Irish
-- serial killer drama).
---------------------------------------------------------------------------

record Driver {I J : Set}(Sync : I -> J -> Set)
              (Hi : I => I)(Lo : J => J) : Set where
  -- Hi is a high-level command-response interface
  -- Lo is a low-level command-response interface
  -- Sync specifies which high and low level states are compatible
  -- and what you expect to know at the time
  field
    -- assuming states are in sync; it should be possible to map
    -- high-level commands to low-level commands...
    hiClo :  (i : I)(j : J) -> Sync i j ->
             Command Hi i -> Command Lo j
    -- ...and afterwards to translate the low-level response to that
    -- command back up to the high-level
    loRhi :  (i : I)(j : J)(s : Sync i j)(c : Command Hi i) ->
             Response Lo j (hiClo i j s c) -> Response Hi i c
    -- moreover, the resulting states should be in sync
    nSync :  (i : I)(j : J)(s : Sync i j)(c : Command Hi i)
             (r : Response Lo j (hiClo i j s c)) ->
             Sync (next Hi i c (loRhi i j s c r)) (next Lo j (hiClo i j s c) r)
open Driver public


---------------------------------------------------------------------------
-- A DANGEROUS HASKELL IO COMMAND-RESPONSE SYSTEM
---------------------------------------------------------------------------

data Maybe (X : Set) : Set where
  yes : X -> Maybe X
  no  : Maybe X

data IOMode : Set where
  readMode writeMode appendMode readWriteMode : IOMode

postulate Handle : Set

data HaskellIOCommand (_ : One) : Set where
  hOpen : String -> IOMode -> HaskellIOCommand <>
  hClose hIsEOF hGetChar : Handle -> HaskellIOCommand <>
  hPutChar : Handle -> Char -> HaskellIOCommand <>
  hError : String -> HaskellIOCommand <>

HaskellIOResponse : (i : One) -> HaskellIOCommand i -> Set
HaskellIOResponse i (hOpen f m) = Maybe Handle
HaskellIOResponse i (hClose h) = One
HaskellIOResponse i (hIsEOF h) = Two
HaskellIOResponse i (hGetChar h) = Char
HaskellIOResponse i (hPutChar h c) = One
HaskellIOResponse i (hError e) = Zero

HASKELLIO : One => One
HASKELLIO = HaskellIOCommand <! HaskellIOResponse / _


---------------------------------------------------------------------------
-- SCRIPTING INTERACTION
---------------------------------------------------------------------------

{- 4.8 Your mission is to translate your lovely, safe characterisation
   of reading and writing into its dodgy Haskell counterpart. Of course,
   your code shouldn't do anything dodgy. You will need to think what
   information must be available when you are in each state.
-}

safe2unsafe : Driver (\ i j -> {!!}) CPInterface (SCRIPT HASKELLIO)
safe2unsafe = {!!}

---------------------------------------------------------------
-- TO BE CONTINUED... BUT NOT WITH ANY MORE CODING OBLIGATIONS
---------------------------------------------------------------
```

**specimen solution and mark scheme**

```
module Ex4Sol where

{- Mark Scheme
   as indicated, below, totalling 15
-}

open import Ex1Prelude
open import IxCon

{-# BUILTIN BOOL Two #-}
{-# BUILTIN TRUE tt #-}
{-# BUILTIN FALSE ff #-}
{-# BUILTIN LIST List #-}
{-# BUILTIN NIL [] #-}
{-# BUILTIN CONS _:>_ #-}

postulate -- this means that we just suppose the following things exist...
  Char : Set
  String : Set
{-# BUILTIN CHAR Char #-}
{-# BUILTIN STRING String #-}

primitive -- these are baked in; they even work!
  primCharEquality : Char -> Char -> Two
  primStringAppend : String -> String -> String
  primStringToList : String -> List Char
  primStringFromList : List Char -> String

---------------------------------------------------------------------------
-- WRITING FILES, AN INTERFACE
---------------------------------------------------------------------------

{- If you possess the ability to open a file for writing, you might
   have the following interface. -}

-- States
data WriteState : Set where
  opened closed : WriteState  -- do you currently have a file open or not?

-- Commands
data WriteC : WriteState -> Set where
  openWrite   : (fileName : String)  -> WriteC closed
  writeChar   : Char                 -> WriteC opened
  closeWrite  :                         WriteC opened

-- Responses
WriteR : (j : WriteState)(c : WriteC j) -> Set
WriteR .closed (openWrite fileName)  = WriteState
WriteR .opened (writeChar x)         = One
WriteR .opened closeWrite            = One

{- 4.1 Implement the following operation which determines the next
   state. You should ensure that you can write characters only to
   a successfully opened file, and that you can write as many as
   you want. It should also be possible to insist that a process
   closes its file. (1 mark) -}

{-
writeNext : (j : WriteState)(c : WriteC j) -> WriteR j c -> WriteState
writeNext j c r = {!!}
-}
writeNext : (j : WriteState)(c : WriteC j) -> WriteR j c -> WriteState
writeNext ._ (openWrite fileName) j = j
writeNext .opened (writeChar x) r = opened
writeNext .opened closeWrite r = closed

-- the file writing interface, assembled as an indexed container
WRITE : WriteState => WriteState
WRITE = WriteC <! WriteR / writeNext


---------------------------------------------------------------------------
-- READING FILES, AN INTERFACE
---------------------------------------------------------------------------

{- To read from a file, it should be open, and you shouldn't be at the
   end of it. -}

-- States
data ReadState : Set where
  opened : (eof : Two) -> ReadState    -- eof is tt if we're at end of file
  closed : ReadState

{- 4.2 Finish the READ implementation, in accordance with the description.
   (3 marks, for commands, responses and next)  -}

{-
-- Commands
data ReadC : ReadState -> Set where
  openRead    : {- your stuff -} ReadC {!!}   -- needs a filename; might not open successfully;
                                              -- might open an empty file
  readChar    : {- your stuff -} ReadC {!!}   -- makes sense only if we're not at end of file
                                              -- and might take us to end of file
  closeRead   : {- your stuff -} ReadC {!!}   -- makes sense only if the file is open
                                              -- but you should not be forced to read the whole file

-- Responses
ReadR : (j : ReadState)(c : ReadC j) -> Set
ReadR j c = {!!}

-- next State; you need to make sure the response gives enough info
readNext : (j : ReadState)(c : ReadC j) -> ReadR j c -> ReadState
readNext j c r = {!!}
-}
-- Commands
data ReadC : ReadState -> Set where
  openRead    : String -> ReadC closed   -- needs a filename; might not open successfully;
                                              -- might open an empty file
  readChar    : ReadC (opened ff)   -- makes sense only if we're not at end of file
                                              -- and might take us to end of file
  closeRead   : {b : Two} -> ReadC (opened b)   -- makes sense only if the file is open

-- Responses
ReadR : (j : ReadState)(c : ReadC j) -> Set
ReadR .closed (openRead x) = ReadState
ReadR .(opened ff) readChar = Char /*/ Two
ReadR ._ closeRead = One

-- next State; you need to make sure the resonse gives enough info
readNext : (j : ReadState)(c : ReadC j) -> ReadR j c -> ReadState
readNext .closed (openRead x) s = s
readNext .(opened ff) readChar (c , b) = opened b
readNext ._ closeRead r = closed

-- the file reading interface, assembled as an indexed container
READ : ReadState => ReadState
READ = ReadC <! ReadR / readNext


---------------------------------------------------------------------------
-- COMBINING TWO INTERFACES WITH SHARED STATE
---------------------------------------------------------------------------

{- 4.3 Let's suppose we have two command-response interfaces which offer
       different functionality for the same system. Correspondingly, we'll
       have two indexed containers for the same index set. Show that you
       can combine them into one indexed container which lets you choose a
       command from either menu and evolves the state as specified by
       whichever interface offered the chosen command.
       (2 marks, one for commands, one for the rest)
-}

_=+=_ : {I : Set} -> I => I -> I => I -> I => I
(C0 <! R0 / n0) =+= (C1 <! R1 / n1)
  =   (\ i -> C0 i /+/ C1 i)
  <!  (\ { i (inl c0) -> R0 i c0 ; i (inr c1) -> R1 i c1 })
  /   (\ { i (inl c0) r0 -> n0 i c0 r0 ; i (inr c1) r1 -> n1 i c1 r1 })


---------------------------------------------------------------------------
-- WHEN IGNORANCE IS BLISS, BIS
---------------------------------------------------------------------------

{- 4.4 If we have a command-response interface with index I representing
       states of the system, show that we can index basically the same
       commands and responses over a state, I /*/ J, where the J is just
       useless information which never changes. (This operation isn't
       super-useful on its own, but it's handy in combination with other
       things. (2 marks; half each for C, R, n, half for deploying
       symmetry) -}

GrowR : {I J : Set} -> I => I -> (I /*/ J) => (I /*/ J)
GrowR (C <! R / n)
  =  (\ { (i , j) -> C i })
  <! (\ { (i , j) c -> R i c })
  /  (\ { (i , j) c r -> n i c r , j })

-- do the same for "growing the index on the left"

GrowL : {I J : Set} -> I => I -> (J /*/ I) => (J /*/ I)
GrowL (C <! R / n)
  =  (\ { (j , i) -> C i })
  <! (\ { (j , i) c -> R i c })
  /  (\ { (j , i) c r -> j , n i c r })


---------------------------------------------------------------------------
-- COMBINING TWO INTERFACES WITH SEPARATE STATE
---------------------------------------------------------------------------

{- 4.5 Making use of 4.4 and 4.5, show how to combine two interfaces which
       operate independently on separate state: commands from one should
       not affect the state of the other. (1 mark)
-}

{-
_<+>_ : {I0 I1 : Set} -> I0 => I0 -> I1 => I1 -> (I0 /*/ I1) => (I0 /*/ I1)
C0 <+> C1 = {!!}
-}

_<+>_ : {I0 I1 : Set} -> I0 => I0 -> I1 => I1 -> (I0 /*/ I1) => (I0 /*/ I1)
C0 <+> C1 = GrowR C0 =+= GrowL C1


---------------------------------------------------------------------------
-- ERROR REPORTING, AN INTERFACE
---------------------------------------------------------------------------

{- I'm building the next bit for you.

   When things go wrong, we need to trigger an error condition and abort
   mission. However, if we have other stuff going on (open files, etc),
   it may not always be ok to drop everything and run away. There will
   be some states in which it is safe to escape (and deliver a suitable
   error message, perhaps) and other states in which escape should be
   impossible.

   If it is safe to issue an error message, we should be able to do so
   without fear of any response from the environment that would oblige
   us to carry on.
-}

data ErrorC {I : Set}(SafeMessage : I -> Set)(i : I) : Set where
  error : SafeMessage i -> ErrorC SafeMessage i
    -- the SafeMessage parameter tells us what is an acceptable
    -- error message in any given state; in states where this gives
    -- Zero, it will be impossible to trigger an error!

ErrorR : {I : Set}{SafeMessage : I -> Set}(i : I)(c : ErrorC SafeMessage i) -> Set
ErrorR _ _ = Zero  -- there's no comeback

errorNext : {I : Set}{SafeMessage : I -> Set}
            (i : I)(c : ErrorC SafeMessage i) -> ErrorR i c -> I
errorNext i c ()  -- so we don't have to say how the state will evolve

ERROR : {I : Set}(SafeMessage : I -> Set) -> I => I
ERROR SafeMessage = ErrorC SafeMessage <! ErrorR / errorNext


---------------------------------------------------------------------------
-- COPY A FILE
---------------------------------------------------------------------------

{- 4.6 Implement a process which, given access to suitable interfaces, will
       give the process for copying a named source file to a named target
       file. You should:
         (1) construct the appropriate combination of interfaces
         (2) ensure that errors are appropriately signalled, including the
               text of any relevant filenames
         (3) ensure that all files are guaranteed by typechecking to be closed,
               whether or not there is an error
         (4) buffer as little data in memory as possible (so write early,
               write often)
-}

IndexCP : Set
IndexCP = (ReadState /*/ WriteState)

BothClosed : IndexCP -> Set
BothClosed (closed , closed) = String
BothClosed _ = Zero

InterfaceCP : IndexCP => IndexCP  -- (1 mark)
InterfaceCP = ERROR BothClosed =+= (READ <+> WRITE)

SuccessCP : IndexCP -> Set
SuccessCP (closed , closed) = One
SuccessCP _ = Zero

initialCP : IndexCP
initialCP = (closed , closed)

concat : List String -> String
concat [] = ""
concat (s :> ss) = primStringAppend s (concat ss)

{-# NO_TERMINATION_CHECK #-}
copyOpen : (b : Two) -> Game InterfaceCP SuccessCP (opened b , opened)
copyOpen tt = < inr (inl closeRead) , ( \ _ -> < inr (inr closeWrite) , ( \ _ -> win <> ) > ) >
copyOpen ff = < inr (inl readChar) , ( \ { (c , b) -> < inr (inr (writeChar c)) , (\ _ -> copyOpen b) > } ) >

-- (3 marks for beginning, middle, end)
cp : (sourceFile targetFile : String) -> Game InterfaceCP SuccessCP initialCP
cp sourceFile targetFile
  = < inr (inl (openRead sourceFile)) , (\
  { (opened b) ->
    < inr (inr (openWrite targetFile)) , ((\
    { opened -> copyOpen b
    ; closed -> < inr (inl closeRead) , (\ _ ->
        < inl (error (concat ("Could not open " :> targetFile :> []))) , (\ ()) >  ) >
    })) >
  ; closed -> < inl (error (concat ("Could not open " :> sourceFile :> []))) , (\ ()) > 
  }) >

-- (1 mark)
SCRIPT : {I : Set} -> I => I -> I => I
SCRIPT {I} CRn = Game CRn (\ I -> One) <! Rs / ns where
  Rs : (i : I) -> Game CRn (\ I -> One) i -> Set
  Rs i (win x) = One
  Rs i < c , k > = Sigma (Response CRn i c) \ r -> Rs (next CRn i c r) (k r)
  ns : (i : I)(cs : Game CRn (\ I -> One) i) -> Rs i cs -> I
  ns i (win x) rs = i
  ns i < c , k > (r , rs) = ns (next CRn i c r) (k r) rs

-- (1 mark)
unScript : {I : Set}(CRn : I => I){X : I -> Set}{i : I} ->
           Game (SCRIPT CRn) X i -> Game CRn X i
runScript : {I : Set}(CRn : I => I){X : I -> Set}{i : I} ->
            (cs : Command (SCRIPT CRn) i)
            (k : (rs : Response (SCRIPT CRn) i cs) ->
                   Game CRn X (next (SCRIPT CRn) i cs rs))
            -> Game CRn X i
unScript CRn (win x) = win x
unScript CRn {X}{i} < cs , k > = runScript CRn cs \ rs -> unScript CRn (k rs)

runScript CRn (win x) k = k <>
runScript CRn < c , f > k = < c , (\ r -> runScript CRn (f r) \ rs -> k (r , rs)) >

-- the rest was for fun
data Maybe (X : Set) : Set where
  yes : X -> Maybe X
  no  : Maybe X

data IOMode : Set where
  readMode writeMode appendMode readWriteMode : IOMode

postulate Handle : Set

data HaskellIOCommand (_ : One) : Set where
  hOpen : String -> IOMode -> HaskellIOCommand <>
  hClose hIsEOF hGetChar : Handle -> HaskellIOCommand <>
  hPutChar : Handle -> Char -> HaskellIOCommand <>
  hError : String -> HaskellIOCommand <>

HaskellIOResponse : (i : One) -> HaskellIOCommand i -> Set
HaskellIOResponse i (hOpen f m) = Maybe Handle
HaskellIOResponse i (hClose h) = One
HaskellIOResponse i (hIsEOF h) = Two
HaskellIOResponse i (hGetChar h) = Char
HaskellIOResponse i (hPutChar h c) = One
HaskellIOResponse i (hError e) = Zero

HASKELLIO : One => One
HASKELLIO = HaskellIOCommand <! HaskellIOResponse / _

record Driver {I J : Set}(Sync : I -> J -> Set)
              (Hi : I => I)(Lo : J => J) : Set where
  field
    hiClo :  (i : I)(j : J) -> Sync i j ->
             Command Hi i -> Command Lo j
    loRhi :  (i : I)(j : J)(s : Sync i j)(c : Command Hi i) ->
             Response Lo j (hiClo i j s c) -> Response Hi i c
    nSync :  (i : I)(j : J)(s : Sync i j)(c : Command Hi i)
             (r : Response Lo j (hiClo i j s c)) ->
             Sync (next Hi i c (loRhi i j s c r)) (next Lo j (hiClo i j s c) r)
open Driver public

RH : ReadState -> Set
RH (opened eof) = Handle
RH closed = One

WH : WriteState -> Set
WH opened = Handle
WH closed = One

hC : (i : IndexCP) (j : One) ->
     RH (outl i) /*/ WH (outr i) ->
     Command InterfaceCP i -> Command (SCRIPT HASKELLIO) j
hC (.closed , w) j (rh , wh) (inr (inl (openRead x)))
  = < hOpen x readMode , (\ { no -> win <> ;
      (yes h) -> < hIsEOF h , (\ b -> win <>) > }) >
hC (.(opened ff) , w) j (rh , wh) (inr (inl readChar))
  = < hGetChar rh , (\ c -> < hIsEOF rh , (\ b -> win <>) >) >
hC (._ , w) j (rh , wh) (inr (inl closeRead))
  = < hClose rh , (\ _ -> win <>) >
hC (r , .closed) j (rh , wh) (inr (inr (openWrite fileName)))
  = < hOpen fileName writeMode , (\ _ -> win <>) >
hC (r , .opened) j (rh , wh) (inr (inr (writeChar x)))
  = < hPutChar wh x , (\ _ -> win <>) >
hC (r , .opened) j (rh , wh) (inr (inr closeWrite))
  = < hClose wh , (\ _ -> win <>) >
hC (opened eof , opened) j (rh , wh) (inl (error ()))
hC (opened eof , closed) j (rh , wh) (inl (error ()))
hC (closed , opened) j (rh , wh) (inl (error ()))
hC (closed , closed) j (rh , wh) (inl (error e)) = < hError e , (\ ()) >
 
hR : (i : IndexCP) (j : One) (s : RH (outl i) /*/ WH (outr i))
     (c : Command InterfaceCP i) ->
     Response (SCRIPT HASKELLIO) j (hC i j s c) ->
     Response InterfaceCP i c
hR (.closed , w) j (<> , wh) (inr (inl (openRead x))) (yes rh , b , <>)
  = opened b
hR (.closed , w) j (<> , wh) (inr (inl (openRead x))) (no , <>)
  = closed
hR (.(opened ff) , w) j (rh , wh) (inr (inl readChar)) (c , b , <>) = c , b
hR (._ , w) j (rh , wh) (inr (inl closeRead)) rs = <>
hR (r , .closed) j (rh , <>) (inr (inr (openWrite fileName))) (yes wh , <>)
  = opened
hR (r , .closed) j (rh , <>) (inr (inr (openWrite fileName))) (no , <>)
  = closed
hR (r , .opened) j (rh , wh) (inr (inr (writeChar x))) rs = <>
hR (r , .opened) j (rh , wh) (inr (inr closeWrite)) rs = <>
hR (opened eof , opened) j (rh , wh) (inl (error ())) rs
hR (opened eof , closed) j (rh , wh) (inl (error ())) rs
hR (closed , opened) j (rh , wh) (inl (error ())) rs
hR (closed , closed) j (rh , wh) (inl (error x)) (() , snd)

hnS : (i : IndexCP) (j : One) (s : RH (outl i) /*/ WH (outr i))
      (c : Command InterfaceCP i)
      (r : Response (SCRIPT HASKELLIO) j (hC i j s c)) ->
      RH (outl (next InterfaceCP i c (hR i j s c r))) /*/
      WH (outr (next InterfaceCP i c (hR i j s c r)))
hnS (.closed , w) j (<> , wh) (inr (inl (openRead x))) (yes rh , snd) = rh , wh
hnS (.closed , w) j (<> , wh) (inr (inl (openRead x))) (no , snd) = <> , wh
hnS (.(opened ff) , w) j (rh , wh) (inr (inl readChar)) rs = rh , wh
hnS (._ , w) j (rh , wh) (inr (inl closeRead)) rs = <> , wh
hnS (r , .closed) j (rh , <>) (inr (inr (openWrite fileName))) (yes wh , snd)
  = rh , wh
hnS (r , .closed) j (rh , <>) (inr (inr (openWrite fileName))) (no , snd) = rh , <>
hnS (r , .opened) j (rh , wh) (inr (inr (writeChar x))) rs = rh , wh
hnS (r , .opened) j (rh , wh) (inr (inr closeWrite)) rs = rh , <>
hnS (opened eof , opened) j (rh , wh) (inl (error ())) rs
hnS (opened eof , closed) j (rh , wh) (inl (error ())) rs
hnS (closed , opened) j (rh , wh) (inl (error ())) rs
hnS (closed , closed) j (rh , wh) (inl (error x)) (() , snd)

safe2unsafe : Driver {IndexCP}{One} (\ { (r , w) j -> RH r /*/ WH w })
  InterfaceCP (SCRIPT HASKELLIO)
safe2unsafe = record
  { hiClo = hC
  ; loRhi = hR
  ; nSync = hnS
  }
```

##Exercise 5##

**problem file and mark scheme** `Ex5/Edit.agda`

```
module Edit where

{- This is the file where you should work. -}

open import AgdaSetup

{- The key editor data structure is the cursor. A Cursor M X represents
   being somewhere in the middle of a sequence of X values, holding an M. -}

record Cursor (M X : Set) : Set where
  constructor _<[_]>_
  field
    beforeMe  : Bwd X
    atMe      : M
    afterMe   : List X
infix 4 _<[_]>_

{- An editor buffer is a nested cursor: we're in the middle of a bunch of
   *lines*, holding a cursor for the current line, which puts us in the
   middle of a bunch of characters, holding the element of One. -}
Buffer : Set
Buffer = Cursor (Cursor One Char) (List Char)

{- This operator, called "chips", shuffles the elements from a backward list
   on to the start of a forward list, keeping them in the same order. -}
_<>>_ : {X : Set} -> Bwd X -> List X -> List X
[]         <>> xs  = xs
(xz <: x)  <>> xs  = xz <>> (x :> xs)

{- The "fish" operator goes the other way. -}
_<><_ : {X : Set} -> Bwd X -> List X -> Bwd X
xz <>< []         = xz
xz <>< (x :> xs)  = (xz <: x) <>< xs

{- You can turn a buffer into a list of lines, preserving its text. -}
bufText : Buffer -> List (List Char)
bufText
  (sz <[
   cz <[ <> ]> cs
   ]> ss)
  = sz <>> ((cz <>> cs) :> ss)

{- Here's an example of a proof of a fact about fish and chips. -}
firstFishFact : {X : Set} -> (xz : Bwd X)(xs : List X) ->
  (xz <>< xs) <>> []  ==  xz <>> xs
firstFishFact xz []          = refl
firstFishFact xz (x :> xs)   = firstFishFact (xz <: x) xs

{- You will need more such facts. -}

{- EXERCISE 5.1 -}
{- When we start the editor with the command
      ./Edit foo.txt
   the contents of foo.txt will be turned into a list of lines.
   Your (not so tricky) mission is to turn the file contents into a buffer which
   contains the same text.
   (1 mark)
-}
initBuf : List (List Char) -> Buffer
initBuf ss =
  [] <[
  [] <[ <> ]> []
  ]> []
{- As you can see, the current version will run, but it always gives the empty
   buffer, which is not what we want unless the input is empty. -}

{- Next comes the heart of the editor. You get a keystroke and the current buffer,
   and you have to say what is the new buffer. You also have to say what is the
   extent of the change.

   The tricky part is this: you have to be honest enough about your change
   report, so that we don't underestimate the amount of updating the screen needs.
-}

Honest : Buffer -> Change /*/ Buffer -> Set
Honest b (allQuiet    , b')                            = b == b'
Honest b (cursorMove  , b')                            = bufText b == bufText b'
Honest (sz <[ _ ]> ss) (lineEdit , (sz' <[ _ ]> ss'))  = (sz == sz') /*/ (ss == ss')
Honest _ (bigChange   , _)                             = One

record UpdateFrom (b : Buffer) : Set where   -- b is the starting buffer
  constructor _///_
  field
    update  : Change /*/ Buffer   -- change and new buffer
    honest  : Honest b update
open UpdateFrom
infix 2 _///_

{- EXERCISE 5.2 -}
{- Implement the appropriate behaviour for as many keystrokes as you can.
   I have done a couple for you, but I don't promise to have done them
   correctly. -}
keystroke : Key -> (b : Buffer) -> UpdateFrom b
keystroke (char c)
  (sz <[
   cz <[ <> ]> cs
   ]> ss)
  = lineEdit ,
  (sz <[
   cz <[ <> ]> c :> cs
   ]> ss)
  /// refl , refl          -- see? same above and below
keystroke (arrow normal right)
  (sz <: s <[
   [] <[ <> ]> cs
   ]> ss)
  = cursorMove ,
  (sz <[ ([] <>< s) <[ <> ]> [] ]> cs :> ss)
  /// within (\ x -> sz <>> (x :> cs :> ss)) turn s into ([] <>< s) <>> []
        because symmetry (firstFishFact [] s)
keystroke k b = allQuiet , b /// refl
{- Please expect to need to invent extra functions, e.g., to measure where you
   are, so that up and down arrow work properly. -}
{- Remember also that you can always overestimate the change by saying bigChange,
   which needs only a trivial proof. But you may find that the display will flicker
   badly if you do. -}
{- (char c)                 1 mark
   enter                    2 marks
   backspace delete         2 marks for the pair
   left right               2 marks for the pair (with cursorMove change)
   up down                  2 marks for the pair (with cursorMove change)
   -}


{- EXERCISE 5.3 -}
{- You will need to improve substantially on my implementation of the next component,
   whose purpose is to update the window. Mine displays only one line! -}
render :
  Nat /*/ Nat ->        -- height and width of window -- CORRECTION! width and height
  Nat /*/ Nat ->        -- first visible row, first visible column
  Change /*/ Buffer ->  -- what just happened
  List Action /*/       -- how to update screen
    (Nat /*/ Nat)       -- new first visible row, first visible column
render _ tl (allQuiet , _) = ([] , tl)
render _ tl (_ , (_ <[ cz <[ <> ]> cs ]> _))
  = (goRowCol 0 0 :> sendText (cz <>> cs) :> []) , tl
{- The editor window gives you a resizable rectangular viewport onto the editor buffer.
   You get told
     the current size of the viewport
     which row and col of the buffer are at the top left of the viewport
       (so you can handle documents which are taller or wider than the window)
     the most recent change report and buffer

   You need to figure out whether you need to move the viewport
       (by finding out if the cursor is still within the viewport)
     and if so, where to.

   You need to figure out what to redisplay. If the change report says
     lineEdit and the viewport has not moved, you need only repaint the
     current line. If the viewport has moved or the change report says
     bigChange, you need to repaint the whole buffer.

   You will need to be able to grab a rectangular region of text from the
     buffer, but you do know how big and where from.

   Remember to put the cursor in the right place, relative to where in
     the buffer the viewport is supposed to be. The goRowCol action takes
     *viewport* coordinates, not *buffer* coordinates! You will need to
     invent subtraction!
-}
{- Your code does not need to worry about resizing the window. My code does
   that. On detecting a size change, my code just calls your code with a
   bigChange report and the same buffer, so if you are doing a proper repaint,
   the right thing will happen. -}
{- 2 marks for ensuring that a buffer smaller than the viewport displays
       correctly, with the cursor in the right place, if nobody changes
       the viewport size
   2 marks for ensuring that the cursor remains within the viewport even if
       the viewport needs to move
   1 mark for ensuring that lineEdit changes need only affect one line of
       the display (provided the cursor stays in the viewport)
-}

{- FOR MASOCHISTS ONLY, you have a chance to be even more creative. You have
   spare detectable keys that you could invent meanings for. You also have the
   freedom to change the definition of Buffer, as my code does not care what
   a Buffer is: it only needs to know how to initialize, update and render,
   and these are defined by you.

   Additional structural cursor moves (beginning and end of line, etc) are quite
   easy. Going left or right word-by-word would be more fun: you can match
   against a pattern such as ' '.

   Selection and cut/copy/paste are more challenging. For these, you need to
   modify the Buffer structure to remember the clipboard contents (if any),
   and to manage the extent of any selected region.

   If you feel the need to vary the foreground or background colour of the displayed
   text (e.g. to show a selection), please let me know.

   (SUBTEXT: this exercise is a cut-down version of last year's post-Easter
   task. Feel free to ignore the cutting-down.)
-}


{- Your code then hooks into mine to produce a top level executable! -}
main : IO One
main = mainLoop initBuf (\ k b -> update (keystroke k b)) render

{- To build the editor, just do
     make
   in a shell window (with Ex5 the current directory).
   To run the editor, once compiled, do
     ./Edit
   in the shell window, which should become the editor window.
   To quit the editor, do
     ctrl-C
   like an old-fashioned soul.
-}

{- There is no one right way to do this exercise, and there is some scope for
   extension. It's important that you get in touch if you need help, either in
   achieving the basic deliverable, or in finding ways to explore beyond it.
-}
```
