module Ex6-1-Vec-Sol where

open import Ex6-Setup


---------------------------------------------------------------------------
-- VECTORS (5 marks)                                                     --
---------------------------------------------------------------------------

-- We've touched on them before, when we needed to manage the height of a
-- stack, but here are the "vectors", or "lists of known length.

data Vec (X : Set) : Nat -> Set where
  []    : Vec X zero
  _::_  : {n : Nat} -> X -> Vec X n -> Vec X (suc n)
infixr 6 _::_

-- This chunk of exercise 6 is about building the basic equipment to work
-- with vectors. We'll need this equipment later.


---------------------------------------------------------------------------
-- CONCATENATION AND ITS INVERSE                                         --
---------------------------------------------------------------------------

infixr 6 _++_

-- Implement concatenation for any two vectors.
-- You will need to say how long the result will be.
-- (1 mark)

_++_ : {X : Set}{m n : Nat} -> Vec X m -> Vec X n -> Vec X (m + n)
[] ++ ys = ys
(x :: xs) ++ ys = x :: xs ++ ys
-- Now, we could write "take" and "drop", but it's more useful to
-- prove that every long vector can be given by concatenating two
-- short vectors.

data Chop {X : Set}(m : Nat){n : Nat} : Vec X (m + n) -> Set where
  is++ : (xs : Vec X m)(ys : Vec X n) -> Chop m (xs ++ ys)

-- A "Chop" for a given vector consists of the evidence that it can
-- be made by concatenation. You will need to fill in the Chop length,
-- above, the same way you filled in the length for _++_.

-- Show that you can compute a Chop for any vector.
-- Hint: you will need to use "with" at some point.
-- (1 mark)

chop : {X : Set}(m : Nat){n : Nat}(xs : Vec X (m + n)) -> Chop m xs
chop zero xs = is++ [] xs
chop (suc m) (x :: xs) with chop m xs
chop (suc m) (x :: .(xs ++ ys)) | is++ xs ys = is++ (x :: xs) ys

-- Where take and drop give you vectors which you *hope* are the prefix
-- and suffix of the input. Chop gives you the pieces which are seen to
-- be the prefix and suffix of the input. Once you have chop, it's easy
-- to write take and drop in terms of it, and you can see they're right.
-- Try uncommenting and finishing the following (for fun).

take : {X : Set}(m : Nat){n : Nat}(xs : Vec X (m + n)) -> Vec X m
take m xs       with chop m xs
take m .(xs ++ ys) | is++ xs ys = xs

-- EXTRA! For no marks, but some utility in future, check that you can
-- use chop to define the function which just gives you the pair of the
-- prefix and the suffix.

vchop : {X : Set}(m : Nat){n : Nat} ->
        Vec X (m + n) -> Vec X m /*/ Vec X n
vchop m xs with chop m xs
vchop m .(xs ++ ys) | is++ xs ys = xs , ys


---------------------------------------------------------------------------
-- APPLICATIVE STRUCTURE                                                 --
---------------------------------------------------------------------------

-- Implement the function which makes a vector from a single element by
-- copying it the relevant number of times. Implement the "vectorized
-- application" operator which takes n functions and n arguments and gives
-- you the n results: the jth result should be given by applying the jth
-- function to the jth argument.
-- (1 mark)

vec : {n : Nat}{X : Set}(x : X) -> Vec X n
vec {zero} x = []
vec {suc n} x = x :: vec x

_<*>_ : {n : Nat}{S T : Set} -> Vec (S -> T) n -> Vec S n -> Vec T n
[] <*> [] = []
f :: fs <*> s :: ss = f s :: (fs <*> ss)
infixl 2 _<*>_

-- The applicative structure is very useful for working with vectors in
-- bulk. For example, I can take the successor of every number in a vector
-- by applying a vector of successor-functions to the vector of numbers.

mySucs : Vec Nat 5
mySucs = vec suc <*> (0 :: 1 :: 2 :: 3 :: 4 :: [])
-- should evaluate to 1 :: 2 :: 3 :: 4 :: 5 :: []

-- Now, using vec and <*> rather than explicit case analysis and recursion,
-- implement vector zipping as a one-liner, turning a pair of vectors into a
-- vector of pairs.
-- (1 mark)

zip : {n : Nat}{X Y : Set} -> Vec X n -> Vec Y n -> Vec (X /*/ Y) n
zip xs ys = vec _,_ <*> xs <*> ys

-- Play the same game as we did for concatenation, take and drop. Show
-- that every vector of pairs can be made by zipping two vectors.
-- (1 mark)

data Unzip {n : Nat}{X Y : Set} : Vec (X /*/ Y) n -> Set where
  isZip : (xs : Vec X n)(ys : Vec Y n) -> Unzip (zip xs ys)

unzip : {n : Nat}{X Y : Set}(xys : Vec (X /*/ Y) n) -> Unzip xys
unzip [] = isZip [] []
unzip ((x , y) :: xys) with unzip xys
unzip ((x , y) :: .(zip xs ys)) | isZip xs ys = isZip (x :: xs) (y :: ys)

-- EXTRA! For no marks, but some utility in future, check that you can
-- use unzip to define the function which just gives you the pair of the
-- two vectors.

vunzip : {X Y : Set}{n : Nat} -> Vec (X /*/ Y) n -> Vec X n /*/ Vec Y n
vunzip xys with unzip xys
vunzip .(vec _,_ <*> xs <*> ys) | isZip xs ys = xs , ys
