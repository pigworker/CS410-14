module ViewDemo where

open import Ex6-Setup

-- This file gives an example of the "view" method, which allows us to write
-- testing operations which actually generate evidence about the things being
-- tested, and in a very visual way. You get to develop more powerful ways of
-- seeing.

-- I recommend commenting out the example code, then redeveloping it
-- interactively, which will give you a much more animated experience of
-- what is going on.

map : {S T : Set} -> (S -> T) -> List S -> List T
map f []        = []
map f (s :: ss) = f s :: map f ss

-- Note, +-+ is concatenation for lists, here, to leave ++ for vectors.

-- trying to find out whether a list of choices all chooses inr

allRight : {S T : Set} -> List (S /+/ T) -> One /+/ List T
allRight [] = inr []  -- trivially all right
allRight (inl s :: xs) = inl <> -- busted!
-- Now the interesting case:
{-
allRight (inr t :: xs) = {!!}
-}
-- We need to know the situation about xs, so here's what to do
-- before the = sign, do a bit of typing to get
{-
allRight (inr t :: xs) with allRight xs
... | r = ?
-}
-- What does that mean? It means we want to be able to see everything
-- we had before on the left-hand side, but also the result of the
-- recursive call. The next line looks like
-- <pattern for main call> | <pattern for extra stuff> = ?
-- but we're allowed to write "..." when, left of |, nothing has changed
-- from the line containing "with". The "r" is just a freshly named
-- pattern variable. Now reload the file, and it's
{-
allRight (inr t :: xs) with allRight xs
... | r = {!!}
-}
-- Next, do case analysis on r! The "..." expands and you see the whole
-- picture.
allRight (inr t :: xs) with allRight xs
allRight (inr t :: xs) | inl <> = inl <>
allRight (inr t :: xs) | inr ts = inr (t :: ts)

-- Here's a more informative way to write the same test. Instead of
-- returning some bits and pieces which we *hope* tell us something
-- about the input, we *demand* to know what the input looks like

-- We introduce a list-dependent type which describes the possible things
-- that list can be. There is one constructor for each possibility.
-- Think of (AllRightable xs) as the type of "knowing whether xs is all
-- right". We know if we can tell these two cases apart.
-- This technique is known as declaring a "view" of some data.
data AllRightable {S T : Set} : List (S /+/ T) -> Set where
  -- is it made from a bunch of ts, all wrapped with inr?
  isAllRight : (ts : List T) -> AllRightable (map inr ts)
  -- or does it have some ts, then a first s, then some more stuff?
  hasFirstLeft : (ts : List T)(s : S)(xs : List (S /+/ T)) ->
    AllRightable (map inr ts +-+ inl s :: xs)

-- Next, show that we can always know. That is, we establish that we can
-- see the data according to the declared "view".
-- You write the program with exactly the same case analysis and "with"
-- steps as the above, but when you come to fill in the return values,
-- just use C-c C-a. There is no choice: the type is an exact specification
-- of the analysis, so you can't lie and say you found an s that wasn't
-- there. But there's something else.
allRightable : {S T : Set}(xs : List (S /+/ T)) -> AllRightable xs
allRightable [] = isAllRight []
allRightable (inl s :: xs) = hasFirstLeft [] s xs
allRightable (inr t :: xs)                        with allRightable xs
-- As before we start from this after "with"
{-
... | r = {!!}
-}
-- but when we do a case split on r, something wonderful happens!
-- In each case, we see the list for what it really is.
allRightable (inr t :: .(map inr ts))                | isAllRight ts
  = isAllRight (t :: ts)
-- In your face, it's all on the right.

allRightable (inr t :: .(map inr ts +-+ inl s :: xs)) | hasFirstLeft ts s xs
  = hasFirstLeft (t :: ts) s xs
-- In your face, it has a leftmost inl s.

-- Patterns which start with . are a new thing. Normally, when you write a
-- pattern, you are *asking* what is present. When you write (or rather,
-- when you get Agda to write) a .-pattern, you are *telling* what is present.
-- Operationally, a .-pattern means "don't bother looking at that because we
-- already know what it is". They exist for code comprehension purposes,
-- to show you exactly what you've got in your hand.
