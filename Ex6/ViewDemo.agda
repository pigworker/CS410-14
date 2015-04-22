module ViewDemo where

open import Ex6-Setup

_++_ : {X : Set} -> List X -> List X -> List X
[] ++ ys = ys
(x :: xs) ++ ys = x :: xs ++ ys
infixr 6 _++_

map : {S T : Set} -> (S -> T) -> List S -> List T
map f []        = []
map f (s :: ss) = f s :: map f ss

allRight : {S T : Set} -> List (S /+/ T) -> One /+/ List T
allRight [] = inr []
allRight (inl s :: xs) = inl <>
allRight (inr t :: xs) with allRight xs
allRight (inr t :: xs) | inl <> = inl <>
allRight (inr t :: xs) | inr ts = inr (t :: ts)


data AllRightable {S T : Set} : List (S /+/ T) -> Set where
  isAllRight : (ts : List T) -> AllRightable (map inr ts)
  hasFirstLeft : (ts : List T)(s : S)(xs : List (S /+/ T)) ->
    AllRightable (map inr ts ++ inl s :: xs)

allRightable : {S T : Set}(xs : List (S /+/ T)) -> AllRightable xs
allRightable [] = isAllRight []
allRightable (inl s :: xs) = hasFirstLeft [] s xs
allRightable (inr t :: xs)                        with allRightable xs
allRightable (inr t :: .(map inr ts))                | isAllRight ts
  = isAllRight (t :: ts)
allRightable (inr t :: .(map inr ts ++ inl s :: xs)) | hasFirstLeft ts s xs
  = hasFirstLeft (t :: ts) s xs
