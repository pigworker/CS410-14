module Zipper where

open import Ex1Prelude
open import FuncKit


data Tree (X : Set) : Set where
  leaf : Tree X
  _<[_]>_ : Tree X -> X -> Tree X -> Tree X

data Context (X : Set) : Set where
  root : Context X
  lefty : Context X -> X -> Tree X -> Context X
  righty : Tree X -> X -> Context X -> Context X

data Layer (X : Set) : Set where
  lefty : One -> X -> Tree X -> Layer X
  righty : Tree X -> X -> One -> Layer X

-- take Context X = List (Layer X)

TreeZipper : Set -> Set
TreeZipper X = Context X /*/ Tree X

getOutHelp : {X : Set} -> Context X -> Tree X -> Tree X
getOutHelp root t = t
getOutHelp (lefty c x r) t = getOutHelp c (t <[ x ]> r)
getOutHelp (righty l x c) t = getOutHelp c (l <[ x ]> t)

getOut : {X : Set} -> TreeZipper X -> Tree X
getOut (c , t) = getOutHelp c t
{- -- termination checker says no
getOut (root , t) = t
getOut (lefty c x r , t) = getOut (c , (t <[ x ]> r))
getOut (righty l x c , t) = getOut (c , (l <[ x ]> t))
-}

Maybe : Set -> Set
Maybe X = One /+/ X

goLeft : {X : Set} -> TreeZipper X -> Maybe (TreeZipper X)
goLeft (c , leaf) = inl <>
goLeft (c , l <[ x ]> r) = inr (lefty c x r , l)

layer : Kit -> Kit
layer (kK A)   = kK Zero
layer kId      = kK One
layer (j k+ k) = layer j k+ layer k
layer (j k* k) = (layer j k* k) k+ (j k* layer k)

plug : (k : Kit) -> {X : Set} -> kFun (layer k) X -> X -> kFun k X
plug (kK A) () x
plug kId <> x = x
plug (j k+ k) (inl j') x = inl (plug j j' x)
plug (j k+ k) (inr k') x = inr (plug k k' x)
plug (j k* k) (inl (j' , k')) x = plug j j' x , k'
plug (j k* k) (inr (j' , k')) x = j' , plug k k' x

KLayer : Kit -> Set
KLayer k = kFun (layer k) (Data k)

kOut1 : (k : Kit) -> KLayer k -> Data k -> Data k
kOut1 k l d = [ plug k l d ]

