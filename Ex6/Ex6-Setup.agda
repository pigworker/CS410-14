module Ex6-Setup where


---------------------------------------------------------------------------
-- NATURAL NUMBERS                                                       --
---------------------------------------------------------------------------

data Nat : Set where
  zero : Nat
  suc : Nat -> Nat
{-# BUILTIN NATURAL Nat #-}

_+_ : Nat -> Nat -> Nat
zero + y = y
suc x + y = suc (x + y)

infixr 5 _+_


---------------------------------------------------------------------------
-- ONE, SIGMA TYPES AND BINARY PRODUCT                                   --
---------------------------------------------------------------------------

record One : Set where constructor <>

record Sg (S : Set)(T : S -> Set) : Set where
  constructor _,_
  field
    fst : S
    snd : T fst
open Sg
_/*/_ : Set -> Set -> Set
S /*/ T = Sg S \ _ -> T
infixr 3 _/*/_
infixr 3 _,_


---------------------------------------------------------------------------
-- EQUALITY, AND SOME FACTS ABOUT SUC                                    --
---------------------------------------------------------------------------

data _==_ {X : Set}(x : X) : X -> Set where
  refl : x == x
infixr 4 _==_

sucInj : {x y : Nat} -> suc x == suc y -> x == y
sucInj refl = refl

sucResp : {x y : Nat} -> x == y -> suc x == suc y
sucResp refl = refl


---------------------------------------------------------------------------
-- IDENTITY AND COMPOSITION FUNCTIONS                                    --
---------------------------------------------------------------------------

id : {X : Set} -> X -> X
id x = x

_o_ : {X : Set}{Y : X -> Set}{Z : (x : X) -> Y x -> Set}
      (f : {x : X}(y : Y x) -> Z x y)(g : (x : X) -> Y x) ->
      (x : X) -> Z x (g x)
(f o g) x = f (g x)


---------------------------------------------------------------------------
-- ORDINARY LISTS                                                        --
---------------------------------------------------------------------------

data List (X : Set) : Set where
  []    : List X
  _::_  : X -> List X -> List X
infixr 6 _::_

{-# COMPILED_DATA List [] [] (:) #-}
{-# BUILTIN LIST List #-}
{-# BUILTIN NIL [] #-}
{-# BUILTIN CONS _::_ #-}


---------------------------------------------------------------------------
-- ORDINARY BOOLEANS                                                     --
---------------------------------------------------------------------------

data Two : Set where
  tt ff : Two
{-# BUILTIN BOOL  Two  #-}
{-# BUILTIN TRUE  tt  #-}
{-# BUILTIN FALSE ff #-}
{-# COMPILED_DATA Two Bool True False #-}


---------------------------------------------------------------------------
-- CHARACTERS AND STRINGS                                                --
---------------------------------------------------------------------------
postulate       -- we just suppose the following things exist...
  Char : Set
  String : Set
{-# BUILTIN CHAR Char #-}
{-# COMPILED_TYPE Char Char #-}      -- ...and by the time we reach Haskell...
{-# BUILTIN STRING String #-}
{-# COMPILED_TYPE String String #-}  -- ...they *do* exist!

primitive       -- these are baked in; they even work!
  primCharEquality    : Char -> Char -> Two
  primStringAppend    : String -> String -> String
  primStringToList    : String -> List Char
  primStringFromList  : List Char -> String
