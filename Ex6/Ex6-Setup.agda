module Ex6-Setup where


---------------------------------------------------------------------------
-- NATURAL NUMBERS                                                       --
---------------------------------------------------------------------------

data Nat : Set where
  zero : Nat
  suc : Nat -> Nat
{-# BUILTIN NATURAL Nat #-}
{-# COMPILED_DATA Nat HaskellSetup.Nat HaskellSetup.Zero HaskellSetup.Suc #-}

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
open Sg public
_/*/_ : Set -> Set -> Set
S /*/ T = Sg S \ _ -> T
infixr 3 _/*/_
infixr 3 _,_


---------------------------------------------------------------------------
-- EQUALITY, AND SOME FACTS ABOUT SUC AND ADDITION                       --
---------------------------------------------------------------------------

data _==_ {X : Set}(x : X) : X -> Set where
  refl : x == x
infixr 4 _==_

transitivity : {X : Set}{x y z : X} -> x == y -> y == z -> x == z
transitivity refl q = q

sucInj : {x y : Nat} -> suc x == suc y -> x == y
sucInj refl = refl

sucResp : {x y : Nat} -> x == y -> suc x == suc y
sucResp refl = refl

plusZeroFact : (x : Nat) -> x + zero == x
plusZeroFact zero     = refl
plusZeroFact (suc x)  = sucResp (plusZeroFact x)

plusSucFact : (x y : Nat) -> x + suc y == suc (x + y)
plusSucFact zero y = refl
plusSucFact (suc x) y = sucResp (plusSucFact x y)

plusCommFact : (x y : Nat) -> y + x == x + y
plusCommFact zero y = plusZeroFact y
plusCommFact (suc x) y
  = transitivity (plusSucFact y x) (sucResp (plusCommFact x y))


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

_+-+_ : {X : Set} -> List X -> List X -> List X
[] +-+ ys = ys
(x :: xs) +-+ ys = x :: (xs +-+ ys)
infixr 6 _+-+_

concat : {X : Set} -> List (List X) -> List X
concat [] = []
concat (xs :: xss) = xs +-+ concat xss

list : {X : Set} -> Nat -> X -> List X
list zero x = []
list (suc n) x = x :: list n x


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
-- ORDINARY SUMS                                                         --
---------------------------------------------------------------------------

data _/+/_ (S T : Set) : Set where
  inl : S -> S /+/ T
  inr : T -> S /+/ T
infixr 2 _/+/_
{-# COMPILED_DATA _/+/_ Either Left Right #-}


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


---------------------------------------------------------------------------
-- IO IN HASKELL                                                         --
---------------------------------------------------------------------------

postulate -- Haskell has a monad for doing IO, which is our route out
  IO      : Set -> Set
  return  : {A : Set} -> A -> IO A
  _>>=_   : {A B : Set} -> IO A -> (A -> IO B) -> IO B
infixl 1 _>>=_
{-# BUILTIN IO IO #-}
{-# COMPILED_TYPE IO IO #-}
{-# COMPILED return (\ _ -> return)    #-}
{-# COMPILED _>>=_  (\ _ _ -> (>>=)) #-}


---------------------------------------------------------------------------
-- KEYS                                                                  --
---------------------------------------------------------------------------

{- Here's the characterization of keys I give you -}
data Direction : Set where up down left right : Direction
data Modifier : Set where normal shift control : Modifier
data Key : Set where
  char       : Char -> Key
  arrow      : Modifier -> Direction -> Key
  enter      : Key
  backspace  : Key
  delete     : Key
  escape     : Key
  tab        : Key
data Event : Set where
  key     : (k : Key) -> Event
  resize  : (w h : Nat) -> Event

{-# IMPORT ANSIEscapes #-}
{-# IMPORT HaskellSetup #-}
{-# COMPILED_DATA Direction
      ANSIEscapes.Direction
      ANSIEscapes.DU ANSIEscapes.DD ANSIEscapes.DL ANSIEscapes.DR #-}
{-# COMPILED_DATA Modifier 
      HaskellSetup.Modifier
      HaskellSetup.Normal HaskellSetup.Shift HaskellSetup.Control #-}
{-# COMPILED_DATA Key
      HaskellSetup.Key
      HaskellSetup.Char HaskellSetup.Arrow HaskellSetup.Enter
      HaskellSetup.Backspace HaskellSetup.Delete HaskellSetup.Escape
      HaskellSetup.Tab #-}
{-# COMPILED_DATA Event
      HaskellSetup.Event
      HaskellSetup.Key HaskellSetup.Resize #-}


---------------------------------------------------------------------------
-- COLOURS                                                               --
---------------------------------------------------------------------------

data Colour : Set where
  black red green yellow blue magenta cyan white : Colour
{-# COMPILED_DATA Colour HaskellSetup.Colour
      HaskellSetup.Black HaskellSetup.Red HaskellSetup.Green
      HaskellSetup.Yellow HaskellSetup.Blue HaskellSetup.Magenta
      HaskellSetup.Cyan HaskellSetup.White #-}


---------------------------------------------------------------------------
-- ACTIONS                                                               --
---------------------------------------------------------------------------

data Action : Set where
  goRowCol : Nat -> Nat -> Action  -- top left is zero zero
  sendText : List Char -> Action
  move     : Direction -> Nat -> Action  -- which way and how much
  fgText   : Colour -> Action
  bgText   : Colour -> Action
{-# COMPILED_DATA Action HaskellSetup.Action
      HaskellSetup.GoRowCol HaskellSetup.SendText HaskellSetup.Move
      HaskellSetup.FgText HaskellSetup.BgText #-}


---------------------------------------------------------------------------
-- HASKELL TUPLES                                                        --
---------------------------------------------------------------------------

data _/**/_ (S T : Set) : Set where
  _,_ : S -> T -> S /**/ T
{-# COMPILED_DATA _/**/_ (,) (,) #-}

data Thud : Set where <> : Thud
{-# COMPILED_DATA Thud () () #-}


