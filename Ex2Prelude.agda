module Ex2Prelude where

open import Ex1Prelude

All : {X : Set}            -- element type
      -> (X -> Set)        -- property of elements
      -> List X -> Set     -- property of whole lists
All P []         = One
All P (x :> xs)  = P x /*/ All P xs

{- If X = One, then List X is like a copy of Nat, and All is a bit like Vec -}
