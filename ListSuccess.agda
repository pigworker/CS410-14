module ListSuccess where

open import Ex1Prelude


_++_ : {X : Set} -> List X -> List X -> List X
[] ++ ys = ys
x :> xs ++ ys = x :> (xs ++ ys)

infixr 3 _++_

win : {X : Set} -> X -> List X
win x = x :> []

_>>=_ : {X Y : Set} -> List X -> (X -> List Y) -> List Y
[] >>= x2ys = []
(x :> xs) >>= x2ys = (x2ys x) ++ xs >>= x2ys

try2 : {R S T : Set} -> (R -> S -> T) -> List R -> List S -> List T
try2 f rs ss = rs >>= (\ r -> ss >>= \ s -> win (f r s))
