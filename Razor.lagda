\chapter{Hutton's Razor}

This chapter is inspired by Professor Graham Hutton, author of
\emph{Programming in Haskell}. We investigate various topics
in the semantics (static and dynamic) of programming languages
by considering minimal extensions to a very simple programming
language---the expressions built from addition and natural numbers.
The idea is that adding up numbers is indicative of `ordinary
computation' in general, and we need add only the extra features
required to expose whatever departure from the ordinary we care
about. Why use complicated examples when simple ones will do?
Graham champions simplicity, and thus gives very clear explanations
of important things. His friends call the adding-up-numbers language
\emph{Hutton's Razor} in his honour.

%format Razor = "\M{Razor}"
\begin{code}
module Razor where

open import BasicPrelude
\end{code}

Without further ado, let us have a datatype of expressions.

%format Expr = "\D{Expr}"
%format val = "\C{val}"
%format plus = "\C{plus}"
\begin{code}
data Expr : Set where
  val   : Nat -> Expr
  plus  : Expr -> Expr -> Expr
\end{code}

Evaluating expressions is quite easy. Let us do it. The essence of it
is to replace the type |Expr| of syntactic things with a type of
semantic values, in this case, |Nat| itself. To do that, we need to
replace the constructors, which make syntactic things, with semantic
counterparts. In effect, |val| becomes |id| and |plus| becomes |+|.

%format Val = "\F{Val}"
%format eval = "\F{eval}"
\begin{code}
Val : Set
Val = Nat

eval : Expr -> Val
eval (val n)       = n
eval (plus e1 e2)  = eval e1 + eval e2
\end{code}