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

Without further ado, let us have a datatype of `Hutton expressions'.

%format HExp = "\D{HExp}"
%format val = "\C{val}"
%format +++ = "\C{+\!\!\!\!+\!\!\!\!+}"
%format _+++_ = _ +++ _
\begin{code}
data HExp : Set where
  val    : Nat -> HExp
  _+++_  : HExp -> HExp -> HExp
\end{code}

Evaluating expressions is quite easy. Let us do it. The essence of it
is to replace the type |HExp| of syntactic things with a type of
semantic values, in this case, |Nat| itself. To do that, we need to
replace the constructors, which make syntactic things, with semantic
counterparts. In effect, |val| becomes |id| and |+++| becomes |+|.

%format Val = "\F{Val}"
%format eval = "\F{eval}"
%format e1 = "\V{e_1}"
%format e2 = "\V{e_2}"
\begin{code}
Val : Set
Val = Nat

eval : HExp -> Val
eval (val n)      = n  -- which is equal to |id n|
eval (e1 +++ e2)  = eval e1 + eval e2
\end{code}

So
\begin{spec}
eval ((val 1 +++ val 2) +++ val 3) = ((id 1 + id 2) + id 3) = 6
\end{spec}

We could think up other ways to interpret the syntax of Hutton's
Razor. We might, for example, just collect the list of numerical
constants which occur in an expression.

%format constants = "\F{constants}"
\begin{code}
constants : HExp -> List Nat
constants (val n)      = n :> []
constants (e1 +++ e2)  = constants e1 ++ constants e2
\end{code}

An interpretation of a bunch of operators for a given `value type' |T| is called
an \textbf{algebra} for those operators: |T| is called the \textbf{carrier} of the
algebra. That is |id| and |+| give an algebra for |HExp| with carrier |Val|;
|(\ n -> n :> [])| and |++| give an algebra for |HExp| with carrier |List Nat|.
Of course, |val| and |+++| give an algebra for |HExp| with carrier |HExp|, and we
call it the \textbf{free} algebra because it is not obliged to obey any mathematical
laws. E.g., we expect |+| to be associative, and more to the point, we expect |2 + 2 = 4|,
but |val 2 +++ val 2| is \emph{not} the same \emph{expression} as |val 4|. So you can
think of `free' as meaning `nothing more than syntax'.

For the rest of this chapter, we shall explore variations on the theme of Hutton's
Razor, illustrative of all sorts of computational ideas, in search of common patterns.


\section{Compiling for a Stack Machine}

Our first variation is to consider |compiling| rather than |interpreting| Hutton's Razor.
The compilation target will be a simple machine which manages the evaluation process via
a \emph{stack}. The machine has just two instructions:
\begin{description}
\item[\texttt{PUSH} |n|] puts the number |n| on top of the stack;
\item[\texttt{ADD}] pops |n| and then |m| from the stack, then pushes |m + n|.
\end{description}
Our mission is to write a compiler which turns an expression into a sequence of
these instructions which leaves the expression's value on the top of the stack,
with the original stack below. For example, compiling |(val 2 +++ val 3) +++ val 1|
should give us
\begin{verbatim}
    code              stack after instruction

                      ...
    PUSH 2            2 , ...
    PUSH 3            3 , 2 , ...
    ADD               5 , ...
    PUSH 1            1 , 5 , ...
    ADD               6 , ...
\end{verbatim}

Correspondingly, let me give a type for code sequences. (I grew up in the 1970s, so
assembly language operators are in ALL CAPS.)
%format HCode = "\D{HCode}"
%format PUSH = "\C{PUSH}"
%format ADD = "\C{ADD}"
%format -SEQ- = "\C{-SEQ-}"
%format _-SEQ-_ = _ -SEQ- _
\begin{code}
data HCode : Set where
  PUSH     : Nat -> HCode
  ADD      : HCode
  _-SEQ-_  : HCode -> HCode -> HCode
infixr 3 _-SEQ-_
\end{code}
That is, we have our two instructions, along with a \emph{sequential composition}
operator, allowing us to plug programs together. I could have used \emph{lists} of
instructions, but this gives a slightly simpler and more extensible treatment: watch
this space.

Based on our informal description of what the stack machine code should do, we can
have a go at implementing the compiler.
%format compile = "\F{compile}"
%format c1 = "\V{c_1}"
%format c2 = "\V{c_2}"
\begin{code}
compile : HExp -> HCode
compile (val n)      = PUSH n
compile (e1 +++ e2)  = compile e1 -SEQ- compile e2 -SEQ- ADD
\end{code}
That is, we have implemented yet another algebra for |HExp|, this time with carrier
|HCode|, with |PUSH| for |val| and |\ c1 c2 -> c1 -SEQ- c2 -SEQ- ADD| for |+++|.

%format exec = "\F{exec}"
However, if we want to see it working, we need to say how to \emph{execute} programs
in |HCode|. We need to write some
\[
  |exec : HCode -> List Nat -> List Nat|
\]
interpreting code as a function from the initial stack (represented as a list) to the
final stack. We need to give an algebra for |HCode| with carrier |List Nat -> List Nat|.
But when we try, we hit a snag.
%if False
\begin{code}
postulate HOLE : Nat -> {X : Set} -> X
\end{code}
%endif
%format (HOLE n) = "\greenBG{\ensuremath{\{\;\}" n "}}"
\begin{code}
exec : HCode -> List Nat -> List Nat
exec (PUSH x)       s                = x :> s
exec ADD            []               = (HOLE 0)
exec ADD            (n :> [])        = (HOLE 1)
exec ADD            (n :> (m :> s))  = (m + n) :> s
exec (c1 -SEQ- c2)  s                = exec c2 (exec c1 s)
\end{code}
We are obliged to say what happens when there are not enough values in the stack for the
correct execution of |ADD|. How will we handle stack \emph{underflow}? We could just give
back any old rubbish, but then we would have to worry that the old rubbish we give back
might actually happen, when we intend that underflow should \emph{never} happen. Moreover,
if we have been competent, at least the |HCode| which comes from |compile| will never
cause underflow.

It is clear that we need to manage the height of the stack somehow, and Agda lets us do it
with \emph{types}. We can express requirements and guarantees about the length of lists by
working with the type of \emph{vectors}, or `lists indexed by their length'.
%format Vec = "\D{Vec}"
\begin{code}
data Vec (X : Set) : Nat -> Set where
  []    : Vec X zero
  _:>_  : {n : Nat} -> X -> Vec X n -> Vec X (suc n)
\end{code}
The type constructor |Vec| now has the type
\[
|Vec : Set -> Nat -> Set|
\]
so that, for example, |Vec Two 8| is the type of bit-vectors of length \emph{exactly} 8.
You can see that, as with list, we have a type |(X : Set)| of elements declared left of
the |:| in the head of the |data| declaration, so it scopes over the whole of the rest
of the declaration. By writing |Nat -> Set| instead of |Set| to the right of |:|, we are
saying that we want a whole \emph{family} of vector types, one for each length, and that
we want to be free to choose the lengths that show up in the constructor types. Specifically,
we fix it so that |[]| makes only vectors with length |zero| and that |x :> xs| has length
one more than |xs|. The curly braces in |{n : Nat} ->| mean that the |n| which gives the
length of the vector's tail will be kept hidden by default.

By the same facility, we can refine |HCode| with our knowledge of how instructions affect
stack height. This time, we index by two numbers, respectively representing the initial
and final heights of the stack when the code is executed.
%format HCodeI = HCode
\begin{code}
data HCodeI : Nat -> Nat -> Set where
  PUSH     : {i : Nat} -> Nat -> HCodeI i (suc i)       -- one goes on
  ADD      : {i : Nat} -> HCodeI (suc (suc i)) (suc i)  -- two off, one on
  _-SEQ-_  : {i j k : Nat} -> HCodeI  i j -> HCodeI j k -> HCodeI i k
                                      -- dominoes!
\end{code}
We can use |ADD| only in situations where it is known that there is enough stuff on the
stack. We have made underflow \emph{impossible}!

%format execI = exec
Now, we can give |execI| a type that makes the promise implicit in our claim that the
indices of |HCodeI| represent the initial and final stack heights: we should input a
stack of the initial height and output a stack of the final height. The code keeps the
promise.
\begin{code}
execI : {i j : Nat} -> HCodeI i j -> Vec Nat i -> Vec Nat j
execI (PUSH x)       s                = x :> s
execI ADD            (x :> (y :> s))  = (y + x) :> s
execI (c1 -SEQ- c2)  s                = execI c2 (execI c1 s)
\end{code}
If you build this program, you will see that the underflow cases do not even appear.
To see what is going on, let me use the `manual override' syntax to show you some of
the hidden numbers.
%format execIx = exec
%format . = ".\!\!"
\begin{code}
execIx : {i j : Nat} -> HCodeI i j -> Vec Nat i -> Vec Nat j
execIx .{i}            .{suc i}  (PUSH {i} n)               s              
  = n :> s
execIx .{suc (suc i)}  .{suc i}  (ADD {i})                  (n :> (m :> s))
  = (m + n) :> s
execIx .{i}            .{k}      (_-SEQ-_ {i}{j}{k} c1 c2)  s              
  = execIx {j} {k} c2 (execIx {i} {j} c1 s)
\end{code}
The curly braces show the height information which is usually hidden in the calls to
|execIx| and in the |HCode I| constructors. Some of the patterns are marked with a
|.| which you can read as `no choice but'. When splitting gives us the case that the
code was |PUSH {i} n|, the initial stack height must be |i| and the final stack height
must be |suc i|, because nothing else fits the types we have given: fortunately,
|n :> s| is a vector one longer than |s|. Similarly, in the |ADD| case, the initial
height must be at least two, so when we match on the stack, the underflow cases do not
fit the known information and are rejected by Agda as impossible.

When we split a scrutinee, for each constructor case Agda learns that
the indices of the scrutinee's type must equal those of the
constructor's return type, and she tries to solve the equations:
sometimes she learns that the case cannot happen; sometimes she learns
useful information about the indices. Crucially, as soon as we have
types which are related to each other by indexing, inspecting data
(e.g., the |HCodeI| code) no longer happens in isolation. Instead, we
can learn useful information about other data (e.g., the stack).

To finish the job, we need to fix up |compile|. Here, we must be sure
that the code we generate can run starting from any height of stack.
Further, we can promise that the stack will only grow by one: that promise
used to be \emph{waffle}, but now it is in the type and checked! Happily,
our old |compile| function really did keep the promise, so it typechecks
without further ado.
%format compileI = compile
\begin{code}
compileI : HExp -> {i : Nat} -> HCodeI i (suc i)
compileI (val n)      = PUSH n
compileI (e1 +++ e2)  = compileI e1 -SEQ- compileI e2 -SEQ- ADD
\end{code}

We have used types to eliminate underflow and to keep the promise that
compiled expressions grow the stack by one value. However, we might like to
know that the compiler really works. It is not enough just to push some value:
we need to know that we get the value we expect---the value given by |eval|.
Our |==| type allows us to express that very property, and we may then write
a \emph{program} which computes the evidence for that property.
%format correct = "\F{correct}"
\begin{code}
correct :  (e : HExp){i : Nat}(s : Vec Nat i) ->
           execI (compileI e) s == eval e :> s
correct (val n)      s  = refl
correct (e1 +++ e2)  s
  rewrite  correct e1 s
        |  correct e2 (eval e1 :> s)
  = refl
\end{code}

It is a little difficult to do the process justice on paper. When the expression
is |val n|, we discover that our return type is
\[
 |execI (compileI (val n)) s == eval (val n) :> s|
\]
but, just by the computation rules we wrote in our programs,
\[
 |execI (compileI (val n)) s = execI (PUSH n) s = n :> s|
\]
and
\[
 |eval (val n) :> s = n :> s|
\]
so both sides of the equation are already equal, and the |refl| constructor typechecks!

We have a harder time of it with addition. After computation, the goal is
\[
 |execI ADD (execI (compileI e2) (execI (compileI e1) s)) == (eval e1 + eval e2) :> s|
\]
and we can get no further. However, we could make a recursive call on a subexpression,
\[
 |correct e1 s : execI (compileI e1) s == eval e1 :> s|
\]
If you have learned \emph{proof by induction}, you may have encountered the notion of
`inductive hypothesis'. For us that is exactly `the type of a permitted recursive call'.
The special |rewrite| syntax works specifically with the |==| type, allowing us to rewrite
the goal by any equation we can prove. After the first step, we get
\begin{spec}
correct :  (e : HExp){i : Nat}(s : Vec Nat i) ->
           execI (compileI e) s == eval e :> s
correct (val n)      s  = refl
correct (e1 +++ e2)  s
  rewrite  correct e1 s
  = (HOLE 0)
\end{spec}
where we have made some definite progress.
\[
 |(HOLE 0) : execI ADD (execI (compileI e2) (eval e1 :> s)) == (eval e1 + eval e2) :> s|
\]
Agda allows us a further rewrite by glueing on another proof with the $\mid$ symbol. This time,
we can use the inductive hypothesis for the other subexpression, giving the stack that the
goal presents us,
\[
 |correct e2 (eval e1 :> s) : execI (compileI e2) (eval e1 :> s) == eval e2 :> eval e1 :> s|
\]
so that the goal becomes
\[
 |execI ADD (eval e2 :> eval e1 :> s) == (eval e1 + eval e2) :> s|
\]
Now, the left-hand side computes to the right-hand side, so |refl| brings us home.

You can compute
\[
 |execI (compileI (val 2 +++ val 2))|
\]
and be glad of the answer |4|, but be aware that you now work in a world where you can show
that your program is \emph{always} correct, for all possible inputs.
