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
Now,xs the left-hand side computes to the right-hand side, so |refl| brings us home.

You can compute
\[
 |execI (compileI (val 2 +++ val 2))|
\]
and be glad of the answer |4|, but be aware that you now work in a world where you can show
that your program is \emph{always} correct, for all possible inputs.


\section{Hutton's Razor with Variables}

%format HExpV = "\F{HExp}"
%format var = "\C{var}"

So far, we have considered \emph{closed} expressions built from
operators and constants. When we implement functions, we often work
with \emph{open} expressions which also contain \emph{variables},
e.g., the formal parameters of the functions. We can extend our little
syntax to allow for this possibility.

\begin{code}
data HExpV (V : Set) : Set where
  var    : V -> HExpV V
  val    : Nat -> HExpV V
  _+++_  : HExpV V -> HExpV V -> HExpV V
\end{code}

Our type has acquired a parameter |V|, being the set of variables which
may occur in expressions, and an extra constructor, |var| which makes
every variable an expression. I encourage you to think of |V| not as the
set of syntactically valid identifiers, but rather as the set of variables
\emph{in scope}. Correspondingly, we should be able to evaluate expressions
if we give a value for each of the variables which may occur in them. An
assignment of values to variables is called an \textbf{environment}, and
here we may represent such a thing simply as a function of type |V -> Val|.

%format evalV = "\F{eval}"
%format gam = "\V{\gamma}"
\begin{code}
evalV : {V : Set} -> HExpV V -> (V -> Val) -> Val
evalV (var x)      gam  = gam x
evalV (val n)      gam  = n
evalV (e1 +++ e2)  gam  = evalV e1 gam + evalV e2 gam
\end{code}

For example, we might have two variables, represented by the elements of |Two|.
%format myHExp = "\F{myHExp}"
\begin{code}
myHExp : HExpV Two
myHExp = ((val 1 +++ var tt) +++ (var tt +++ var ff))
\end{code}
\[
 |(evalV myHExp \ { tt -> 7 ; ff -> 11 }) == 26|
\]
\textbf{Notation.~} In Agda, the scope of a |\| extends as far as possible to the
right, so there is a common tendency not to parenthesize |\|-abstractions when
they are the last argument to a function. Meanwhile, the braces-and-semicolons
notation allows you to do a little bit of local case-splitting inside a
|\|-abstraction, used here to give a different value to each variable.

We can recover plain Hutton's Razor by making variables impossible: all expressions
in |HExpV Zero| are \emph{closed}. Indeed one motivation for bothering with |Zero|
is to give a uniform treatment to open and closed expressions, but recover closed
expressions specifically whenever we need them. If we have no variables, we can
evaluate without an environment as before, or rather, it is easy to come up with an
environment which assigns values to all none of the variables.
%format eval0 = "\F{eval0}"
\begin{code}
eval0 : HExpV Zero -> Nat
eval0 e = evalV e magic
\end{code}


\section{Simultaneous Substitution for Open Expressions}

Environments map variables to values, but that is not all we can do with variables
in expressions. In particular, we may systematically replace variables by expressions,
performing \emph{substitution}.
%format subst = "\F{subst}"
%format sg = "\V{\sigma}"
\begin{code}
subst : {U V : Set} -> HExpV U -> (U -> HExpV V) -> HExpV V
subst (var x)      sg  = sg x
subst (val n)      sg  = val n
subst (e1 +++ e2)  sg  = subst e1 sg +++ subst e2 sg
\end{code}
The function |sg : U -> HExpV V| maps each variable in |U| to some expression whose
variables are drawn from |V|. We can roll out this substitution to all the variables
in a |HExpV U| to get a |HExpV V|: because we act on all the variables, not just one
of them, we call this operation \emph{simultaneous} substitution.

Substitution is a lot like evaluation, but where |evalV| extends our
original evaluation algebra with an environment, |subst| extends the
original free algebra with the substitution. We can prove a useful fact relating
the two.
%format evalSubstFact = "\F{evalSubstFact}"
\begin{code}
evalSubstFact :  {U V : Set}(e : HExpV U)(sg : U -> HExpV V)(gam : V -> Val) ->
                 (evalV (subst e sg) gam) == (evalV e \ u -> evalV (sg u) gam)
evalSubstFact (var x) sg gam = refl
evalSubstFact (val n) sg gam = refl
evalSubstFact (e1 +++ e2) sg gam
  rewrite evalSubstFact e1 sg gam | evalSubstFact e2 sg gam
  = refl
\end{code}
If you substitute then evaluate, you get the same answer as if you build an
environment from the substitution. The proof is an easy induction on expressions,
rewriting the goal for |e1 +++ e2| by both inductive hypotheses. Why is this
fact useful? It tells us that the typical way we evaluate function calls is
sensible: when we give the \emph{actual} parameters to a function, they are
expressions, and what we do in theory is substitute those \emph{expressions} for the
formal parameters and evaluate, but what we really do is evaluate the actual
parameters to construct an environment which assigns \emph{values} to the formal
parameters.

A special case of this useful fact is that, if we had to, we could make do with
evaluation for \emph{closed} terms only by turning the environment into a
substitution, replacing each variable by a numerical constant.
%format eval0Fact = "\F{eval0Fact}"
\begin{code}
eval0Fact :  {V : Set}(e : HExpV V)(gam : V -> Val) ->
             eval0 (subst e (val o gam)) == evalV e gam
eval0Fact e gam = evalSubstFact e (val o gam) magic
\end{code}


\subsection{Identity and Composition for Substitution}

Recall the type of |subst|.
\[
 |subst : {U V : Set} -> HExpV U -> (U -> HExpV V) -> HExpV V|
\]
Now, taking |U = V|, the constructor |var : V -> HExpV V| could be used as the
substitution, which would give us
\[
 |subst (var x) var  = var x|
\]
It looks like there is a `do nothing' option! Let's prove it, trying the standard
`proof plan' of induction on expressions, rewriting by the inductive hypotheses.
%format idSubstFact = "\F{idSubstFact}"
\begin{code}
idSubstFact : {V : Set}(e : HExpV V) -> subst e var == e
idSubstFact (var x)  = refl
idSubstFact (val n)  = refl
idSubstFact (e1 +++ e2)
  rewrite idSubstFact e1 | idSubstFact e2
  = refl
\end{code}
We call |var| the \textbf{identity substitution} because it maps expressions to
themselves, just like the identity function.

%format sg1 = "\V{\sigma_1}"
%format sg2 = "\V{\sigma_2}"
Meanwhile, suppose we have substitutions
\[
 |sg1 : U -> HExpV V| \qquad |sg2 : V -> HExpV W|
\]
We can deploy them, one then the other, on some |e : HExpV U| to get
\[
 |subst (subst e sg1) sg2 : HExpV W|
\]
%format -after- = "\F{-after-}"
%format _-after-_ = _ -after- _
but is there a \emph{single} substitution which would do the same job in one pass?
Of course there is. We can \emph{compose} substitutions: it is conventional to make
composition work right-to-left, so I call the operator |-after-| as a reminder.
\begin{code}
_-after-_ : {U V W : Set} -> (V -> HExpV W) -> (U -> HExpV V) -> U -> HExpV W
(sg2 -after- sg1) u = subst (sg1 u) sg2
\end{code}
We had better check that it works as claimed. Again, the standard proof pattern works.
%format compSubstFact = "\F{compSubstFact}"
\begin{code}
compSubstFact :  {U V W : Set}(sg2 : V -> HExpV W)(sg1 : U -> HExpV V)(e : HExpV U) ->
                 subst e (sg2 -after- sg1) == subst (subst e sg1) sg2
compSubstFact sg2 sg1 (var x)      = refl
compSubstFact sg2 sg1 (val x)      = refl
compSubstFact sg2 sg1 (e1 +++ e2)
  rewrite compSubstFact sg2 sg1 e1 | compSubstFact sg2 sg1 e2
  = refl
\end{code}

%format tsbus = "\F{tsbus}"
So, |var| and |-after-| are related to |subst| in much the way that |id| and |o| relate
to ordinary function application. We can tease that out a little more clearly if we consider
the `agree on all inputs' relation for functions.\nudge{Many of us would
prefer if this relation were just given by |==|, but that is sadly not so in today's
Agda.}
%format =^= = "\F{\doteq}"
%format _=^=_ = _ =^= _
\begin{code}
_=^=_ : {S T : Set}(f g : S -> T) -> Set
f =^= g = (s : _) -> f s == g s
infixl 2 _=^=_
\end{code}

\textbf{Conor~} explain the |_| notation!

Ordinary function composition, |o|, absorbs |id| and is associative.
%format funAbsorbLeft = "\F{funAbsorbLeft}"
%format funAbsorbRight = "\F{funAbsorbRight}"
%format funAssociative = "\F{funAssociative}"
\begin{code}
funAbsorbLeft   :  {S T : Set}(g : S -> T) ->
                   id o g =^= g
funAbsorbLeft g s = refl

funAbsorbRight  :  {S T : Set}(f : S -> T) ->
                   f o id =^= f
funAbsorbRight f s = refl

funAssociative  :  {R S T U : Set }(f : T -> U)(g : S -> T)(h : R -> S) ->
                   (f o g) o h =^= f o (g o h)
funAssociative f g h r = refl
\end{code}

With a little more work, the corresponding thing is true for substitutions.
%format Subst = "\F{Subst}"
%format substAbsorbLeft = "\F{substAbsorbLeft}"
%format substAbsorbRight = "\F{substAbsorbRight}"
%format substAssociative = "\F{substAssociative}"
\begin{code}
Subst : Set -> Set -> Set
Subst S T = S -> HExpV T

substAbsorbLeft   :  {S T : Set}(g : Subst S T) ->
                     var -after- g =^= g
substAbsorbLeft g s = idSubstFact (g s)

substAbsorbRight  :  {S T : Set}(f : Subst S T) ->
                     f -after- var =^= f
substAbsorbRight f s = refl

substAssociative  :  {R S T U : Set }(f : Subst T U)(g : Subst S T)(h : Subst R S) ->
                     (f -after- g) -after- h =^= f -after- (g -after- h)
substAssociative f g h r = compSubstFact f g (h r)
\end{code}

Moreover, if we flip |subst| around,\nudge{Programmers use |subst|;
mathematicians use |tsbus|. I'm both.} we can see it as a map from substitutions to ordinary functions.
\begin{code}
tsbus : {U V : Set} -> (U -> HExpV V) -> (HExpV U -> HExpV V)
tsbus sg e = subst e sg
\end{code}
What our earlier proofs really tell us is that |tsbus| fits the identity and composition structure
of substitutions into that of functions.
\[\begin{array}{lcl}
|idSubstFact|        & |:| &  |{S : Set} ->| \\
                     &     &  |tsbus {S}{S} var =^= id| \smallskip \\
|compSubstFact|      & |:| &  |{R S T : Set}(f : Subst S T)(g : Subst R S) ->| \\
                     &     &  |tsbus (f -after- g) =^= tsbus f o tsbus g|
\end{array}\]
