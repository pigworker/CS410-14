\chapter{A Basic Prelude}

Let us build some basic types and equipment for general use. We might need to
rethink some of this stuff later, but it's better to keep things simple until
life forces complexity upon us. In the course of establishing this setup, we'll
surely encounter language features in need of explanation.

Concretely, we shall implement

%format BasicPrelude = "\M{BasicPrelude}"
\begin{code}
module BasicPrelude where
\end{code}

the source code for this chapter of the notes is indeed that very module.
We'll be able to import this module into others that we define later.
The first exercise will put it to good use.


\section{Natural Numbers}

We have already had a quick preview of the datatype of natural numbers.
Let us have it in our prelude.

%format Set = "\D{Set}"
%format Nat = "\D{Nat}"
%format zero = "\C{zero}"
%format suc = "\C{suc}"
\begin{code}
data Nat : Set where
  zero  : Nat
  suc   : Nat -> Nat

{-# BUILTIN NATURAL  Nat   #-}
{-# BUILTIN ZERO     zero  #-}
{-# BUILTIN SUC      suc   #-}
\end{code}

The funny comment-like BUILTIN things are not comments, but
\emph{pragmas}---not quite official parts of the language. Agda's
implementers expected that we might need to define numbers, so these
pragmas just tell Agda what we've chosen to call the bits and
pieces. The payoff is that we are now allowed write numbers in
\emph{decimal}, leaving Agda to do all that |suc|cing.

If we define addition,
%format + = "\F{+}"
%format _+_ = "\us{" + "}"
\begin{code}
_+_ : Nat -> Nat -> Nat
zero   + n  = n
suc m  + n  = suc (m + n)

infixr 5 _+_
\end{code}
then we can try evaluating expressions (using [C-c C-n]) such as
\begin{spec}
1 + 2 + 3 + 4
\end{spec}
Note that the |infixr 5| declaration assigns a precedence level of 5 to |+|
(with higher binding more tightly) and ensures that multiple additions group
to the right. The above means
\begin{spec}
1 + (2 + (3 + 4))
\end{spec}


\section{Impossible, Trivial, and Different}

In this section, we build three finite types, capturing important basic
concepts.

%format Zero = "\D{Zero}"
%format magic = "\F{magic}"
\subsection{|Zero|}
The |Zero| type has nothing after its |where| but silence. There is no way
to make a \emph{value} of type |Zero|. In Haskell, you could just write an
infinite recursion or take the head of an empty list, but Agda won't
countenance such dodges.
\begin{code}
data Zero : Set where
\end{code}

The |Zero| type represents the idea of \emph{impossibility}, which is a very useful
idea, because if it's impossible to get into a situation, you don't need to worry
about how to get out of it. The following definition bottles that intuition.
\begin{code}
magic :  {X : Set} ->
         Zero -> X
magic ()
\end{code}
There's plenty to explain here. The |{X : Set} ->| means
`for all |Set|s, |X|'. So, the whole type says `for all |Set|s |X|, there is a
function from |Zero| to |X|'. To define a function, we must explain which
value of the output type to return for each value of the input type. But that
ought to be very easy, because there are no values of the input type! It's
a bit like saying `if you believe \emph{that}, you'll believe anything'.

The braces have a secondary meaning: they tell Agda that we don't want
to write |X| explicitly when we use |magic|. Rather, we want Agda to
infer which |X| is relevant from the context in which |magic| is being
used, just the same way that Haskell silently infers the types at
which polymorphic functions are used. So, the first visible argument
of |magic| has type |Zero|. If we're refining a
goal by |magic ?|, then it's clear that |X| should be the goal type, and
then we are left finding something of type |Zero| to fill in for the |?|.

But how do way say what |magic| does? We don't. Instead, we say that
it doesn't.  The definition of |magic| is not given by an equation,
but rather by \emph{refutation}. In Agda, if we can point out that an
input to a function is impossible, we do not have to write an |=| sign
and an output. The way we point it out is to write the
\emph{absurd pattern} |()| in the place of the impossible thing. We're
effectively saying `BUSTED!'.

Note, by the way, that Agda's notation thus makes |()| mean the
opposite of what it means in Haskell, where it's the empty tuple,
easily constructed but not very informative. That's also a useful
thing to have around.

%format One = "\D{One}"
%format <> = "\C{\left<\right>}"
\subsection{|One|}

\textbf{tl;dr} There is a type called |One|. It has one element, written |<>|.

I could define a |data|type with one constructor. Instead, let me show
you another feature of Agda---|record|s. Where a |data|type is given
by a \emph{choice} of constructors, a |record| type is given by a
\emph{collection} of fields. To build a record value, one must supply
a value for each field. I define |One| to be the record type with
\emph{no fields}, so it is very easy to give a value for each field: there's
only one way to do it.
\begin{code}
record One : Set where
\end{code}

Values of |record| types are officially written
|record {field1 = value1;...;fieldn = valuen}|, so the only value in |One| is
\begin{spec}
  record {}
\end{spec}
which is a bit of a mouthful for something so trivial. Fortunately, Agda lets
us give a neater notation. We may optionally equip a record type with a
\emph{constructor}---the function which makes a record, taking the values of the
fields as arguments. As part of the record declaration, I write
\begin{code}
  constructor <>
\end{code}
which means, because there are no arguments, that
\begin{spec}
<> : One
\end{spec}
We are allowed to use either the official |record| notation or the constructor
shorthand when we write patterns. Note that pattern matching an element of |One|
does not tell us anything we didn't already know. Think:

\begin{tabular}{cccc}
|Zero| & impossible to make & useful to possess & not representable with bits \\
|One|  & trivial to make & useless to possess & representable with no bits \\
\end{tabular}

On reflection, it is perhaps perverse to introduce record types with such a
degenerate example. We'll have some proper records with fields in, shortly.

But first, let us complete our trinity of finite types by getting our hands
on a bit, at last.

%format Two = "\D{Two}"
%format tt = "\C{t\!t}"
%format ff = "\C{f\!f}"
\section{|Two|}

The type |Two| represents a choice between exactly two things. As it is a
choice, let's define it as a |data|type. As the two constructors have the
same type, I can save space and declare them on the same line.
\begin{code}
data Two : Set where
  tt ff : Two
\end{code}
In Haskell, this type is called Bool and has values True and False. I call
the type |Two| to remind you how big it is, and I use ancient abbreviations
for the constructors.

Agda's cunning mixfix syntax lets you rebuild familiar notations.
%format if = "\F{if}"
%format then = "\F{then}"
%format else = "\F{else}"
%format if_then_else_ = if _ then _ else _
\begin{code}
if_then_else_ : {X : Set} -> Two -> X -> X -> X
if tt then t else f = t
if ff then t else f = f
\end{code}
Again, we expect Agda to figure out the type of the conditional expression
from the context, so we use braces to indicate that it should be hidden.

(Here are some dangling questions. Is it good that the types of the
two branches are just the same as the type of the overall expression?
Do we not know more, once we have checked the condition? How could we
know that we know more?)

We can use conditionals to define conjunction of two Booleans:

\begin{code}
_/\_ : Two -> Two -> Two
b1 /\ b2 = if b1 then b2 else ff
\end{code}
%
Now that we have a way to represent Boolean values and conditional expressions,
we might like to have some conditions. E.g., let us be able to compare numbers.
%format <= = "\F{\le}"
%format _<=_ = "\us{" <= "}"
\begin{code}
_<=_ : Nat -> Nat -> Two
zero   <= y      = tt
suc x  <= zero   = ff
suc x  <= suc y  = x <= y
\end{code}

%format List = "\D{List}"
%format :> = "\C{:\!>}"
%format _:>_ = "\us{" :> "}"
\section{|List|s}

We can declare a |data|type which does the job of Haskell's workhorse
|[a]|. The definition of |List| is parametrized by some |X|, the set
in to which the list's elements belong. I write the parameters for the
datatype to the left of the |:| in the declaration.
\nudge{A typesetting gremlin prevents me from colouring |[]| red.}
\begin{code}
data List (X : Set) : Set where
  []    : List X
  _:>_  : X -> List X -> List X

infixr 5 _:>_
\end{code}
I give a `nil' constructor, |[]|, and a right associative infix `cons' constructor,
|:>|, which is arrowhead-shaped to remind you that you access list elements
from left to right. We can write lists like
\begin{spec}
1 :> 2 :> 3 :> 4 :> 5 :> []
\end{spec}
but Agda does not supply any fancy syntax like Haskell's |[1,2,3,4,5]|.

How many values are there in the set |List Zero|?

Does the set |List One| remind you of any other set that you know?

\begin{code}
infixr 5 _++_

_++_ : {A : Set} -> List A -> List A -> List A
[]         ++ ys = ys
(x :> xs)  ++ ys = x :> (xs ++ ys)
\end{code}


\section{Interlude: Insertion}

%format insertionSort = "\F{insertionSort}"
%format insertList = "\F{insertList}"

We've got quite a bit of kit now. Let's take a break from grinding out
library components and write a program or two. In particular, as we have
numbers and lists and comparison, we could write insertion sort. Let's
see if we can remember how it goes. Split into cases, and the empty case
is clear.
\begin{spec}
insertionSort : List Nat -> List Nat
insertionSort []         = []
insertionSort (x :> xs)  = ?
\end{spec}
What happens next? If we can insert |x| into the right place after sorting
|xs|, we'll be home. Agda is a declare-before-use language, but a declaration
does not have to be right next to the corresponding definition. We can make
progress like this.
\begin{code}
insertionSort : List Nat -> List Nat

insertList : Nat -> List Nat -> List Nat

insertionSort []         = []
insertionSort (x :> xs)  = insertList x (insertionSort xs)
\end{code}
\begin{spec}
insertList y xs = ?
\end{spec}
Now, how do we insert? Again, we need to split the list into its cases.
the |[]| case is easy. (It's also easy to get wrong.)
\begin{spec}
insertList y []         = y :> []
insertList y (x :> xs)  = ?
\end{spec}
To proceed in the `cons` case, we need to know whether or not |y| should
come before |x|. We could go with
\[
  |if y <= x then ? else ?|
\]
but let me take the chance to show you another feature. Instead of moving
to the right and giving an expression, Agda lets us bring the extra information
we need to the \emph{left}, where we can pattern match on it.
\begin{spec}
insertList y []         = y :> []
insertList y (x :> xs)  with  y <= x
insertList y (x :> xs)  |     b       = ?
\end{spec}
The |with| construct adds an extra column to the left-hand side, tabulating
cases for the result of the given expression. Now, if we split on |b|, we get
\begin{spec}
insertList y []         = y :> []
insertList y (x :> xs)  with  y <= x
insertList y (x :> xs)  |     tt      = ?
insertList y (x :> xs)  |     ff      = ?
\end{spec}
and for each line of this extended table, it is clear what the output must be.
\begin{code}
insertList y []         = y :> []
insertList y (x :> xs)  with  y <= x
insertList y (x :> xs)  |     tt      = y :> x :> xs
insertList y (x :> xs)  |     ff      = x :> insertList y xs
\end{code}
If the patterns to the left of the bar stay just the same as on the |with|-line,
we're allowed to abbreviate them, as folllows.
\begin{spec}
insertList y []         = y :> []
insertList y (x :> xs)  with  y <= x
...                     |     tt      = y :> x :> xs
...                     |     ff      = x :> insertList y xs
\end{spec}
Which of these strikes you as a better document is a matter of taste.

\subsection{Programs as Decision Trees}

It's good to think of a function definition as the description of a
\emph{decision tree}. We start by considering a bunch of inputs and we need
a strategy
to deliver an output. We can
\begin{itemize}
\item give an output built from the stuff we've got, with the |= output| strategy;
\item split one of our things into constructor cases, in each case considering
  the structures inside (and if there are no cases, we document that with an
  absurd pattern);
\item get more stuff to consider by asking the value of some |extra| expressed
  in terms
  of the stuff we already have---that's what the right-hand side, |with extra|,
  achieves.
\end{itemize}

You can read a program as a dialogue between the machine, saying `what
am I supposed to do with this stuff?' on the left, and the programmer,
explaining how to proceed on the right by one of the above strategies.
The case-splitting nodes aren't documented by an explicit
right-hand-side in the final program, but you see them in passing
while you work, and you can see that they result in multiple left-hand
sides for distinguished cases. Agda figures out how to compute your
functions by reconstructing the full decision tree from the
constructors in your patterns.


\section{Unit Testing with Dependent Types}

%format == = "\D{==}"
%format _==_ = "\us{" == "}"
%format refl = "\C{refl}"

I'm only in chapter two and I can't resist the temptation. I want to be able
to write unit tests in my code---example expressions which should have the
values given, e.g.
\[
  |insertionSort (5 :> 2 :> 4 :> 3 :> 1 :> []) == (1 :> 2 :> 3 :> 4 :> 5 :> [])|
\]

The good news is that Agda can run old programs \emph{during} typechecking of
new programs. We can make the typechecker run our unit tests for us, making use
of the following\nudge{Yes, it is scary.} piece of kit.

\begin{spec}
infix 4 _==_

data _==_ {X : Set}(x : X) : X -> Set where
  refl : x == x
\end{spec}

%if False
\begin{code}
postulate
      Level : Set
      lzero  : Level
      lsuc   : Level -> Level
      lmax   : Level -> Level -> Level

{-# BUILTIN LEVEL     Level #-}
{-# BUILTIN LEVELZERO lzero  #-}
{-# BUILTIN LEVELSUC  lsuc   #-}
{-# BUILTIN LEVELMAX  lmax   #-}

data _==_ {l}{X : Set l}(x : X) : X -> Set l where
  refl : x == x
infix 4 _==_
{-# BUILTIN EQUALITY _==_ #-}
{-# BUILTIN REFL refl #-}
\end{code}
%endif

This |data|type has two parameters: the |X| in braces is a |Set|, and the
braces, as ever, mean that it should be hidden; the |x| is an element of |X|,
and its \emph{round} brackets mean that it should be \emph{visible}, in this
case as the thing to the left of the |==| sign. However, right of the |:|,
we have |X -> Set|, not just |Set|, because this is an \emph{indexed} collection
of sets. For each |y : X|, we get a set |x == y| whose elements represent
\emph{evidence} that |x| and |y| are equal. The constructor tells us the only
way to generate the evidence. The return type of a constructor may choose any
value for the index, and it delivers values only for that index. Here, by
choosing |x| for the index in the type of |refl|, we ensure that for equality
evidence to exist, the two sides of the equation must have the very same value.

The upshot of all this is that we can write a unit test like this:
%format iTest = "\F{iTest}"
\begin{code}
iTest : insertionSort (5 :> 2 :> 4 :> 3 :> 1 :> []) == (1 :> 2 :> 3 :> 4 :> 5 :> [])
iTest = refl
\end{code}
The typechecker must make sure it is valid to use the |refl| constructor,
so it evaluates both sides of the equation to ensure that they are the same.

Try messing up the program to see what happens!

Even better, try deleting the program and rebuilding it interactively. While
your program is under construction and the test might possibly work out fine in
the end, the |refl| evidence in the unit test will have a yellow background,
indicating that it is \yellowBG{suspicious}\nudge{sus-pish-ous}. But you will not
be allowed to do anything interactively which makes the test actually fail, and if
you override the interactive system and load a silly program, the refl will
have the brown background of \brownBG{steaming unpleasantness}.

We won't be fooling around with fancy types in programming for a while yet,
but unit testing is a good engineering practice, so let us take advantage
of Agda's capacity to support it.


\section{More Prelude: Sums and Products}

%format /+/ = "\D{/\!\!+\!\!/}"
%format _/+/_ = "\us{" /+/ "}"
%format inl = "\C{inl}"
%format inr = "\C{inr}"
We often build datatypes which offer some sort of choice. Sometimes we just
want to give a choice between two types which are already established. The
type which offers `an |S| or a |T|' is called the \emph{sum} of |S| and
|T|.\nudge{Haskell calls this construction |Either|.} We define it as a datatype
with |S| and |T| as parameters, allowing
constructors, for `left injection' and `right injection', respectively.
\begin{code}
infixr 1 _/+/_

data _/+/_ (S T : Set) : Set where
  inl  : S  -> S /+/ T
  inr  : T  -> S /+/ T
\end{code}

To see why it really is a kind of sum, try finding all the \emph{values} in each of
\[
  |Zero /+/ Zero|\quad |Zero /+/ One|\quad |One /+/ One|\quad
  |One /+/ Two|\quad |Two /+/ Two|
\]

When we offer a choice, we need to able to cope with either possibility.
The following gadget captures the idea of `computing by cases'.

%format <?> = "\F{\left<?\right>}"
%format _<?>_ = "\us{" <?> "}"
\begin{code}
_<?>_ :   {S T X : Set} ->
          (S -> X) -> (T -> X) ->
          S /+/ T -> X
(f <?> g) (inl s) = f s
(f <?> g) (inr t) = g t
\end{code}
It might look a bit weird that it's an \emph{infix} operator with \emph{three}
arguments, but it's used in a higher-order way. To make a function,
|f <?> g| which takes |S /+/ T| to some |X|, you need to have a function for each
case, so |f| in |S -> X| and |g| in |T -> X|.

%format /*/ = "\D{/\!\!\times\!\!/}"
%format _/*/_ = "\us{" /*/ "}"
%format , = "\C{,}"
%format outl = "\F{outl}"
%format outr = "\F{outr}"
Meanwhile, another recurrent theme in type design is that we ask for a \emph{pair}
of things, drawn from existing types.\nudge{Haskell uses the notation |(s,t)| for
both the types and values.} This is, somehow, the classic example of a |record|.
\begin{code}
infixr 2 _/*/_

record _/*/_ (S T : Set) : Set where
  constructor _,_
  field
    outl  : S
    outr  : T
open _/*/_ public
infixr 4 _,_
\end{code}
I have a little explaining to do, here. The |field| keyword introduces the
declarations of the record's fields, which must be indented below it.
We have two fields, so it makes sense to have an infix |constructor|, which is
just a comma---unlike Haskell, parentheses are needed only to resolve ambiguity.
The |open| declaration makes |outl| and |outr| available as the `left projection'
and `right projection' functions, respectively. You can check that
\[
|outl : {S T : Set} -> S /*/ T -> S| \qquad
|outr : {S T : Set} -> S /*/ T -> T|
\]
The |public| means that |outl| and |outr| stay in scope whenever any other module
imports this one.

To see why |S /*/ T| is called the \emph{product} of |S| and |T|, try finding
all the values in the following types.
\[
|Zero /*/ Zero|\quad |Zero /*/ One| \quad |One /*/ One|\quad
|One /*/ Two|\quad |Two /*/ Two|
\]

It is sometimes useful to be able to convert a function which takes a
pair into a function which takes its arguments one at a time. This
conversion is called `currying' after the logician, Haskell Curry,
even though Moses Scho\"nfinkel invented it slightly earlier.
%format curry = "\F{curry}"
\begin{code}
curry :  {S T X : Set} ->
         (S /*/ T -> X) ->
         S -> T -> X
curry f s t = f (s , t)
\end{code}
Its inverse is, arguably, even more useful, as it tells you how to build a
function from pairs by considering each component separately.
%format uncurry = "\F{uncurry}"
\begin{code}
uncurry :  {S T X : Set} ->
           (S -> T -> X) ->
           S /*/ T -> X
uncurry f (s , t) = f s t
\end{code}


\section{Interlude: Exponentiation}

How many functions are there in a type |S -> T|? It depends on when we consider
two functions to be the same. Mathematically, such a function is considered just
to be the choice of a |T| value corresponding to each |S| value. There might be
lots of different ways to \emph{implement} that function, but if two programs
of type |S -> T| agree on outputs whenever we feed them the same inputs, we say
they are two implementations of the same function.

So it's easy to count functions, at least if the sets involved are
finite. If there are |t| different elements of |T| and |s| different
elements of |S|, then we need to choose one of the |t| for each one of
the |s|, so that's $t^s$ different possibilities. Just as |S /+/ T| really
behaves like a sum and |S /*/ T| really behaves like a product, we
find that |S -> T| really behaves like the exponential $|T|^{|S|}$.

The fact that |curry| and |uncurry| are mutually inverse (or \emph{isomorphic})
just tells us something we learned in school
\[
  |X|^{(|S /*/ T|)} \cong (|X|^{|T|})^{|S|}
\]

You might also remember that
\[
  |X|^{(|S /+/ T|)} \cong |X|^{|S|} |/*/| |X|^{|T|}
\]
and it's not hard to see why that makes sense in terms of counting functions.
(Think about what |<?>| does.)

Many of the algebraic laws you learned for numeric operations at school
make perfect sense for \emph{type} operations and account for structures
fundamental to computation. That's (to some extent) how the Mathematically
Structured Programming Group came by its name. Keep your eyes peeled for more!


\section{More Prelude: Basic Functional Plumbing}

%format id = "\F{id}"
%format o = "\F{\circ}"
%format _o_ = "\us{" o "}"

Functions are a bit like machines with an input pipe and an output pipe. Their
types tell us whether it's safe to plumb them together. Any functional plumber
needs some basic tools.

Firstly, here's a bit of pipe with no machine in the middle---the \emph{identity}
function. What comes out is what went in!
\begin{code}
id : {X : Set} -> X -> X
id x = x
\end{code}

Secondly, we need to be able to plumb the output from one machine to the input
of another. Here's function \emph{composition}.
\begin{code}
_o_ : {A B C : Set} -> (B -> C) -> (A -> B) -> (A -> C)
(f o g) a = f (g a)

infixr 2 _o_
\end{code}

What laws do you think |id| and |o| should obey? If you plumb an extra bit of pipe
onto a machine, does it change what the machine does? If you plumb a sequence of
machines together, the order of the machines can clearly matter, but does the
order in which you did the plumbing jobs affect the behaviour of the end product?

