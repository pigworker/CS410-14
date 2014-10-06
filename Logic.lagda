\chapter{Logic via Types}

The inescapable honesty of Agda makes it possible for us to
treat values as \emph{evidence} for something. We gain a
logical interpretation of types.

%format Logic = "\M{Logic}"
\begin{code}
module Logic where

open import BasicPrelude
\end{code}

One way of looking at logical formulae is to consider what constitutes
evidence that they hold. We can look at the connectives systematically.

What constitutes `evidence for A or B'? Either `evidence for A'
or `evidence for B'. If we have a type, |A|, representing `evidence for A'
and another, |B| representing `evidence for B', then |A /+/ B| represents
`evidence for A or B'.

What constitutes `evidence for A and B'? We need both `evidence for A'
and `evidence for B'. If we have a type, |A|, representing `evidence for A'
and another, |B| representing `evidence for B', then |A /*/ B| represents
`evidence for A and B'.

What constitutes `evidence that A implies B'? We need to be sure that,
given `evidence for A', we can produce `evidence for B'.  If we have a
type, |A|, representing `evidence for A' and another, |B| representing
`evidence for B', then |A -> B| represents `evidence for A and B'.

There will be more to say here, after exercise 1 is completed, but the basic
message is:
\begin{center}
propositions are types; types are propositions\\
proofs are programs; programs are proofs
\end{center}

Types like |Nat| are rather boring propositions. Types like |2 + 2 == 4| are
slightly more interesting.

