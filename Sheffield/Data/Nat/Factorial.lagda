\input{lagda-preamble}

\title{The factorial function}

\begin{document}

\maketitle

This file defines the factorial function in Agda and proves some
basic properties.  We start by declaring a module:

\begin{code}
module Sheffield.Data.Nat.Factorial where 
\end{code}

We next list some standard library modules whose results we need to
use.  Recall that after importing and opening a module we can use all
the definitions from that module without needing to give the module
name as a prefix.

\begin{code}
open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.Divisibility renaming (poset to ∣-poset)
open import Relation.Nullary.Core
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

open import Sheffield.Data.Nat.Divisibility

open ≡-Reasoning
open DecTotalOrder decTotalOrder hiding (_≤_ ; _≤?_ ) renaming (refl to ≤-refl ; trans to ≤-trans)
\end{code}

We now give the obvious recursive definition of the factorial
function.  Note that the official name of this function is \verb+_!+,
and that the placement of the underscore indicates that we can write
the argument on the left, giving the traditional notation \verb+n !+
for \verb+n+ factorial.

\begin{code}

_! : ℕ → ℕ

0 ! = 1
(suc n) ! = (suc n) * (n !)  

\end{code}

We now want to prove some divisibility statements.  The first of these
says that if $k\leq n$ then $k!$ divides $n!$.  Recall that there are
two different, but essentially equivalent, formulations of the order
relation on \verb+ℕ+, denoted by \verb+≤+ and \verb+≤′+ .  (The first
treats \verb+0 ≤ n+ as a special case, whereas the second treats
\verb+n ≤′ n+ as a special case instead.)  It is convenient to prove
the result using \verb+≤′+ first and then deduce the result for
\verb+≤+ using the conversion function \verb+≤⇒≤′+ defined in
\verb+Data.Nat+.

We start by defining a function called \verb+k!∣n!′+.  It takes two
implicit arguments called \verb+k+ and \verb+n+, and an explicit
argument which is a proof that \verb+k ≤′ n+.  It then returns a proof
that \verb+k !+ defines \verb+n !+.  These facts are represented by
the following declaration:
\begin{code}
k!∣n!′ : {k n : ℕ} → k ≤′ n → k ! ∣ n !
\end{code}

To see how the definition works, we need to understand the explicit
argument in more detail.  As with all propositions in Agda, the
proposition \verb+k ≤′ n+ is actually a type, and terms of that type
count as proofs of the proposition.  The type is defined inductively
by the following rules:
\begin{enumerate}
 \item For each natural number \verb+n+, there is a term
  \verb+≤′-refl+ of type \verb+n ≤′ n+.  Here \verb+n+ is an implicit
  argument to the function \verb+≤′-refl+ so Agda will deduce it from
  the context in which the function is used.
 \item For every term \verb+i≤′j+ of type \verb+i ≤′ j+, there is a term 
  \verb+(≤′-step i≤′j)+ of type \verb!i ≤′ (1 + j)!.  
 \item All terms of type \verb+n ≤′ m+ arise from one of the above two
  constructors. 
\end{enumerate}
We can thus define \verb+k!∣n!′+ by specifying its value on terms
constructed in the above two ways.

The value on a term \verb+≤′-refl+ of type \verb+n ≤′ n+ should be a
proof that \verb+n ∣ n+.  The module \verb+Data.Nat.Divisibility+
contains such a proof, as part of a package that describes \verb+ℕ+ as
a partially ordered set under the relation of divisibility.  The whole
package has the fully qualified name
\verb+Data.Nat.Divisibility.poset+, but we imported and opened the
module \verb+Data.Nat.Divisibility+ with renaming, so we can use the
shorter name \verb+∣-poset+ instead.  This is a record of type
\verb+Poset+ as defined in \verb+Relation.Binary+.  One of the fields
in this record is a function called \verb+refl+ that takes a natural
number \verb+n+ as an implicit argument and returns a term of type
\verb+n ∣ n+.  To refer to the \verb+refl+ field in the record
\verb+∣-poset+ (of type \verb+Poset+) we use the syntax 
\verb+Poset.refl ∣-poset+.  This leads to the following clause as the
first half of the definition of \verb+k!∣n!′+:
\begin{code}
k!∣n!′ ≤′-refl = (Poset.refl ∣-poset)
\end{code}

For the second half of the definition, we must cover the case where
the explicit argument has the form \verb+(≤′-step k≤′n)+ for some
natural numbers \verb+k+ and \verb+n+, so the implicit arguments are
\verb+k+ and \verb+suc n+.  It is convenient here to make the implicit
arguments explicit, which is permitted if we enclose them in curly
brackets.  We may assume by induction that \verb+(k!∣n!′ k≤′n)+ is
defined as a term of type \verb+k ! ∣ n !+.  The module
\verb+Extra.Data.Nat.Divisibility+ defines a function \verb+left-*+
which accepts an integer \verb+a+ and a proof that \verb+b ∣ c+ and
returns a proof that \verb+b ∣ a * c+.  We have 
\verb+(suc n) * (n !) = (n + 1) !+ by definition, so 
\verb+left-* (suc n) (k!∣n!′ k≤′n)+ is a proof that \verb+k !+ divides
\verb+(suc n) !+.  This validates the following clause, which
completes the definition of \verb+k!∣n!′+
\begin{code}
k!∣n!′ {k} {suc n} (≤′-step k≤′n) = left-* (suc n) (k!∣n!′ k≤′n)
\end{code}

The module \verb+Data.Nat+ defines a function \verb+≤⇒≤′+ that
converts terms of type \verb+i ≤ j+ to terms of type \verb+i ≤′ j+.
This provides a straightforward way to define \verb+k!∣n!+ in terms of
$k!∣n!′$:
\begin{code}
k!∣n! : {k n : ℕ} → k ≤ n → k ! ∣ n !
k!∣n! k≤n = k!∣n!′ (≤⇒≤′ k≤n) 
\end{code}

We now prove that if \verb+0 < k ≤ n+ then \verb+k+ divides 
\verb+n !+.  It is again convenient to prove a version using \verb+≤'+
first.  It is also convenient to prove the shifted statement that if
\verb+k < n+ then \verb+1 + k divides n !+, and deduce the unshifted
statement from this.  We have the following declaration for the
shifted version:
\begin{code}
k+1∣n!′ : {k n : ℕ} → k <′ n → suc k ∣ n !
\end{code}

The explicit argument is of type \verb+k <′ n+, which is by definition
the same as \verb+(suc k) ≤′ n+.  Our function is again defined by two
separate clauses for the two possible forms of this explicit
argument.  If it has the form \verb+≤′-refl+ then \verb+n+ is forced
to be the same as \verb+suc k+.  The function 
\verb+(Poset.refl ∣-poset)+ (with implicit argument \verb+k+) provides
a proof that \verb+suc k ∣ suc k+, and we can use the function 
\verb+right-*+ (from \verb+Extra.Data.Nat.Divisibility+) to convert
this to a proof that \verb+suc k+ divides \verb+n ! = (suc k) * (k !)+.
The required syntax is as follows:
\begin{code}
k+1∣n!′ {k} .{suc k} ≤′-refl = right-* (k !) (Poset.refl ∣-poset)
\end{code}
Note that the first two arguments on the left hand side are in curly
brackets, because they are implicit arguments that we have chosen to
make explicit.  Note also the dot attached to \verb+{suc k}+ which
indicates that the second argument is forced to be \verb+suc k+ in
order for the left hand side to be meaningful.  This is the only
circumstance in which one is allowed to repeat a variable name on the
left hand side of a definition.

We now cover the second case of \verb+k+1∣n!′+.  Here we have natural
numbers \verb+k+ and \verb+n+, and a proof (named \verb+k<′n+) that
\verb+k <′ n+, which is converted by \verb+≤′-step+ to a proof that
\verb+k <′ suc n+.  We may assume inductively that 
\verb+(k+1∣n!′ k<′n)+ is defined and gives a proof that \verb+suc k+
divides \verb+n !+.  We use the function \verb+left-*+
(from \verb+Extra.Data.Nat.Divisibility+) to convert this to a proof
that \verb+suc k+ divides \verb+(suc n) ! = (suc n) * (n !)+.
\begin{code}
k+1∣n!′ {k} {suc n} (≤′-step k<′n) = left-* (suc n) (k+1∣n!′ k<′n)
\end{code}

We again use the function \verb+≤⇒≤′+ from \verb+Data.Nat+ to
reformulate our statement in terms of \verb+≤+ rather than \verb+≤′+.
\begin{code}
k+1∣n! : {k n : ℕ} → k < n → suc k ∣ n !
k+1∣n! k<n = k+1∣n!′ (≤⇒≤′ k<n) 
\end{code}

It is also convenient to give a further reformulation in which we
unshift the first argument.  The declaration is as follows:
\begin{code}
k∣n! : {k n : ℕ} → 0 < k → k ≤ n → k ∣ n !
\end{code}

It is straightforward to define this function by pattern matching.
The first explicit argument is a proof that \verb+0 < j+, or
equivalently that \verb+suc 0 ≤ j+.  The propositions \verb+n ≤ m+ are
again defined (in \verb+Data.Nat+) by inductive rules:
\begin{enumerate}
 \item For any natural number \verb+n+, there is a term \verb+z≤n+
  (with \verb+n+ as an implicit argument) of type \verb+0 ≤ n+.
 \item For any term \verb+t+ of type \verb+n ≤ m+, there is a term
  \verb+s≤s t+ of type \verb+suc n ≤ suc m+. 
 \item All terms of type \verb+n ≤ m+ (for any \verb+n+ and \verb+m+)
  are obtained by iterated application of these constructors.
\end{enumerate}
The only possible pattern for a proof of \verb+suc 0 ≤ k+ is 
\verb+s≤s z≤n+, where the implicit argument to \verb+z≤n+ must be a
natural number \verb+j+ with \verb+suc j ≡ k+.  In this context the
second argument to \verb+k∣n!+ must be a proof that \verb+suc j ≤ n+,
or equivalently that \verb+j < n+.  We can thus feed this proof into
the function \verb|k+1∣n!| to see that \verb+k+ divides \verb+n !+.
The relevant syntax is as follows:
\begin{code}
k∣n! (s≤s z≤n) j<n = k+1∣n! j<n
\end{code}

We conclude with a proof that \verb+n ! ≥ 1+ for all \verb+n+. This is by induction on \verb+n+; the base case $n=0$ can be discharged easily since $0! = 1$. However, the induction step requires a lemma which we denote by \verb|m≤n+*m|. Thsi lemma states that, for any $m$ and $n$, multiplying by the successor of $n$ does not decrease $m$.

\begin{code}
n!≥1 : (n : ℕ) → ((n !) ≥ 1)
n!≥1 0 = s≤s z≤n
n!≥1 (suc m) = ≤-trans (n!≥1 m) (m≤n+*m (m !) m) where 
  m≤n+*m : (m n : ℕ) → (m ≤ (suc n) * m)
  m≤n+*m m n = m≤m+n m (n * m) 
\end{code}

\end{document}


