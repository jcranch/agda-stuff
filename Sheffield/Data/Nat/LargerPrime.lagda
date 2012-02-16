\input{lagda-preamble}

\title{Euclid's theorem in Agda}

\begin{document}

\maketitle

This document describes a proof in Agda that there are infinitely many
primes, or more precisely, that for any natural number $n$ there
exists a prime $p$ such that $p>n$.  We have explained the code in
great detail, as an introduction to Agda for mathematicians.

As Agda is based on intuitionistic logic, we can only prove the
existence of $p$ by constructing it, in some sense or other.  Our
approach is as follows:
\begin{itemize}
 \item[(a)] We prove that for any natural number $m>1$ there is a
  smallest natural number $p>1$ such that $p$ divides $m$, and that
  this $p$ is prime. 
 \item[(b)] Given an arbitrary natural number $n$ we show that the
  number $m=n!+1$ is larger than $1$, so we can apply~(a) to get a
  prime $p$ dividing $m$.
 \item[(c)] We then prove that this $p$ is larger than $n$.  In more
  detail, we suppose that $p\leq n$, and then note that $p$ divides
  both $n!$ and $n!+1$, so $p$ divides $1$, so $p=1$, which is a
  contradiction because $1$ is not prime.  This proves the double
  negation of the desired inequality $p>n$, which is enough even in
  Agda's constructive framework because the order relation on $ℕ$ is
  decidable. 
\end{itemize}

The proof relies on a number of modules in the Agda standard library,
and some new modules written for this project.  The basic definitions
of Peano arithmetic are set up in the Agda standard library
(specifically, in the module \verb+Data.Nat+ and its submodules).
Facts about divisibility and primes are proved in
\verb+Data.Nat.Divisibility+ and \verb+Data.Nat.Primality+.  The new
modules are as follows:

\begin{itemize}
 \item[(1)] The module \verb+Extra.Data.Nat.LargerPrime+ defined in this file
  assembles the ingredients mentioned below to prove the main result.
 \item[(2)] The module \verb+Extra.Data.Nat.LeastDivisor+ implements
  step~(a) in the above outline.  It relies on a more general
  framework for finding least elements defined in the module
  \verb+Extra.Data.Nat.Minimiser+. 
 \item[(3)] The module \verb+Extra.Data.Nat.Primality+ proves some basic
  facts about primes that are not covered by the standard
  library module \verb+Data.Nat.Primality+.
 \item[(4)] The module \verb+Extra.Data.Nat.Factorial+ defines the
  factorial function and proves some basic properties.
\end{itemize}

We start by declaring the module:
\begin{code}
module Sheffield.Data.Nat.LargerPrime where
\end{code}

Modules provide a framework for packaging together related
definitions.  In ordinary mathematical writing it is common to quote
results from different sources with incompatible notational
conventions; one then has to redefine some of the notation in the
sources to avoid ambiguity or clashes.  Agda modules provide
reasonably good support for maneuvers of this kind.  

We next list some standard library modules whose results we need to
use.  Note that we use the keyword \verb+open+ as well as
\verb+import+.  If we just say \verb+import Data.Nat.Primality+ then
we can use the definition \verb+Prime+ given in the module
\verb+Data.Nat.Primality+ but we need to refer to it as
\verb+Data.Nat.Primality.Prime+.  If we then say
\verb+open Data.Nat.Primality+ then we can use the short form
\verb+Prime+ rather than \verb+Data.Nat.Primality.Prime+.  The line
\verb+open import Data.Nat.Primality+ is equivalent to \verb+import+
followed by \verb+open+.  The code for the module
\verb+Data.Nat.Primality+ is in the file
\verb+src/Data/Nat/Primality.agda+ in the standard library.  The
location of the standard library depends on the details of your
installation.  If you already have Agda working under emacs then the
command \verb+C-h v agda2-include-dirs+ should tell you where to
look. 

\begin{code}
open import Data.Empty
open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.Divisibility
open import Data.Nat.Primality
open import Relation.Nullary.Core
open import Relation.Binary.PropositionalEquality
\end{code}

The module \verb+Data.Empty+ defines the empty set.  The next four
modules should be self-explanatory.  The module
\verb+Relation.Nullary.Core+ contains the negation operator and some 
auxiliary definitions for decidable relations that will be discussed
later.  The module \verb+Relation.Binary.PropositionalEquality+
contains some code that makes it easier to formalise proofs that use
chains of equalities, like
\begin{align*}
 a &= b \hspace{4em}  \text{ by Lemma 1 } \\
   &= c \hspace{4em}  \text{ by Lemma 2 } \\
   &= d \hspace{4em}  \text{ by Lemma 3. }
\end{align*}
It also contains many things that will not concern us for the moment.

Next, we will need to use the fact that addition of natural numbers is
commutative.  In order to keep the standard library tidy, this is not
represented as an isolated fact, but is packaged with various other
facts in a proof that $ℕ$ is a commutative semiring.  We therefore
need to import the definition of a semiring to gain access to the fact
that we need.  We use the following code:

\begin{code}
open import Algebra.Structures
open IsCommutativeSemiring isCommutativeSemiring using ( +-comm )
\end{code}

The effect is that the name \verb!+-comm! now refers to a proof that
$n+m=m+n$ for all $n,m\in ℕ$.  (Note that names in Agda can use almost
any character other than a space.  It is common for names to include
mathematical symbols or other punctuation.)

The details take some explanation, which could be skipped by the
impatient.  Firstly, \verb+IsCommutativeSemigroup+ (with a capital
\verb+I+) is a function of eight arguments that is defined in the
module \verb+Algebra.Structures+.  The first three arguments are given
in curly brackets in the function definition, which means that in most
circumstances these arguments need not be given explicitly because
they can be deduced from the remaining arguments.  The first two
arguments are levels, which are used by Agda to avoid Russell-type
paradoxes.  One can usually ignore these completely.  The third
(implicit) argument is a set $A$.  The remaining (explicit) arguments
are a relation on $A$ (written as $≈$), two binary operations on $A$
(written as addition and multiplication) and two elements $0,1\in A$.
The value of the function \verb+IsCommutativeSemigroup+ at these
arguments is, roughly speaking, the set of proofs that $≈$ is an
equivalence relation and that $A/≈$ is a commutative semiring under
the given operations.  Of course this set could be empty, if the
operations do not in fact make $A/≈$ into a commutative semiring.
(For reasons that we will not discuss here, algebraic structures are
always represented in Agda in this fashion, with operations defined on
a set $A$, and axioms that hold only modulo a specified equivalence
relation on $A$.)

Next, the natural numbers zero and one, and the operations of addition
and multiplication of natural numbers, are defined in \verb+Data.Nat+.
We also have the relation of equality on $ℕ$.  Feeding these
ingredients into the function \verb+IsCommutativeSemiring+ we get the
set $P$ of proofs that $ℕ$ is a commutative semiring.  The module
\verb+Data.Nat.Properties+ constructs such a proof, which is a
particular element called
\verb+Data.Nat.Properties.isCommutativeSemiring+ (with a lower case
\verb+i+) of the set $P$.  As we have imported and opened the module
\verb+Data.Nat.Properties+, we can omit the prefix and use the name
\verb+isCommutativeSemiring+.

We described \verb+IsCommutativeSemiring+ as a set-valued function,
which is essentially correct, but in more technical terms it is a
parametrised record type.  Agda automatically creates an associated
module for each parametrised record type.  The statement
\begin{verbatim}
open IsCommutativeSemiring isCommutativeSemiring using ( +-comm )
\end{verbatim}

is a variant of the operation of opening a module, which we have seen
before.  The proof \verb+isCommutativeSemigroup+ is a package of
proofs of all the different axioms for a commutative semiring, and
the effect of the above \verb+open+ statement is to enable us to refer
to the part of the package called \verb!+-comm!, which is a proof that
addition is commutative.  This process of opening a record is similar
to the usual practice of saying ``consider a semiring $R$'' and then
taking all semiring-related notation to refer to $R$ unless otherwise
specified.  

We need one more module from the standard library, called
\verb+∣-Reasoning+.  This is defined as a submodule of
\verb+Data.Nat.Divisibility+, and it makes it easier to reason with
chains of divisibility statements, analogous to the chains of
equalities that we described previously.
\begin{code}
open ∣-Reasoning
\end{code}

We also import three new modules that we mentioned previously:
\begin{code}
open import Sheffield.Data.Nat.LeastDivisor
open import Sheffield.Data.Nat.Primality
open import Sheffield.Data.Nat.Factorial
\end{code}

We next specify what we hope to construct.  In Agda, whenever we
construct an object with certain properties, we need to package it
together with a collection of proofs that it does indeed have those
properties.  In our case we construct a prime $p$ that is larger than
$n$, and we need to remember a proof of that inequality.  In Agda, the
proposition that $p$ is greater than $n$ is denoted by \verb+p > n+,
with spaces between the symbols.  Like all propositions in Agda, this
is a type, whose terms (if any) are the proofs that $p>n$.  The string
\verb+p>n+ (with no space) is a valid variable name in Agda, and it is
a standard idiom to use this name to refer to an arbitrary term of
type \verb+p > n+.  With this notation, we hope to construct a record
consisting of a natural number $p$, a proof (denoted by
\verb+p-prime+) that $p$ is prime, and a proof (denoted by \verb+p>n+)
that $p>n$.  The next block of code defines \verb+LargerPrime n+ (with
a capital L) to be the set of such records.

\begin{code}
record LargerPrime (n : ℕ) : Set where
  field
    p : ℕ
    p-prime : Prime p
    p>n : p > n
\end{code}

We now want to define a function \verb+largerPrime+ (with a lower case
l) which constructs an element \verb+largerPrime n+ of
\verb+LargerPrime n+ for each natural number $n$.  In Agda's notation,
this means that \verb+largerPrime+ is a term of type 
\verb+(n : ℕ) → LargerPrime n+.  Agda's type checking system is strong
enough that to ensure that any term that it accepts as having the
above type gives a valid proof of Euclid's theorem.

The next few lines are housekeeping:
\begin{code}
largerPrime : (n : ℕ) → LargerPrime n
largerPrime n = record {
    p = p ; 
    p-prime = p-prime ; 
    p>n = p>n
  } where
\end{code}

The rest of the code is indented at least as much as the keyword
\verb+where+, which means that it is treated as a single block.  The
above lines tell Agda that this block will define \verb+p+,
\verb+p-prime+ and \verb+p>n+ with the advertised types.

We next invoke the \verb+leastDivisor+ function defined in the module 
\verb+Extra.Data.Nat.LeastDivisor+.
\begin{code}
    L = leastDivisor (1 + (n !)) (s≤s (n!≥1 n)) 
\end{code}

The \verb+leastDivisor+ function takes two arguments: a natural number
and a proof that that number is at least two.  For the number we take
$1+(n!)$.  The module \verb+Extra.Data.Nat.Factorial+ defines a
function \verb+n!≥1+ such that \verb+n!≥1 n+ is a proof that 
\verb+1 ≤ n!+, and \verb+Data.Nat+ defines a function \verb+s≤s+ that
converts proofs of \verb+a ≤ b+ to proofs of \verb!1 + a ≤ 1 + b!.  We
can thus use \verb+s≤s (n!≥1 n)+ as the second argument to
\verb+leastDivisor+, and we define \verb+L+ to be the value returned
by this function.  Now \verb+L+ is a record with seven fields.  There
is a field called \verb+p+ whose value is a natural number, a field
called \verb+p-prime+ whose value is a proof that \verb+p+ is prime,
and a field called \verb+p-least+ whose value is a proof that no
number with $2\leq k<p$ divides $1+(n!)$.  

There is also a field called \verb+p∣n+.  The name of this field is
designed to make sense when the first argument to \verb+leastDivisor+
is called \verb+n+.  Its value in our context is in fact a proof that
$p$ divides $1+(n!)$, not a proof that $p$ divides $n$.  

We now open the record \verb+L+:
\begin{code}
    open LeastDivisor L renaming ( p≤n to p≤1+n! ; p∣n to p∣1+n! )
\end{code}
This allows us to refer to the fields in \verb+L+ by their short
names, except that we have given two of the fields new names that make
more sense in our context.  In particular, this defines \verb+p+ and
\verb+p-prime+ as required, so we just need to define \verb+p>n+. 

We first declare the type of \verb+p>n+:
\begin{code}
    p>n : p > n
\end{code}

We next have a \verb+with+ clause:
\begin{code}
    p>n with (suc n) ≤? p
\end{code}
Here \verb+suc+ is the successor function, taking $n$ to $1+n$.  Next,
there is a function called \verb+_≤?_+ defined in \verb+Data.Nat+.
This is an example of a useful notational mechanism in Agda: when the
name of a function involves underscores, the position of those
underscores indicates how the arguments are placed relative to the
function symbol.  Because the name \verb+_≤?_+ starts and ends with an
underscore, we can write \verb+n ≤? m+ for the value of the function
at a pair of natural numbers \verb+n+ and \verb+m+.  That value will
either have the form \verb+yes r+ (where \verb+r+ is a proof that
$n\leq m$) or \verb+no q+ (where \verb+q+ is a proof that $n\not\leq
m$).  (These are terms of the type \verb+Dec (n ≤ m)+, which is
defined in \verb+Relation.Nullary.Core+.)  The clause 
\verb+p>n with (suc n) ≤? p+ indicates that we will define \verb+p>n+
using two separate cases, depending on the value of 
\verb+(suc n) ≤? p+.  If this value has the form \verb+yes r+ then
\verb+r+ must be a proof that \verb+p > n+ and we can just take
\verb+p>n+ to be \verb+r+.  (This relies on the fact that 
\verb+p > n+ is \emph{by definition} the same as \verb+(suc n) ≤ p+,
as we see by reading the code for \verb+Data.Nat+.)  This is
implemented by the following line:
\begin{code}
    p>n | yes r = r
\end{code}

Now what if \verb+(suc n) ≤? p+ has the form \verb+no q+ for some
\verb+q+?  Here \verb+q+ would have to be a proof that \verb+p ≤ n+,
which cannot actually happen.  Nonetheless, Agda forces use to deal
with this hypothetical case, and prove that it is vacuous.
This works as follows.  Agda notation for the
empty type is \verb+⊥+.  For any set \verb+W+ there is a term
\verb+⊥-elim+ of type \verb+(⊥ → W)+.  Logically, this corresponds to
the principle that a falsity implies everything; set-theoretically, it
corresponds to the fact that the empty set is initial in the category
of sets.  (The set \verb+W+ is an implicit argument to the
\verb+⊥-elim+ function, given in curly brackets when that function is
defined in \verb+Data.Empty+.)  Next, the function \verb+Prime+
defined in \verb+Data.Nat.Primality+ sends a natural number $n$ to the
set of proofs that $n$ is prime.  When $n$ is given as a double
successor, the set \verb+(Prime n)+ is defined in an obvious way in
terms of divisibility properties.  However, the two initial cases
$n=0$ and $n=1$ are handled separately, with 
\verb+Prime 0 = Prime 1 = ⊥+ by definition.  We handle the 
\verb+no q+ case by constructing from \verb+q+ a proof that $1$ is
prime, or in other words a term \verb+1-prime+ of type 
\verb+Prime 1 = ⊥+.  We then apply \verb+⊥-elim+ to \verb+1-prime+ to
get a term of whatever type we want; in this case, a term of type 
\verb+(p > n)+.  The line 
\begin{code}
    p>n | no  q = ⊥-elim 1-prime where
\end{code}
indicates that we will handle the \verb+no q+ case by the general
approach discussed above, and promises that the following block of
code will eventually define \verb+1-prime+.  Note that the type
checker knows what type \verb+p>n+ is supposed to
have, and supplies this type as the implicit argument to
\verb+⊥-elim+.  It also knows that \verb+1-prime+ must have type
\verb+⊥+ in order to be an acceptable explicit argument to
\verb+⊥-elim+, and when we get to the definition of \verb+1-prime+ it
will check that we have indeed provided a term of type \verb+⊥+.

The rest of the code forms another \verb+where+ block nested inside
the \verb+where+ block that we introduced earlier, so it is indented
by two more spaces.

We now construct a proof that $p$ divides $n!$.  The
module \verb+Data.Nat.Factorial+ defines a function \verb+k∣n!+ that
takes a pair of inequalities \verb+1 ≤ k+ and \verb+k ≤ n+, and
returns a proof that \verb+k+ divides \verb+n !+.  We have a proof
called \verb+p-prime+ that \verb+p+ is prime, and the function
\verb+prime≥1+ defined in \verb+Extra.Data.Nat.Primality+ can be used
to convert this to a proof that \verb+1 ≤ p+.  By hypothesis we have a
proof called \verb+q+ that \verb+p > n+ is false, and using the
functions \verb+≰⇒>+ and \verb+≤-pred+ from \verb+Data.Nat+ we convert
this to a proof that \verb+p ≤ n+ is true.  After feeding these
ingredients to the function \verb+k∣n!+ we obtain the required proof
that \verb+p+ divides \verb+n !+.  We denote this proof by 
\verb+p∣n!+.
\begin{code}
      p∣n! : p ∣ n !
      p∣n! = k∣n! (prime≥1 p-prime) (≤-pred (≰⇒> q))
\end{code}

We now need a proof that \verb+p+ divides \verb|n ! + 1|.  We have
already extracted from the record \verb+L+ a proof (denoted by
\verb|p∣1+n!|) that \verb+p+ divides \verb|1 + n !|.  Although 
\verb|n ! + 1| is provably equal to \verb|1 + n !|, these two terms
have a different internal representation so we cannot just use
\verb|p∣1+n!| as a proof that \verb|p ∣ n ! + 1|.  However, we also
extracted a function called \verb!+-comm! from
\verb+Data.Nat.Properties.isCommutativeSemiring+, and 
\verb|(+-comm 1 (n !))| is a proof that 
\verb|1 + n ! ≡ n ! + 1|.  Using notation established in the module
\verb+∣-Reasoning+ we can string these proofs together:
\begin{code}
      p∣n!+1 : p ∣ n ! + 1
      p∣n!+1 = begin p ∣⟨ p∣1+n! ⟩ 1 + (n !) ≡⟨ +-comm 1 (n !) ⟩ (n !) + 1 ∎
\end{code}

We next use the function \verb+∣-∸+ defined in
\verb+Data.Nat.Divisibility+.  Given proofs that \verb+i+ divides
\verb+n + m+ and \verb+n+, this returns a proof that \verb+i+ divides
\verb+m+.  Thus, we can pass in our proofs that \verb+p+ divides
\verb+n !+ and \verb|n ! + 1|, and get back a proof that \verb+p+
divides \verb+1+.
\begin{code}
      p∣1 : p ∣ 1
      p∣1 = ∣-∸ p∣n!+1 p∣n!
\end{code}

The module \verb+Data.Nat.Divisibility+ also defines a function called
\verb+∣1⇒≡1+, which can be used to convert our proof that $p$ divides
$1$ to a proof that $p=1$.  
\begin{code}
      p≡1 : p ≡ 1
      p≡1 = ∣1⇒≡1 p∣1
\end{code}

We conclude by using the function \verb+subst+ defined in
\verb+Relation.Binary.PropositionalEquality.Core+.  Roughly speaking,
this works as follows.  The first argument is a set \verb+A+ depending
on a parameter \verb+x+.  The second argument is a proof of 
\verb+u ≡ v+, where \verb+u+ and \verb+v+ are possible values of
\verb+x+.  The third argument is an element of the set \verb+(A u)+,
and the return value is the same thing regarded as an element of
\verb+(A v)+.  We have a proof that \verb+p ≡ 1+ and a proof that
\verb+p+ is prime, so we can use \verb+subst+ to produce a proof that
\verb+1+ is prime.  
\begin{code}
      1-prime : Prime 1
      1-prime = subst Prime p≡1 p-prime
\end{code}
As discussed previously, this element \verb+1-prime+ can be fed into
\verb+⊥-elim+ to give a tautological proof of our theorem in the
vacuous case where \verb+p ≤ n+.

\end{document}