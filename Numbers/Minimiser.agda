------------------------------------------------------------------------
-- Minima for sets of natural numbers
--
-- Classically, every nonempty set of natural numbers has a smallest
-- element.  A constructive statement along these lines is as follows.
-- Suppose we have a proposition P for natural numbers, a natural number
-- k, and a proof u of (P k).  From this we hope to construct a triple
-- (n,p,q) where n is a natural number, p is a proof of (P n), and q 
-- is a proof of ¬ (P j) for all j < n.  In the constructive world this
-- is not possible without one further ingredient: we need a decision
-- oracle P? for P.  The framework for such oracles is defined in the
-- packages Relation.Nullary and Relation.Unary, which we import below.
-- The idea is that P? is a function which, for each natural number j,
-- returns either a term (yes x) (with x a proof of (P j)) or a term 
-- (no y) (with y a proof of ¬ (P j)).
--
-- We organise our definitions as follows.
-- An ℕ-set is a record consisting of a proposition P : ℕ → Set and
-- a decision oracle P? for P.  A minimiser for an ℕ-set is a triple
-- (n,p,q) as discussed above.  The main objective of this file is
-- to define a function (minimiser S n u) which takes an ℕ-set S,
-- an integer n and a proof u of (P n), and returns a minimiser 
-- for S.  To define (minimiser S n u) we separate the cases 
-- where n = zero and where n = (suc m) = m+1 for some m.  In the
-- first case zero is clearly the smallest number n where (P n) holds,
-- so we return (zero,u,v), where v is trivially defined because it
-- has empty domain.  In the second case we let S' be an ℕ-set 
-- corresponding in classical terms to {k ∈ ℕ : k+1 ∈ S}, so 
-- m ∈ S'.  We can regard u as a proof that m ∈ S', so we can 
-- assume that (minimiser S' m u) is already defined.  recursively. We
-- then put (minimiser S (m+1) u) = (minimiser S' m u)+1. 

------------------------------------------------------------------------

module Minimiser where

open import Data.Empty
open import Data.Fin as Fin 
open import Data.Fin.Dec
open import Data.Nat
open import Relation.Nullary
open import Relation.Unary
import Level 

record ℕ-set {c} : Set (Level.suc c) where
 field
  P : ℕ → Set c
  P? : Decidable P

record Minimiser (S : ℕ-set) : Set where 
 field
  value : ℕ
  valid : (ℕ-set.P S value)
  minimal : (k : Fin value) →  ¬ (ℕ-set.P S (Fin.toℕ k))

zero-minimiser : {S : ℕ-set} → (a : (ℕ-set.P S zero)) → Minimiser S
zero-minimiser a = record { value = zero; valid = a; minimal = λ ()} 

private
  P-shift : (ℕ → Set) → (ℕ → Set)
  P-shift P n = P (suc n)

  P?-shift : (P : ℕ → Set) → (P? : Decidable P) → (Decidable (P-shift P))
  P?-shift P P? n = (P? (suc n))

  S-shift : ℕ-set → ℕ-set
  S-shift S = record { P = (P-shift (ℕ-set.P S));
                       P? = (P?-shift (ℕ-set.P S) (ℕ-set.P? S))}

  Q-shift : (S : ℕ-set) →
            (M : Minimiser (S-shift S)) →
            (y : ¬ (ℕ-set.P S zero)) →
            (k : Fin (suc (Minimiser.value M))) →
            ¬ (ℕ-set.P S (Fin.toℕ k))
  Q-shift S M y zero = y
  Q-shift S M y (suc j) = Minimiser.minimal M j 

  M-shift : (S : ℕ-set) → (M : Minimiser (S-shift S)) → (Minimiser S)
  M-shift S M with (ℕ-set.P? S zero)
  ... | yes x = zero-minimiser x 
  ... | no y  = record { value = suc (Minimiser.value M);
                         valid = Minimiser.valid M;
                         minimal = Q-shift S M y }

minimiser : (S : ℕ-set) → (n : ℕ) → (u : (ℕ-set.P S n)) → (Minimiser S)
minimiser S zero u = zero-minimiser u 
minimiser S (suc m) u = M-shift S (minimiser (S-shift S) m u) 



