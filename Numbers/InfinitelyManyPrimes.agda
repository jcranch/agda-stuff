-- This file proves that there are infinitely many primes, or more
-- precisely, that for any natural number n there exists a prime p
-- with p > n.  Our approach is to define p to be the smallest
-- divisor of n ! + 1 such that p > 1, and then check that p has the 
-- required properties.
-- The proof that p is indeed larger than n is by contradiction: if it
-- is no larger then p divides both n! and n!+1, and hence divides 1.

module InfinitelyManyPrimes where

open import Algebra.Structures
open import Data.Empty
open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.Divisibility
open import Data.Nat.Primality
open import Relation.Nullary.Core
open import Relation.Binary.PropositionalEquality

open ∣-Reasoning
open IsCommutativeSemiring isCommutativeSemiring using ( +-comm )

open import LeastDivisor
open import Factorial


larger-prime : ℕ → ℕ
larger-prime n = least-divisor-value (1 + (n !)) (s≤s (n!≥1 n))

larger-prime-prime : (n : ℕ) → Prime (larger-prime n)
larger-prime-prime n = least-divisor-prime (1 + (n !)) (s≤s (n!≥1 n))

larger-prime-larger : (n : ℕ) → (n < larger-prime n)
larger-prime-larger n with suc n ≤? larger-prime n
larger-prime-larger n | yes r = r
larger-prime-larger n | no ¬r = ⊥-elim 1-prime where

  suc-pred : {n : ℕ} → n > 0 → suc (pred n) ≡ n
  suc-pred (s≤s m≤n) = refl

  p = larger-prime n

  p>0 : p > 0
  p>0 with p | inspect larger-prime n
  p>0 | zero | [ e ] = ⊥-elim (subst Prime e (larger-prime-prime n))
  p>0 | suc p′ | [ e ] = s≤s z≤n

  suc-pred-p : suc (pred p) ≡ p
  suc-pred-p = suc-pred p>0

  p≤n : p ≤ n
  p≤n = ≤-pred (≰⇒> ¬r)

  p∣n! : p ∣ n !
  p∣n! = subst (λ x → x ∣ n !) suc-pred-p (fact-div (subst (λ x → x ≤ n) (sym suc-pred-p) p≤n))

  p∣n!+1 : p ∣ n ! + 1
  p∣n!+1 = begin
    p
      ∣⟨ least-divisor-divides (1 + n !) (s≤s (n!≥1 n)) ⟩
    1 + n !
      ≡⟨ +-comm 1 (n !) ⟩
    n ! + 1 ∎

  p∣1 : p ∣ 1
  p∣1 = ∣-∸ p∣n!+1 p∣n!

  p≡1 : p ≡ 1
  p≡1 = ∣1⇒≡1 p∣1

  1-prime : Prime 1
  1-prime = subst Prime p≡1 (larger-prime-prime n)

