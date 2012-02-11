--- In this module we define the factorial function and prove a
--- couple of basic properties.  For the moment we have just done
--- the minimum necessary for the proof that there are infinitely
--- many primes.

module Factorial where 

open import Algebra
open import Algebra.Structures
open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.Divisibility renaming (poset to ∣-poset)
open import Data.Fin as Fin hiding (_+_ ; _<_ ; _≤_ ; pred)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
private
  module CS = CommutativeSemiring Data.Nat.Properties.commutativeSemiring

open ≡-Reasoning
open DecTotalOrder decTotalOrder hiding (_≤_) renaming (refl to ≤-refl ; trans to ≤-trans)
open IsCommutativeSemiring isCommutativeSemiring hiding (refl ; sym ; trans)

_! : ℕ → ℕ

0 ! = 1
(suc n) ! = (suc n) * (n !)  

private 
  div-aux : (m n p : ℕ) → (m ∣ n) → (m ∣ (p * n))
  div-aux m n p m∣n = Poset.trans ∣-poset m∣n (divides p refl)

  div-aux′ : (m n p : ℕ) → (m ∣ n) → (m ∣ (n * p))
  div-aux′ m n p m∣n = Poset.trans ∣-poset m∣n (divides p (*-comm n p))

-- We now prove that if 0 ≤ k < n then k+1 divides n!
fact-div : {k n : ℕ} → k < n → suc k ∣ n !
fact-div k<n = aux (≤⇒≤′ k<n) where
  aux : {k n : ℕ} → k <′ n → suc k ∣ n !
  aux {k} .{suc k} ≤′-refl = div-aux′ (suc k) (suc k) (k !) (Poset.refl ∣-poset)
  aux {k} {suc n} (≤′-step m≤′n) = div-aux (suc k) (n !) (suc n) (aux m≤′n)

m≤n+*m : (m n : ℕ) → (m ≤ (suc n) * m)
m≤n+*m m n = m≤m+n m (n * m) 

-- We now prove that n! ≥ 1 for all n
n!≥1 : ∀ n → ((n !) ≥ 1)
n!≥1 0 = s≤s z≤n
n!≥1 (suc m) = ≤-trans (n!≥1 m) (m≤n+*m (m !) m)

