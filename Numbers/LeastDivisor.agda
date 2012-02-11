--- In this module we show that if n ≥ 2 and d is the smallest
--- divisor of n such that d ≥ 2, then d is prime.
---
--- It turns out to be inconvenient to carry around the hypotheses
--- n ≥ 2 and d ≥ 2.  Instead we write everything in terms of 
--- variables n' and d' with n = 2 + n' and d = 2 + d'.  Following
--- standard Agda conventions we will actually call these variables
--- n-2 and d-2 (with no spaces) rather than n' and d'.  At the
--- end of the module we define wrapper functions to allow us to 
--- work with n and d again.

module LeastDivisor where

import Level
open import Algebra
open import Data.Fin as Fin hiding (_+_ ; _≤_ ; pred)
open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.Divisibility
open import Data.Nat.Primality
open import Data.Product
open import Function
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Unary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

open CommutativeSemiring commutativeSemiring using (*-identity)
open ∣-Reasoning

open import Minimiser

data Divides-shifted : ℕ → ℕ → Set where
 divides-shifted :
  {n-2 d-2 : ℕ} (q-1 : ℕ) (eq : suc (suc n-2) ≡ (suc q-1) * (suc (suc d-2))) 
   → Divides-shifted n-2 d-2

divides-shifted-refl : (n-2 : ℕ) → Divides-shifted n-2 n-2
divides-shifted-refl n-2 = divides-shifted 0 (sym $ proj₁ *-identity (suc (suc n-2)))

shift-divides : {d-2 n-2 : ℕ} (x : suc (suc d-2) ∣ suc (suc n-2)) →
 Divides-shifted n-2 d-2

shift-divides (divides zero ())
shift-divides (divides (suc q-1) eq) = divides-shifted q-1 eq

unshift-divides : {n-2 d-2 : ℕ} (x : Divides-shifted n-2 d-2) → 
 suc (suc d-2) ∣ suc (suc n-2) 

unshift-divides (divides-shifted q-1 eq) = divides (suc q-1) eq

Divides-shifted? : (n-2 : ℕ) → (Relation.Unary.Decidable (Divides-shifted n-2))
Divides-shifted? n-2 d-2 with (suc (suc d-2)) ∣? (suc (suc n-2))
Divides-shifted? n-2 d-2 | yes x = yes (shift-divides x)
Divides-shifted? n-2 d-2 | no y = no (λ z → y (unshift-divides z)) 

Shifted-divisor-set : ℕ → ℕ-set
Shifted-divisor-set n-2 = record { P  = Divides-shifted n-2;
                                   P? = Divides-shifted? n-2 }

Least-divisor-shifted : ℕ → Set
Least-divisor-shifted n-2 = Minimiser (Shifted-divisor-set n-2)

least-divisor-shifted : (n-2 : ℕ) → Least-divisor-shifted n-2
least-divisor-shifted n-2 =
 minimiser (Shifted-divisor-set n-2) n-2 (divides-shifted-refl n-2)

least-divisor-shifted-value : ℕ → ℕ
least-divisor-shifted-value n-2 = 
 2 + Minimiser.value (least-divisor-shifted n-2)

least-divisor-shifted-prime : (n-2 : ℕ) → 
 Prime (least-divisor-shifted-value n-2)

least-divisor-shifted-prime n-2 k a = 
 c k (shift-divides d) where
 L = least-divisor-shifted n-2
 p-2 = Minimiser.value L
 b = unshift-divides (Minimiser.valid L)
 c = Minimiser.minimal L
 d = begin (2 + (Fin.toℕ k)) ∣⟨ a ⟩ (2 + p-2) ∣⟨ b ⟩ (2 + n-2) ∎
 
Least-divisor : (n : ℕ) → (2 ≤ n) → Set
Least-divisor n a = Least-divisor-shifted (pred (pred n))

least-divisor : (n : ℕ) → (a : 2 ≤ n) → (Least-divisor n a)
least-divisor 0 ()
least-divisor (suc 0) (s≤s ())
least-divisor (suc (suc n-2)) a = least-divisor-shifted n-2

least-divisor-value : (n : ℕ) → (a : 2 ≤ n) → ℕ
least-divisor-value 0 ()
least-divisor-value (suc 0) (s≤s ())
least-divisor-value (suc (suc n-2)) a = 
 least-divisor-shifted-value n-2

least-divisor-prime : (n : ℕ) → (a : 2 ≤ n) → 
 Prime (least-divisor-value n a) 
least-divisor-prime 0 ()
least-divisor-prime (suc 0) (s≤s ())
least-divisor-prime (suc (suc n-2)) a = 
 least-divisor-shifted-prime n-2

least-divisor-divides : (n : ℕ) (2≤n : 2 ≤ n) → least-divisor-value n 2≤n ∣ n
least-divisor-divides 0 ()
least-divisor-divides (suc 0) (s≤s ())
least-divisor-divides (suc (suc n-2)) 2≤n = unshift-divides (Minimiser.valid (least-divisor-shifted n-2))