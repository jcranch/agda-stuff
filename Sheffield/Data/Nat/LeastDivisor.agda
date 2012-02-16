module Sheffield.Data.Nat.LeastDivisor where

open import Data.Nat
open import Data.Nat.Divisibility renaming (poset to ∣-poset)
open import Data.Nat.Primality
open import Relation.Nullary
open import Relation.Unary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

open import Data.Fin hiding (_≤_ ; _<_ ; _+_)

open ∣-Reasoning

open import Sheffield.Data.Nat.Minimiser

record LeastDivisor {n : ℕ} : Set where
 field 
  2≤n : 2 ≤ n 
  p : ℕ
  2≤p : 2 ≤ p
  p≤n : p ≤ n
  p∣n : p ∣ n
  p-least : (k : ℕ) → 2 ≤ k → k < p → ¬ ( k ∣ n )  
  p-prime : Prime p
 
leastDivisor : (n : ℕ) → (2≤n : 2 ≤ n) → (LeastDivisor {n})
leastDivisor 0 ()
leastDivisor (suc 0) (s≤s ())
leastDivisor (suc (suc n-2)) 2≤n = record {
    2≤n = 2≤n ;
    p = p ; 
    2≤p = s≤s (s≤s z≤n) ;
    p∣n = p∣n ;
    p≤n = ∣⇒≤ p∣n ;
    p-least = p-least ;
    p-prime = p-prime
  } where
    n = suc (suc n-2)
    P : ℕ → Set
    P k-2 = suc (suc k-2) ∣ n
    P? : Relation.Unary.Decidable P
    P? k-2 = suc (suc k-2) ∣? n
    S : ℕ-set
    S = P , P?
    M = minimiser S n-2 (Poset.refl ∣-poset)
    open Minimiser M renaming ( n to p-2 ; Pn to p∣n )
    p = suc (suc p-2)

    p-least : (k : ℕ) → 2 ≤ k → k < p → ¬ ( k ∣ n )  
    p-least zero () _ _ 
    p-least (suc zero) (s≤s ()) _ _ 
    p-least (suc (suc k-2)) 2≤k (s≤s (s≤s k-2<p-2)) k∣n =
      minimal k-2 k-2<p-2 k∣n
 
    p-prime : Prime p
    p-prime k k+2∣p = minimal (toℕ k) (Fin<top k) k+2∣n where
      Fin<top : {n : ℕ} → (k : Fin n) → (toℕ k < n)
      Fin<top zero = s≤s z≤n
      Fin<top (suc i) = s≤s (Fin<top i)
      k+2∣n = begin (2 + (toℕ k)) ∣⟨ k+2∣p ⟩ p ∣⟨ p∣n ⟩ n ∎

