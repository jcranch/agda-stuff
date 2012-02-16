module Sheffield.Data.Nat.Minimiser where

open import Data.Empty
open import Data.Nat
open import Relation.Nullary
open import Relation.Unary
import Level 

record ℕ-set {c} : Set (Level.suc c) where
  constructor _,_
  field
    P : ℕ → Set c
    P? : Decidable P

record Minimiser (S : ℕ-set) : Set where 
  constructor _,_,_
  open ℕ-set S
  field
    n : ℕ
    Pn : P n
    minimal : (k : ℕ) →  (k < n) → ¬ (P k)

0-min : {S : ℕ-set} → (P0 : (ℕ-set.P S zero)) → Minimiser S
0-min P0 = 0 , P0 , λ k → λ ()

minimiser : (S : ℕ-set) → (n : ℕ) → (ℕ-set.P S n) → (Minimiser S)
minimiser S 0 P0 = 0-min P0 
minimiser S (suc m) Q with (ℕ-set.P? S) 0
... | yes P0 = 0-min P0
... | no ¬P0 = suc n′ , P′n′ , minimal where 
    P′ : ℕ → Set
    P′ k = (ℕ-set.P S) (suc k)
    P′? : Decidable P′ 
    P′? k = (ℕ-set.P? S) (suc k)
    S′ : ℕ-set
    S′ = P′ , P′?
    M′ = minimiser S′ m Q
    n′ = Minimiser.n M′
    P′n′ = Minimiser.Pn M′
    minimal′ = Minimiser.minimal M′
    minimal : (k : ℕ) →  (k < suc n′) → ¬ ((ℕ-set.P S) k)
    minimal 0 _ = ¬P0
    minimal (suc k) (s≤s k<n′) = minimal′ k k<n′ 




