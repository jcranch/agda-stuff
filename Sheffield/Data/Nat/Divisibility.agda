module Sheffield.Data.Nat.Divisibility where 

open import Algebra
open import Algebra.Structures
open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.Divisibility renaming (poset to ∣-poset)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
private
  module CS = CommutativeSemiring Data.Nat.Properties.commutativeSemiring

open IsCommutativeSemiring isCommutativeSemiring hiding (refl ; sym ; trans)

left-* : {m n : ℕ} → (p : ℕ) → m ∣ n → m ∣ (p * n) 
left-* p m∣n = Poset.trans ∣-poset m∣n (divides p refl)

right-* : {m n : ℕ} → (p : ℕ) → m ∣ n → m ∣ (n * p) 
right-* {m} {n} p m∣n = Poset.trans ∣-poset m∣n (divides p (*-comm n p))