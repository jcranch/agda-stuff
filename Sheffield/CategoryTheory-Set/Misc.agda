module Sheffield.CategoryTheory-Set.Misc where

open import Function
open import Level
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_ ; refl)


{-
cong₃ : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d} (f : A → B → C → D) {x y u v p q} → x ≡ y → u ≡ v → p ≡ q → f x u p ≡ f y v q
cong₃ f refl refl refl = refl
-}

record existsUnique {α β ℓ : Level} (A : Set α) (_≈_ : Rel A ℓ) (P : A → Set β) : Set (α ⊔ β ⊔ ℓ) where

  constructor makeUnique

  field
    witness : A
    satisfaction : P witness
    uniqueness : (a : A) → P a → a ≈ witness

anyTwoSimilar : {α β ℓ : Level} {A : Set α} {_≈_ : Rel A ℓ} {P : A → Set β} {x y : A} → IsEquivalence _≈_ → existsUnique A _≈_ P → P x → P y → x ≈ y
anyTwoSimilar {_≈_ = _≈_} {x = x} {y = y} ≈-equiv E Px Py = IsEquivalence.trans ≈-equiv (existsUnique.uniqueness E x Px) (IsEquivalence.sym ≈-equiv (existsUnique.uniqueness E y Py))