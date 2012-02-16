module Sheffield.CategoryTheory-Set.Categories.Isomorphism where

open import Level

open import Sheffield.CategoryTheory-Set.Categories
open import Sheffield.CategoryTheory-Set.Functors
open import Sheffield.CategoryTheory-Set.Functors.Equality

infix 4 _≡₀_
record _≡₀_ {ℓ₁ ℓ₁′ ℓ₂ ℓ₂′ : Level} (C : Category {ℓ₁} {ℓ₁′}) (D : Category {ℓ₂} {ℓ₂′}) : Set (ℓ₁ ⊔ ℓ₁′ ⊔ ℓ₂ ⊔ ℓ₂′) where
  field
    F   : Functor C D
    F⁻¹ : Functor D C
    unit : F⁻¹ ⊙ F ≡₁ idFunctor C
    counit : F ⊙ F⁻¹ ≡₁ idFunctor D
