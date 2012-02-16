module Sheffield.CategoryTheory-Set.Categories.Equivalence where

open import Function
open import Level
open import Relation.Binary.PropositionalEquality

open import Sheffield.CategoryTheory-Set.Categories
open import Sheffield.CategoryTheory-Set.Functors
open import Sheffield.CategoryTheory-Set.Functors.Isomorphism
open import Sheffield.CategoryTheory-Set.NaturalTransformations



record Equivalence {ℓ₁ ℓ₁′ ℓ₂ ℓ₂′ : Level} {C : Category {ℓ₁} {ℓ₁′}} {D : Category {ℓ₂} {ℓ₂′}} (F : Functor C D) : Set (ℓ₁ ⊔ ℓ₁′ ⊔ ℓ₂ ⊔ ℓ₂′) where
  constructor makeEquiv
  field
    F⁻¹ : Functor D C
    unit : F⁻¹ ⊙ F ≅₁ idFunctor C
    counit : F ⊙ F⁻¹ ≅₁ idFunctor D


infix 4 _≅₀_
record _≅₀_ {ℓ₁ ℓ₁′ ℓ₂ ℓ₂′ : Level} (C : Category {ℓ₁} {ℓ₁′}) (D : Category {ℓ₂} {ℓ₂′}) : Set (ℓ₁ ⊔ ℓ₁′ ⊔ ℓ₂ ⊔ ℓ₂′) where
  constructor make-≅₀
  field
    F : Functor C D
    isEquiv : Equivalence F


cong₀ : {ℓ₁ ℓ₁′ ℓ₂ ℓ₂′ : Level} {C : Category {ℓ₁} {ℓ₁′}} {D : Category {ℓ₂} {ℓ₂′}} (F : Functor C D) (F⁻¹ : Functor D C) (unit : F⁻¹ ⊙ F ≅₁ idFunctor C) (counit : F ⊙ F⁻¹ ≅₁ idFunctor D) → C ≅₀ D
cong₀ F F⁻¹ unit counit = make-≅₀ F (makeEquiv F⁻¹ unit counit)


opposite² : {ℓ₁ ℓ₁′ : Level} (C : Category {ℓ₁} {ℓ₁′}) → opposite (opposite C) ≅₀ C
opposite² C = cong₀ F F⁻¹ I J where

  F : Functor (opposite (opposite C)) C
  F = makeFunctor id id (λ x → refl) (λ g f → refl)
  F⁻¹ : Functor C (opposite (opposite C))
  F⁻¹ = makeFunctor id id (λ x → refl) (λ g f → refl)

  I : F⁻¹ ⊙ F ≅₁ idFunctor (opposite (opposite C))
  I = make-≅₁ Θ (make-Iso₁ Θ⁻¹ ε η) where
    Θ = makeNatTrans (Category.id C) (λ f → trans (Category.id-l C f) (sym (Category.id-r C f)))
    Θ⁻¹ = makeNatTrans (Category.id C) (λ f → trans (Category.id-l C f) (sym (Category.id-r C f)))
    ε = λ x → Category.id-l C _
    η = λ x → Category.id-l C _

  J : F ⊙ F⁻¹ ≅₁ idFunctor C
  J = make-≅₁ Θ (make-Iso₁ Θ⁻¹ ε η) where
    Θ = makeNatTrans (Category.id C) (λ f → trans (Category.id-l C f) (sym (Category.id-r C f)))
    Θ⁻¹ = makeNatTrans (Category.id C) (λ f → trans (Category.id-l C f) (sym (Category.id-r C f)))
    ε = λ x → Category.id-l C _
    η = λ x → Category.id-l C _

