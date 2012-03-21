module Sheffield.CategoryTheory-Setoid.Terminal where

open import Level
open import Relation.Binary.PropositionalEquality

open import Sheffield.CategoryTheory-Setoid.Categories
open import Sheffield.CategoryTheory-Setoid.Functors
open import Sheffield.CategoryTheory-Setoid.NaturalTransformations



module fixed-category {ℓ₁ ℓ′₁ ℓ″₁ : Level} (C : Category {ℓ₁} {ℓ′₁} {ℓ″₁}) where

  open Category C
  open Iso C

  record IsTerminal (t : obj) : Set (ℓ₁ ⊔ ℓ′₁ ⊔ ℓ″₁) where
    constructor make-terminal

    field
      exists : (x : obj) → homset x t
      unique : {x : obj} (f : homset x t) → f ≈ exists x

    any-two-equal : {x : obj} (f g : homset x t) → f ≈ g
    any-two-equal f g = ≈-trans (unique f) (≈-sym (unique g))

  any-two-iso : {t₁ t₂ : obj} → IsTerminal t₁ → IsTerminal t₂ → t₁ ≅ t₂
  any-two-iso {t₁} {t₂} term₁ term₂ = make-iso
    (IsTerminal.exists term₂ t₁)
    (IsTerminal.exists term₁ t₂)
    (IsTerminal.any-two-equal term₁ _ _)
    (IsTerminal.any-two-equal term₂ _ _)

open fixed-category public



IsInitial : {ℓ₁ ℓ′₁ ℓ″₁ : Level} (C : Category {ℓ₁} {ℓ′₁} {ℓ″₁}) (t : Category.obj C) → Set (ℓ₁ ⊔ ℓ′₁ ⊔ ℓ″₁)
IsInitial C = IsTerminal (opposite C)

