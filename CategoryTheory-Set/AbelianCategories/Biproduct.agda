module AbelianCategories.Biproduct where

open import Level
open import Relation.Binary.PropositionalEquality

open import AbelianCategories.Zero
open import Categories
open import Limits.Product
open import Limits.Product.Properties
open import Misc


module biproduct-context {ℓ ℓ′ : Level} (C : Category {ℓ} {ℓ′}) where

  open Category C

  record IsBiproduct (x y x⊕y : obj) (p₁ : hom x⊕y x) (p₂ : hom x⊕y y) (i₁ : hom x x⊕y) (i₂ : hom y x⊕y) : Set (ℓ ⊔ ℓ′) where
    constructor make-biproduct
    field
      bi-product : IsProduct-lowbrow C x y x⊕y p₁ p₂
      bi-coproduct : IsCoproduct-lowbrow C x y x⊕y i₁ i₂

  record Biproduct (x y : obj) : Set (ℓ ⊔ ℓ′) where
    field
      _⊕_ : obj
      proj₁ : hom _⊕_ x
      proj₂ : hom _⊕_ y
      inj₁ : hom x _⊕_
      inj₂ : hom y _⊕_
      isBiproduct : IsBiproduct x y _⊕_ proj₁ proj₂ inj₁ inj₂

  HasBiproducts : Set (ℓ ⊔ ℓ′)
  HasBiproducts = (x y : obj) → Biproduct x y

open biproduct-context public


