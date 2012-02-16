module Sheffield.CategoryTheory-Set.AbelianCategories.NormalMorphism where

open import Level

open import Sheffield.CategoryTheory-Set.AbelianCategories.Kernel
open import Sheffield.CategoryTheory-Set.AbelianCategories.Zero
open import Sheffield.CategoryTheory-Set.Categories


module normal-context {ℓ ℓ′ : Level} (C : Category {ℓ} {ℓ′}) {z : Category.obj C} (z₀ : IsZero-obj C z) where

  open Category C

  record NormalMonomorphism {x y : obj} (f : hom x y) (f-mono : monomorphism C f) : Set (ℓ ⊔ ℓ′) where
    field
      y⁺ : obj
      f⁺ : hom y y⁺
      isKernel : IsKernel C z₀ f⁺ f

  AllMonomorphismsNormal : Set (ℓ ⊔ ℓ′)
  AllMonomorphismsNormal = {x y : obj} (f : hom x y) (f-mono : monomorphism C f) → NormalMonomorphism f f-mono

open normal-context public

NormalEpimorphism : {ℓ ℓ′ : Level} (C : Category {ℓ} {ℓ′}) {z : Category.obj C} (z₀ : IsZero-obj C z) {x y : Category.obj C} (f : Category.hom C x y) (f-epi : epimorphism C f) → Set (ℓ ⊔ ℓ′)
NormalEpimorphism C z₀ = NormalMonomorphism (opposite C) (zero-obj-opposite C z₀)

AllEpimorphismsNormal : {ℓ ℓ′ : Level} (C : Category {ℓ} {ℓ′}) {z : Category.obj C} (z₀ : IsZero-obj C z) → Set (ℓ ⊔ ℓ′)
AllEpimorphismsNormal C z₀ = AllMonomorphismsNormal (opposite C) (zero-obj-opposite C z₀)

