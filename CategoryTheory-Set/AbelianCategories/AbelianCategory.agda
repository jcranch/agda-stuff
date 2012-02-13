module AbelianCategories.AbelianCategory where

open import Level


open import AbelianCategories.Biproduct
open import AbelianCategories.Kernel
open import AbelianCategories.NormalMorphism
open import AbelianCategories.Zero
open import Categories
open import Limits.Interderivability
open import Limits.Product
open import Limits.Pullback


record IsAbelianCategory {ℓ ℓ′ : Level} {C : Category {ℓ} {ℓ′}} : Set (ℓ ⊔ ℓ′) where
  open Category C

  field
    zero-obj : obj
    isZero-obj : IsZero-obj C zero-obj

    hasPullbacks : HasPullbacks C
    hasPushouts : HasPushouts C

    hasKernels : HasKernels C isZero-obj
    hasCokernels : HasCokernels C isZero-obj

    allMonomorphismsNormal : AllMonomorphismsNormal C zero-obj isZero-obj
    allEpimorphismsNormal : AllEpimorphismsNormal C zero-obj isZero-obj

  open IsZero-obj isZero-obj

  hasProducts : HasProducts C
  hasProducts = terminal→pullbacks→products C term hasPullbacks

  hasCoproducts : HasCoproducts C
  hasCoproducts = terminal→pullbacks→products (opposite C) init hasPushouts


  -- to do:
  -- follow Borceux
  -- is it better to be less vague and demand that they're the cokernels of their kernels?


{-
  hasBiproducts : HasBiproducts C
  hasBiproducts x y = record {
    _⊕_ = x⊕y } where
    x⊕y = {!!}
-}