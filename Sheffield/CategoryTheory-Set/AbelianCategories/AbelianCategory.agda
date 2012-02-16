module Sheffield.CategoryTheory-Set.AbelianCategories.AbelianCategory where

open import Level


open import Sheffield.CategoryTheory-Set.AbelianCategories.Biproduct
open import Sheffield.CategoryTheory-Set.AbelianCategories.Kernel
open import Sheffield.CategoryTheory-Set.AbelianCategories.NormalMorphism
open import Sheffield.CategoryTheory-Set.AbelianCategories.Zero
open import Sheffield.CategoryTheory-Set.Categories
open import Sheffield.CategoryTheory-Set.Limits.Interderivability
open import Sheffield.CategoryTheory-Set.Limits.Product
open import Sheffield.CategoryTheory-Set.Limits.Pullback
open import Sheffield.CategoryTheory-Set.Misc



record IsAbelianCategory {ℓ ℓ′ : Level} (C : Category {ℓ} {ℓ′}) : Set (ℓ ⊔ ℓ′) where
  open Category C

  field
    zero-obj : obj
    isZero-obj : IsZero-obj C zero-obj

    hasPullbacks : HasPullbacks C
    hasPushouts : HasPushouts C

    hasKernels : HasKernels C isZero-obj
    hasCokernels : HasCokernels C isZero-obj

    allMonomorphismsNormal : AllMonomorphismsNormal C isZero-obj
    allEpimorphismsNormal : AllEpimorphismsNormal C isZero-obj

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


{-
opposite-abelian : {ℓ ℓ′ : Level} {C : Category {ℓ} {ℓ′}} → IsAbelianCategory C → IsAbelianCategory (opposite C)
opposite-abelian {C = C} CisAbelian = record {
  zero-obj = zero-obj ;
  isZero-obj = isZero-obj′ ;
  hasPullbacks = hasPushouts ;
  hasPushouts = hasPullbacks′ ;
  hasKernels = hasCokernels ;
  hasCokernels = hasKernels′ ;
  allMonomorphismsNormal = allEpimorphismsNormal ;
  allEpimorphismsNormal = allMonomorphismsNormal′ } where
  open IsAbelianCategory CisAbelian
  isZero-obj′ = zero-obj-opposite C isZero-obj
  hasPullbacks′ : HasPushouts (opposite C)
  hasPullbacks′ f₁ f₂ = pullback-intro _×̣_ proj₁ proj₂ equation isPullback′ where
    open Pullback (hasPullbacks f₁ f₂)
    open IsPullback-lowbrow C f₁ f₂ proj₁ proj₂ equation isPullback
    isPullback′ : IsPullback-lowbrow (opposite (opposite C)) f₁ f₂ proj₁ proj₂ equation
    isPullback′ = make-pullback (λ q₁ q₂ a → factorisations q₁ q₂ a)
  hasKernels′ : HasCokernels (opposite C) isZero-obj′
  hasKernels′ f = kernel-intro kernel-obj kernel-hom isKernel′ where
    open Kernel C isZero-obj (hasKernels f)
    open IsKernel C isZero-obj isKernel
    isKernel′ = make-kernel zero-• {!equalises!}
  allMonomorphismsNormal′ : AllEpimorphismsNormal (opposite C) isZero-obj′
  allMonomorphismsNormal′ f f-mono = {!!}
-}