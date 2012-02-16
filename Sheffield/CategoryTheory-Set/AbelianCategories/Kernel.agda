module Sheffield.CategoryTheory-Set.AbelianCategories.Kernel where


open import Level
open import Relation.Binary.PropositionalEquality

open import Sheffield.CategoryTheory-Set.AbelianCategories.Zero
open import Sheffield.CategoryTheory-Set.Categories
open import Sheffield.CategoryTheory-Set.Limits.Equaliser
open import Sheffield.CategoryTheory-Set.Limits.Terminal
open import Sheffield.CategoryTheory-Set.Misc



module kernel-setup {ℓ ℓ′ : Level} (C : Category {ℓ} {ℓ′}) {z : Category.obj C} (z₀ : IsZero-obj C z) where

  open IsZero-obj z₀
  open Category C

  private
    terminal-morphism = exists-to-1 C z term
    initial-morphism = exists-to-1 (opposite C) z init


  record IsKernel {w x y : obj} (f : hom x y) (k : hom w x) : Set (ℓ ⊔ ℓ′) where
    constructor make-kernel

    private
      f₀ = zero-hom-witness C z₀ x y

    field
      zero-• : f • k ≡ f₀ • k
      equalises : IsEqualiser-lowbrow C f f₀ k zero-•



  -- monomorphisms have zero kernels

  module kernels-of-monomorphisms {x y : obj} (f : hom x y) (f-mono : monomorphism C f) where

    private
      f₀ = zero-hom-witness C z₀ x y
      k₀ = zero-hom-witness C z₀ z x

    kernel-mono : IsKernel f k₀
    kernel-mono = make-kernel e (make-equaliser H) where
      e = (trans (zero-hom-unique C z₀ (f • k₀) (initial-morphism-zero C z₀ (f • k₀))) (sym (zero-hom-unique C z₀ (f₀ • k₀) (initial-morphism-zero C z₀ (f₀ • k₀)))))
      H : {a : obj} (g : hom a x) → f • g ≡ f₀ • g → existsUnique (hom a z) _≡_ (λ h → k₀ • h ≡ g)
      H {a} g e = makeUnique w s u where
        w = terminal-morphism a
        s : k₀ • w ≡ g
        s = f-mono (k₀ • w) g p where
          p : f • (k₀ • w) ≡ f • g
          p = zeroes-equal C z₀ (f • (k₀ • w)) (f • g) (zero-compose-r C z₀ f (k₀ • w) (zero-compose-l C z₀ k₀ w (zero-hom-satisfies C z₀ z x))) (subst (IsZero-hom C z₀) (sym e) (zero-compose-l C z₀ f₀ g (zero-hom-satisfies C z₀ x y)))
        u : (h : hom a z) → k₀ • h ≡ g → h ≡ w
        u h e′ = unique-to-1 C z term h
  open kernels-of-monomorphisms public


  record Kernel {x y : obj} (f : hom x y) : Set (ℓ ⊔ ℓ′) where
    constructor kernel-intro
    field
      kernel-obj : obj
      kernel-hom : hom kernel-obj x
      isKernel : IsKernel f kernel-hom


  HasKernels : Set (ℓ ⊔ ℓ′)
  HasKernels = {x y : obj} (f : hom x y) → Kernel f

open kernel-setup public

HasCokernels : {ℓ ℓ′ : Level} (C : Category {ℓ} {ℓ′}) {z : Category.obj C} (z₀ : IsZero-obj C z) → Set (ℓ ⊔ ℓ′)
HasCokernels C {z} z₀ = HasKernels (opposite C) (zero-obj-opposite C z₀)