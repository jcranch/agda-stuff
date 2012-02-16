module Sheffield.CategoryTheory-Set.Functors.Properties where

open import Level
open import Relation.Binary.PropositionalEquality

open import Sheffield.CategoryTheory-Set.Categories
open import Sheffield.CategoryTheory-Set.Functors
import Sheffield.CategoryTheory-Set.Functors.Composition
open import Sheffield.CategoryTheory-Set.Functors.Isomorphism
open import Sheffield.CategoryTheory-Set.NaturalTransformations


module unitors-iso {ℓ₁ ℓ′₁ ℓ₂ ℓ′₂ : Level} 
    {C : Category {ℓ₁} {ℓ′₁}} {D : Category {ℓ₂} {ℓ′₂}}
    (F : Functor C D) where

    open Sheffield.CategoryTheory-Set.Functors.Composition.unitors F
    open Category D

    private
      F₀ = Functor.obj F
      F₁ = λ {x} {y} f → Functor.hom F {x} {y} f

    ⊙-unitor-l-iso : Isomorphism₁ ⊙-unitor-l
    ⊙-unitor-l-iso = make-Iso₁ ⊙-unitor-l⁻¹ (λ x → id-l (id (F₀ x))) (λ x → id-l (id (F₀ x)))

    ⊙-unitor-r-iso : Isomorphism₁ ⊙-unitor-r
    ⊙-unitor-r-iso = make-Iso₁ ⊙-unitor-r⁻¹ (λ x → id-l (id (F₀ x))) (λ x → id-l (id (F₀ x)))

open unitors-iso public


module associators-iso {ℓ₁ ℓ′₁ ℓ₂ ℓ′₂ ℓ₃ ℓ′₃ ℓ₄ ℓ′₄ : Level} 
    {C₁ : Category {ℓ₁} {ℓ′₁}} {C₂ : Category {ℓ₂} {ℓ′₂}}
    {C₃ : Category {ℓ₃} {ℓ′₃}} {C₄ : Category {ℓ₄} {ℓ′₄}}
    (H : Functor C₃ C₄) (G : Functor C₂ C₃) (F : Functor C₁ C₂) where

  open Sheffield.CategoryTheory-Set.Functors.Composition.associators H G F

  private
    obj₁ = Category.obj C₁
    obj₂ = Category.obj C₂
    obj₃ = Category.obj C₃
    obj₄ = Category.obj C₄
    hom₁ = Category.hom C₁
    hom₂ = Category.hom C₂
    hom₃ = Category.hom C₃
    hom₄ = Category.hom C₄

    _•₄_ : {x y z : obj₄} → hom₄ y z → hom₄ x y → hom₄ x z
    _•₄_ = Category.compose C₄

    H₀ = Functor.obj H
    G₀ = Functor.obj G
    F₀ = Functor.obj F
    H₁ : {x y : obj₃} (f : hom₃ x y) → hom₄ (H₀ x) (H₀ y)
    H₁ {x} {y} f = Functor.hom H f
    G₁ : {x y : obj₂} (f : hom₂ x y) → hom₃ (G₀ x) (G₀ y)
    G₁ {x} {y} f = Functor.hom G f
    F₁ : {x y : obj₁} (f : hom₁ x y) → hom₂ (F₀ x) (F₀ y)
    F₁ {x} {y} f = Functor.hom F f

  ⊙-associator-iso : Isomorphism₁ ⊙-associator
  ⊙-associator-iso = make-Iso₁ ⊙-associator⁻¹ (λ x → Category.id-l C₄ (NatTrans.component ⊙-associator x)) (λ x → Category.id-r C₄ (NatTrans.component ⊙-associator⁻¹ x))

open associators-iso public