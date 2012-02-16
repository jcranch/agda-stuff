module Sheffield.CategoryTheory-Set.Functors.Composition where

open import Level
open import Relation.Binary.PropositionalEquality

open import Sheffield.CategoryTheory-Set.Categories
open import Sheffield.CategoryTheory-Set.Functors
open import Sheffield.CategoryTheory-Set.NaturalTransformations


module unitors {ℓ₁ ℓ′₁ ℓ₂ ℓ′₂ : Level} 
    {C : Category {ℓ₁} {ℓ′₁}} {D : Category {ℓ₂} {ℓ′₂}}
    (F : Functor C D) where

    open Category D

    private
      F₀ = Functor.obj F
      F₁ = λ {x} {y} f → Functor.hom F {x} {y} f

    ⊙-unitor-l : NatTrans (idFunctor D ⊙ F) F
    ⊙-unitor-l = makeNatTrans (λ x → id (F₀ x)) (λ f → trans (id-l (F₁ f)) (sym (id-r (F₁ f))))

    ⊙-unitor-l⁻¹ : NatTrans F (idFunctor D ⊙ F)
    ⊙-unitor-l⁻¹ = makeNatTrans (λ x → id (F₀ x)) (λ f → trans (id-l (F₁ f)) (sym (id-r (F₁ f))))

    ⊙-unitor-r : NatTrans (F ⊙ idFunctor C) F
    ⊙-unitor-r = makeNatTrans (λ x → id (F₀ x)) (λ f → trans (id-l (F₁ f)) (sym (id-r (F₁ f))))

    ⊙-unitor-r⁻¹ : NatTrans F (F ⊙ idFunctor C)
    ⊙-unitor-r⁻¹ = makeNatTrans (λ x → id (F₀ x)) (λ f → trans (id-l (F₁ f)) (sym (id-r (F₁ f))))

open unitors public


module associators {ℓ₁ ℓ′₁ ℓ₂ ℓ′₂ ℓ₃ ℓ′₃ ℓ₄ ℓ′₄ : Level} 
    {C₁ : Category {ℓ₁} {ℓ′₁}} {C₂ : Category {ℓ₂} {ℓ′₂}}
    {C₃ : Category {ℓ₃} {ℓ′₃}} {C₄ : Category {ℓ₄} {ℓ′₄}}
    (H : Functor C₃ C₄) (G : Functor C₂ C₃) (F : Functor C₁ C₂) where

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

  ⊙-associator : NatTrans (H ⊙ (G ⊙ F)) ((H ⊙ G) ⊙ F)

  ⊙-associator = makeNatTrans component naturality where
    component : (x : obj₁) → hom₄ (H₀ (G₀ (F₀ x))) (H₀ (G₀ (F₀ x)))
    component x = Category.id C₄ (H₀ (G₀ (F₀ x)))

    naturality : {x y : obj₁} (f : hom₁ x y) →
      component y •₄ Functor.hom (H ⊙ (G ⊙ F)) f ≡
      Functor.hom ((H ⊙ G) ⊙ F) f •₄ component x
    naturality {x} {y} f = trans (Category.id-l C₄ (H₁ (G₁ (F₁ f)))) (sym (Category.id-r C₄ (H₁ (G₁ (F₁ f)))))

  ⊙-associator⁻¹ : NatTrans ((H ⊙ G) ⊙ F) (H ⊙ (G ⊙ F))

  ⊙-associator⁻¹ = makeNatTrans component naturality where
    component : (x : obj₁) → hom₄ (H₀ (G₀ (F₀ x))) (H₀ (G₀ (F₀ x)))
    component x = Category.id C₄ (H₀ (G₀ (F₀ x)))

    naturality : {x y : obj₁} (f : hom₁ x y) →
      component y •₄ Functor.hom ((H ⊙ G) ⊙ F) f ≡
      Functor.hom (H ⊙ (G ⊙ F)) f •₄ component x
    naturality {x} {y} f = trans (Category.id-l C₄ (H₁ (G₁ (F₁ f)))) (sym (Category.id-r C₄ (H₁ (G₁ (F₁ f)))))

open associators public
