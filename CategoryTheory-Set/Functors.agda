module Functors where


open import Function renaming (id to id-fun)
open import Level
open import Relation.Binary.PropositionalEquality as PropEq using (_≡_ ; refl)
open PropEq.≡-Reasoning

open import Categories


record Functor {ℓ₁ ℓ′₁ ℓ₂ ℓ′₂ : Level} (C : Category {ℓ₁} {ℓ′₁}) (D : Category {ℓ₂} {ℓ′₂}) : Set (ℓ₁ ⊔ ℓ₂ ⊔ ℓ′₁ ⊔ ℓ′₂) where
  constructor makeFunctor
  field
    obj : Category.obj C → Category.obj D
    hom : forall {x y : Category.obj C} → Category.hom C x y → Category.hom D (obj x) (obj y)
    id : (x : Category.obj C) → hom (Category.id C x) ≡ Category.id D (obj x)
    compose : {x y z : Category.obj C} (g : Category.hom C y z) (f : Category.hom C x y) → hom (Category.compose C g f) ≡ Category.compose D (hom g) (hom f)


idFunctor : {ℓ₁ ℓ′₁ : Level} (C : Category {ℓ₁} {ℓ′₁}) → Functor C C
idFunctor C = makeFunctor (id-fun) (id-fun) (λ x → refl) (λ g f → refl)


constFunctor : {ℓ₁ ℓ′₁ ℓ₂ ℓ′₂ : Level} (C : Category {ℓ₁} {ℓ′₁}) (D : Category {ℓ₂} {ℓ′₂}) → Category.obj D → Functor C D
constFunctor C D x = makeFunctor (λ _ → x) (λ _ → Category.id D x) (λ _ → refl) (λ g f → PropEq.sym (Category.id-l D (Category.id D x)))


module functor-composition {ℓ₁ ℓ′₁ ℓ₂ ℓ′₂ ℓ₃ ℓ′₃ : Level} {C : Category {ℓ₁} {ℓ′₁}} {D : Category {ℓ₂} {ℓ′₂}} {E : Category {ℓ₃} {ℓ′₃}} where
  open Category C renaming (obj to obC ; hom to homC)
  open Category D renaming (id to id′ ; _•_ to _•′_)
  open Category E renaming (id to id″ ; _•_ to _•″_)

  infixl 7 _⊙_
  _⊙_ : Functor D E → Functor C D → Functor C E
  makeFunctor G₀ G₁ G-id G-compose ⊙ makeFunctor F₀ F₁ F-id F-compose = makeFunctor (G₀ ∘ F₀) (G₁ ∘ F₁) ⊙-id ⊙-compose where

    ⊙-id : (x : obC) → G₁ (F₁ (id x)) ≡ id″ (G₀ (F₀ x))
    ⊙-id x = begin
      G₁ (F₁ (id x))
        ≡⟨ PropEq.cong G₁ (F-id x) ⟩
      G₁ (id′ (F₀ x))
        ≡⟨ G-id (F₀ x) ⟩
      id″ (G₀ (F₀ x)) ∎

    ⊙-compose : {x y z : obC} (g : homC y z) (f : homC x y) → (G₁ ∘ F₁) (g • f) ≡ (G₁ ∘ F₁) g •″ (G₁ ∘ F₁) f
    ⊙-compose {x} {y} {z} g f = begin
      G₁ (F₁ (g • f))
        ≡⟨ PropEq.cong G₁ (F-compose g f) ⟩
      G₁ (F₁ g •′ F₁ f)
        ≡⟨ G-compose (F₁ g) (F₁ f) ⟩
      G₁ (F₁ g) •″ G₁ (F₁ f) ∎

open functor-composition public



functor-op : {ℓ₁ ℓ₂ ℓ′₁ ℓ′₂ : Level} {C : Category {ℓ₁} {ℓ′₁}} {D : Category {ℓ₂} {ℓ′₂}} → Functor C D → Functor (opposite C) (opposite D)
functor-op (makeFunctor obj hom id compose) = makeFunctor obj hom id (flip compose)