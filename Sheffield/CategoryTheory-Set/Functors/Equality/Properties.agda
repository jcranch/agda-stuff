module Sheffield.CategoryTheory-Set.Functors.Equality.Properties where

-- Equality of functors is evil.

open import Level
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

open import Sheffield.CategoryTheory-Set.Categories
open import Sheffield.CategoryTheory-Set.Functors
open import Sheffield.CategoryTheory-Set.Functors.Equality
open import Sheffield.CategoryTheory-Set.ExtensionalEquality


{-
⊙-≡₁-compatible : {ℓ₁ : Level} {ℓ₂ : Level} {ℓ₃ : Level}
                  {ℓ′₁ : Level} {ℓ′₂ : Level} {ℓ′₃ : Level}
                  {C : Category {ℓ₁} {ℓ′₁}}
                  {D : Category {ℓ₂} {ℓ′₂}}
                  {E : Category {ℓ₃} {ℓ′₃}}
                  {F₁ : Functor C D} {F₂ : Functor C D}
                  {G₁ : Functor D E} {G₂ : Functor D E} →
                  G₁ ≡₁ G₂ → F₁ ≡₁ F₂ → G₁ ⊙ F₁ ≡₁ G₂ ⊙ F₂
⊙-≡₁-compatible {_} {_} {_} {_} {_} {_} {C} {D} {E} {F₁} {F₂} {G₁} {G₂} (refl₁ α β) (refl₁ γ δ) = refl₁ ε ζ where
  ε : (a : Category.obj C) → Functor.obj (G₁ ⊙ F₁) a ≡ Functor.obj (G₂ ⊙ F₂) a
  ε a = begin
    Functor.obj G₁ (Functor.obj F₁ a)
      ≡⟨ cong (Functor.obj G₁) (γ a) ⟩
    Functor.obj G₁ (Functor.obj F₂ a)
      ≡⟨ α (Functor.obj F₂ a) ⟩
    Functor.obj G₂ (Functor.obj F₂ a) ∎ where open ≡-Reasoning
  ζ : {x y : Category.obj C} (f : Category.hom C x y) → subst₂ (Category.hom E) (ε x) (ε y) (Functor.hom (G₁ ⊙ F₁) f) ≡ Functor.hom (G₂ ⊙ F₂) f
  ζ {x} {y} f = {!!}
-}

{-
⊙-unit-l : {ℓ₁ ℓ₂ ℓ′₁ ℓ′₂ : Level}
           {C : Category {ℓ₁} {ℓ′₁}} {D : Category {ℓ₂} {ℓ′₂}}
           (F : Functor C D) → (idFunctor D) ⊙ F ≡₁ F
⊙-unit-l {_} {_} {_} {_} {C} {D} F = refl₁ ((idFunctor D) ⊙ F) F (λ x → refl) (λ f → HetrEq.refl)
-}

{-
⊙-unit-r : {ℓ₁ ℓ₂ ℓ′₁ ℓ′₂ : Level}
           {C : Category {ℓ₁} {ℓ′₁}} {D : Category {ℓ₂} {ℓ′₂}}
           (F : Functor C D) → F ⊙ (idFunctor C) ≡₁ F
⊙-unit-r {_} {_} {_} {_} {C} {D} F = refl₁ (F ⊙ (idFunctor C)) F (λ x → refl) (λ f → HetrEq.refl)
-}

{-
⊙-assoc : {ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ′₁ ℓ′₂ ℓ′₃ ℓ′₄ : Level}
          {C₁ : Category {ℓ₁} {ℓ′₁}} {C₂ : Category {ℓ₂} {ℓ′₂}}
          {C₃ : Category {ℓ₃} {ℓ′₃}} {C₄ : Category {ℓ₄} {ℓ′₄}}
          (H : Functor C₃ C₄) (G : Functor C₂ C₃) (F : Functor C₁ C₂) →
          H ⊙ (G ⊙ F) ≡₁ H ⊙ G ⊙ F
⊙-assoc H G F = refl₁ (H ⊙ (G ⊙ F)) (H ⊙ G ⊙ F) (λ x → refl) (λ f → HetrEq.refl)
-}