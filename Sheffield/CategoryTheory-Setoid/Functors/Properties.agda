module Sheffield.CategoryTheory-Setoid.Functors.Properties where

open import Function.Equality hiding (id)
open import Function.Surjection hiding (id)
open import Level
open import Relation.Binary

open import Sheffield.CategoryTheory-Setoid.Categories
open import Sheffield.CategoryTheory-Setoid.Functors
open import Sheffield.CategoryTheory-Setoid.Functors.Isomorphism
open import Sheffield.CategoryTheory-Setoid.Functors.Isomorphism.Properties
open import Sheffield.CategoryTheory-Setoid.NaturalTransformations
open import Sheffield.CategoryTheory-Setoid.NaturalTransformations.Equality


module identity-statements {ℓ₁ ℓ′₁ ℓ″₁ : Level} {C : Category {ℓ₁} {ℓ′₁} {ℓ″₁}} where

  open Category C

  identity-faithful : faithful (idFunctor C)
  identity-faithful x y e = e

  identity-full : full (idFunctor C)
  identity-full x y = record {
    from = record {
      _⟨$⟩_ = λ f → f;
      cong = λ e → e };
    right-inverse-of = λ _ → ≈-refl }

open identity-statements public


module composition-statements {ℓ₁ ℓ′₁ ℓ″₁ ℓ₂ ℓ′₂ ℓ″₂ ℓ₃ ℓ′₃ ℓ″₃ : Level} {C : Category {ℓ₁} {ℓ′₁} {ℓ″₁}} {D : Category {ℓ₂} {ℓ′₂} {ℓ″₂}} {E : Category {ℓ₃} {ℓ′₃} {ℓ″₃}} (G : Functor D E) (F : Functor C D) where

  faithful-composition : faithful G → faithful F → faithful (G ⊙ F)
  faithful-composition fG fF x y {f} {g} e = fF _ _ (fG _ _ e)

  faithful-cancel-l : faithful (G ⊙ F) → faithful F
  faithful-cancel-l fGF x y {f} {g} e = fGF x y (cong (Functor.hom G) e)

  full-composition : full G → full F → full (G ⊙ F)
  full-composition fG fF x y = record {
    from = record {
      _⟨$⟩_ = λ f → Surjective.from (fF _ _) ⟨$⟩ (Surjective.from (fG _ _) ⟨$⟩ f);
      cong = λ {x} {y} e → cong (Surjective.from (fF _ _)) (cong (Surjective.from (fG _ _)) e) };
    right-inverse-of = λ f → Category.≈-trans E (Functor.hom-cong G (Surjective.right-inverse-of (fF _ _) (Surjective.from (fG _ _) ⟨$⟩ f))) (Surjective.right-inverse-of (fG _ _) f) }

open composition-statements public


module invariance-statements {ℓ₁ ℓ′₁ ℓ″₁ ℓ₂ ℓ′₂ ℓ″₂ : Level} {C : Category {ℓ₁} {ℓ′₁} {ℓ″₁}} {D : Category {ℓ₂} {ℓ′₂} {ℓ″₂}} (F₁ F₂ : Functor C D) (F₁≅₁F₂ : F₁ ≅₁ F₂) where

  open _≅₁_ F₁≅₁F₂
  open Category D

  private
    Φ₀ = NatTrans.component obverse
    Ψ₀ = NatTrans.component reverse

  faithful-invariance : faithful F₂ → faithful F₁
  faithful-invariance H x y {f} {g} e = H x y {f} {g} (≅₁-morphisms F₁≅₁F₂ e)

  full-invariance : full F₂ → full F₁
  full-invariance H x y = record {
    from = record {
      _⟨$⟩_ = λ f → Surjective.from (H _ _) ⟨$⟩ (≅₁-hom F₁≅₁F₂ ⟨$⟩ f);
      cong = λ {f} {g} e → cong (Surjective.from (H _ _)) (cong (≅₁-hom F₁≅₁F₂) e) };
    right-inverse-of = rio } where
      open ≈-Reasoning _ _
      rio : (f : _) → _
      rio f = begin
        Functor.homsets F₁ (Surjective.from (H x y) ⟨$⟩ (Φ₀ y • f • Ψ₀ x))
          ≈⟨ ≈-sym (≅₁-hom-≈ (≅₁-sym F₁≅₁F₂) (Surjective.from (H x y) ⟨$⟩ (Φ₀ y • f • Ψ₀ x))) ⟩
        Ψ₀ y • (Functor.homsets F₂ (Surjective.from (H x y) ⟨$⟩ (Φ₀ y • f • Ψ₀ x))) • Φ₀ x
          ≈⟨ cong (≅₁-hom (≅₁-sym F₁≅₁F₂)) ((Surjective.right-inverse-of (H x y) (≅₁-hom F₁≅₁F₂ ⟨$⟩ f))) ⟩
        Ψ₀ y • (Φ₀ y • f • Ψ₀ x) • Φ₀ x
          ≈⟨ ≈-sym (assoc _ _ _) ⟩
        (Ψ₀ y • (Φ₀ y • (f • Ψ₀ x))) • Φ₀ x
          ≈⟨ •-cong (≈-sym (assoc _ _ _)) ≈-refl ⟩
        ((Ψ₀ y • Φ₀ y) • (f • Ψ₀ x)) • Φ₀ x
          ≈⟨ assoc _ _ _ ⟩
        (Ψ₀ y • Φ₀ y) • ((f • Ψ₀ x) • Φ₀ x)
          ≈⟨ •-cong (_≈₂_.component-≈ unit y) (assoc _ _ _) ⟩
        id _ • (f • (Ψ₀ x • Φ₀ x))
          ≈⟨ id-l _ ⟩
        f • (Ψ₀ x • Φ₀ x)
          ≈⟨ •-cong ≈-refl (_≈₂_.component-≈ unit x) ⟩
        f • id _
          ≈⟨ id-r _ ⟩
        f ∎

      

open invariance-statements public







