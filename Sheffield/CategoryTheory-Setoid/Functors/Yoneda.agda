module Sheffield.CategoryTheory-Setoid.Functors.Yoneda where

-- the Yoneda embedding

open import Function.Equality
open import Level

open import Sheffield.CategoryTheory-Setoid.Categories
open import Sheffield.CategoryTheory-Setoid.Examples.Sets
open import Sheffield.CategoryTheory-Setoid.Functors
open import Sheffield.CategoryTheory-Setoid.Functors.Category
open import Sheffield.CategoryTheory-Setoid.NaturalTransformations
open import Sheffield.CategoryTheory-Setoid.NaturalTransformations.Equality


module yoneda-embedding-context {ℓ ℓ′ ℓ″ : Level} (C : Category {ℓ} {ℓ′} {ℓ″}) where

  open Category C

  yoneda : Functor {ℓ} {ℓ′} {ℓ″} {ℓ ⊔ suc ℓ′ ⊔ suc ℓ″} {ℓ ⊔ suc ℓ′ ⊔ suc ℓ″} {ℓ ⊔ ℓ′ ⊔ ℓ″} C (Functors {ℓ} {ℓ′} {ℓ″} {suc ℓ′ ⊔ suc ℓ″} {ℓ′ ⊔ ℓ″} {ℓ′ ⊔ ℓ″} (opposite C) (Setoids {ℓ′} {ℓ″}))
  yoneda = makeFunctor Y₀ Y₁ Y-id Y-compose where
    Y₀ : obj → Functor (opposite C) Setoids
    Y₀ x = makeFunctor (λ a → hom a x) hom² (λ _ e → ≈-trans (id-r _) e) (λ _ _ e → ≈-trans (•-cong e ≈-refl) (≈-sym (assoc _ _ _))) where
      hom² : {a₁ a₂ : obj} → hom a₂ a₁ ⟶ Category.hom Setoids (hom a₁ x) (hom a₂ x)
      hom² {a₁} {a₂} = record {
        _⟨$⟩_ = λ f → record {
          _⟨$⟩_ = λ g → g • f;
          cong = λ ε → •-cong ε ≈-refl };
        cong = λ ε e → •-cong e ε }

    Y₁-homs : {x₁ x₂ : obj} → homset x₁ x₂ → NatTrans (Y₀ x₁) (Y₀ x₂)
    Y₁-homs {x₁} {x₂} f = makeNatTrans cpt nat where
      cpt : (y : obj) → _
      cpt y = record {
        _⟨$⟩_ = λ g → f • g;
        cong = •-cong ≈-refl }
      nat : {y₁ y₂ : obj} (g : homset y₂ y₁) → _
      nat {y₁} {y₂} g = λ {f₁} {f₂} e → ≈-trans (•-cong ≈-refl (•-cong e ≈-refl)) (≈-sym (assoc _ _ _))

    Y₁ : {x₁ x₂ : obj} → hom x₁ x₂ ⟶ Category.hom (Functors (opposite C) Setoids) (Y₀ x₁) (Y₀ x₂)
    Y₁ {x₁} {x₂} = record {
      _⟨$⟩_ = Y₁-homs ;
      cong = λ {f₁} {f₂} ε → make-≈₂ (λ x e → •-cong ε e) }

    Y-id : (x : obj) → _
    Y-id x = make-≈₂ (λ x {f₁} {f₂} ε → ≈-trans (id-l _) ε)

    Y-compose : {x y z : obj} (g : homset y z) (f : homset x y) → _
    Y-compose g f = make-≈₂ (λ x {f₁} {f₂} ε → ≈-trans (•-cong ≈-refl ε) (assoc _ _ _))

open yoneda-embedding-context public