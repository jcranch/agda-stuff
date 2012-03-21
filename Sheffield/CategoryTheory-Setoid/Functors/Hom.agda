module Sheffield.CategoryTheory-Setoid.Functors.Hom where

open import Data.Product renaming (_×_ to _*_)
open import Level
open import Relation.Binary

open import Sheffield.CategoryTheory-Setoid.Categories
open import Sheffield.CategoryTheory-Setoid.Categories.Product using (_×_)
open import Sheffield.CategoryTheory-Setoid.Examples.Sets
open import Sheffield.CategoryTheory-Setoid.Functors


module hom-functor {ℓ ℓ′ ℓ″ : Level} (C : Category {ℓ} {ℓ′} {ℓ″}) where

  open Category C

  Hom : Functor (opposite C × C) Setoids
  Hom = record {
    obj = uncurry hom ;
    hom = record {
      _⟨$⟩_ = λ f → record {
        _⟨$⟩_ = λ g → proj₂ f • g • proj₁ f;
        cong = λ ε → •-cong ≈-refl (•-cong ε ≈-refl) } ;
      cong = λ ε₁ ε₂ → •-cong (proj₂ ε₁) (•-cong ε₂ (proj₁ ε₁)) } ;
    id = λ x → ≈-trans (≈-trans (id-l _) (id-r _)) ;
    compose = κ } where
      κ : {x y z : _} (g : Category.homset (opposite C × C) y z) (f : Category.homset (opposite C × C) x y) {β : _} {α : _} (ε : _) → _
      κ (g₁ , g₂) (f₁ , f₂) {β} {α} ε = begin
        (g₂ • f₂) • (β • (f₁ • g₁))
          ≈⟨ assoc _ _ _ ⟩
        g₂ • (f₂ • (β • (f₁ • g₁)))
          ≈⟨ •-cong ≈-refl (•-cong ≈-refl (•-cong ε ≈-refl)) ⟩
        g₂ • (f₂ • (α • (f₁ • g₁)))
          ≈⟨ •-cong ≈-refl (•-cong ≈-refl (≈-sym (assoc _ _ _))) ⟩
        g₂ • (f₂ • ((α • f₁) • g₁))
          ≈⟨ •-cong ≈-refl (≈-sym (assoc _ _ _)) ⟩
        g₂ • ((f₂ • (α • f₁)) • g₁) ∎ where open ≈-Reasoning _ _

open hom-functor public



