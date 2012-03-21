module Sheffield.CategoryTheory-Setoid.Examples.PreorderCategory where

open import Data.Unit using (tt)
open import Function
open import Level
open import Relation.Binary

open import Sheffield.CategoryTheory-Setoid.Categories
open import Sheffield.CategoryTheory-Setoid.Functors
open import Sheffield.CategoryTheory-Setoid.SetoidFunction


PreorderCategory : {ℓ ℓ′ : Level} {A : Set ℓ} (_≤_ : Rel A ℓ′) → Reflexive _≤_ → Transitive _≤_ → Category {ℓ} {ℓ′} {zero}
PreorderCategory {A = A} _≤_ refl trans = record {
  obj = A ;
  hom = λ x y → indiscreteSetoid (x ≤ y) ;
  id = λ x → refl ;
  compose = record {
    _⟨$⟩_ = λ g → record {
      _⟨$⟩_ = λ f → trans f g;
      cong = λ _ → tt } ;
    cong = λ _ _ → tt } ;
  id-l = λ _ → tt ;
  id-r = λ _ → tt ;
  assoc = λ _ _ _ → tt }


PreorderFunctor : {ℓ₁ ℓ′₁ ℓ₂ ℓ′₂ : Level}
  {A₁ : Set ℓ₁} (_≤₁_ : Rel A₁ ℓ′₁) (r₁ : Reflexive _≤₁_) (t₁ : Transitive _≤₁_)
  {A₂ : Set ℓ₂} (_≤₂_ : Rel A₂ ℓ′₂) (r₂ : Reflexive _≤₂_) (t₂ : Transitive _≤₂_)
  (f : A₁ → A₂) → f Preserves _≤₁_ ⟶ _≤₂_ →
  Functor (PreorderCategory _≤₁_ r₁ t₁) (PreorderCategory _≤₂_ r₂ t₂)
PreorderFunctor _≤₁_ r₁ t₁ _≤₂_ r₂ t₂ f p = record {
  obj = f ;
  hom = record {
    _⟨$⟩_ = p;
    cong = λ _ → tt } ;
  id = λ _ → tt ;
  compose = λ _ _ → tt }
