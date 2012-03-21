module Sheffield.CategoryTheory-Setoid.Categories.Diagrams where

open import Data.Empty using (⊥)
open import Data.Unit using (⊤ ; tt) renaming (setoid to ⊤-setoid)
open import Level
open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (refl)

open import Sheffield.CategoryTheory-Setoid.Categories
open import Sheffield.CategoryTheory-Setoid.Functors
open import Sheffield.CategoryTheory-Setoid.NaturalTransformations



∅ : Category {zero} {zero} {zero}
∅ = record {
  obj = ⊥ ;
  hom = λ () ;
  id = λ () ;
  compose = λ {_} → λ {} ;
  id-l = λ {_} → λ {} ;
  id-r = λ {_} → λ {} ;
  assoc = λ {_} → λ {} }

∅-functor : {ℓ₁ ℓ′₁ ℓ″₁ : Level} {C : Category {ℓ₁} {ℓ′₁} {ℓ″₁}} → Functor ∅ C
∅-functor = record {
  obj = λ () ;
  hom = λ {x} → λ {} ;
  id = λ () ;
  compose = λ {x} {y} → λ {} }

∅-nat-trans : {ℓ₁ ℓ′₁ ℓ″₁ : Level} {C : Category {ℓ₁} {ℓ′₁} {ℓ″₁}} {F G : Functor ∅ C} → NatTrans F G
∅-nat-trans = record {
  component = λ () ;
  naturality = λ {x} → λ {} }



point : Category {zero} {zero} {zero}
point = record {
  obj = ⊤ ;
  hom = λ _ _ → ⊤-setoid ;
  id = λ _ → tt ;
  compose = record {
    _⟨$⟩_ = λ g → record {
      _⟨$⟩_ = λ f → tt ;
      cong = λ _ → refl } ;
    cong = λ _ _ → refl } ;
  id-l = λ _ → refl ;
  id-r = λ _ → refl ;
  assoc = λ _ _ _ → refl }
